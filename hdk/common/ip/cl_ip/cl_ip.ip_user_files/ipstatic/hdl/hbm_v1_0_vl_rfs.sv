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
/******************************************************************************
******************************************************************************/
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor             : AMD
// \   \   \/     Version            : 1.0
//  \   \         Application        : MIG
//  /   /         Filename           : hbm_top.sv
// /___/   /\     Date Last Modified : $Date$
// \   \  /  \    Date Created       : Tue Jan 3 2017
//  \___\/\___\
//
//Device: UltraScale+ HBM
//Design Name: HBM
//*****************************************************************************

`timescale 1ps / 1ps

`ifdef MODEL_TECH
  `define SIMULATION_MODE
`elsif INCA
  `define SIMULATION_MODE
`elsif VCS
  `define SIMULATION_MODE
`elsif XILINX_SIMULATOR
  `define SIMULATION_MODE
`elsif _VCP
  `define SIMULATION_MODE
`endif

`include "defines.vh"

////////////////////////////////////////////////////////////////////////////////
// Module Delcaration
////////////////////////////////////////////////////////////////////////////////
module hbm_top #(
  parameter          HBM_STACK        = 1, // valid values 1 , 2
  parameter          SWITCH_ENABLE_00 = "TRUE",
  parameter          SWITCH_ENABLE_01 = "TRUE", 

  parameter          INIT_BYPASS = "FALSE",
  parameter          INIT_SEQ_TIMEOUT = 10000000,

  parameter          AXI_RST_ASSERT_WIDTH = 16,
  parameter          AXI_RST_DEASSERT_WIDTH = 2,

  parameter          TEMP_WAIT_PERIOD_0 = 100000,
  parameter          TEMP_WAIT_PERIOD_1 = 100000,

  parameter [15:0]   SWITCH_EN_0 = 1,
  parameter [15:0]   SWITCH_EN_1 = 1,
  parameter [15:0]   AXI_CLK_FREQ = 450.00,
  parameter [15:0]   AXI_CLK1_FREQ = 450.00,
  parameter [15:0]   HBM_REF_CLK_FREQ_0 = 100,
  parameter [15:0]   HBM_REF_CLK_FREQ_1 = 100,
  parameter [15:0]   HBM_CLK_FREQ_0 = 900,
  parameter [15:0]   HBM_CLK_FREQ_1 = 900,
  parameter [15:0]   HBM_STACK_NUM = 0,

  parameter          CLK_SEL_00 = "FALSE",
  parameter          CLK_SEL_01 = "FALSE",
  parameter          CLK_SEL_02 = "FALSE",
  parameter          CLK_SEL_03 = "FALSE",
  parameter          CLK_SEL_04 = "FALSE",
  parameter          CLK_SEL_05 = "FALSE",
  parameter          CLK_SEL_06 = "FALSE",
  parameter          CLK_SEL_07 = "FALSE",
  parameter          CLK_SEL_08 = "TRUE",
  parameter          CLK_SEL_09 = "FALSE",
  parameter          CLK_SEL_10 = "FALSE",
  parameter          CLK_SEL_11 = "FALSE",
  parameter          CLK_SEL_12 = "FALSE",
  parameter          CLK_SEL_13 = "FALSE",
  parameter          CLK_SEL_14 = "FALSE",
  parameter          CLK_SEL_15 = "FALSE",
  parameter          CLK_SEL_16 = "FALSE",
  parameter          CLK_SEL_17 = "FALSE",
  parameter          CLK_SEL_18 = "FALSE",
  parameter          CLK_SEL_19 = "FALSE",
  parameter          CLK_SEL_20 = "FALSE",
  parameter          CLK_SEL_21 = "FALSE",
  parameter          CLK_SEL_22 = "FALSE",
  parameter          CLK_SEL_23 = "FALSE",
  parameter          CLK_SEL_24 = "TRUE",
  parameter          CLK_SEL_25 = "FALSE",
  parameter          CLK_SEL_26 = "FALSE",
  parameter          CLK_SEL_27 = "FALSE",
  parameter          CLK_SEL_28 = "FALSE",
  parameter          CLK_SEL_29 = "FALSE",
  parameter          CLK_SEL_30 = "FALSE",
  parameter          CLK_SEL_31 = "FALSE",
  
  parameter integer  DATARATE_STACK_0   = 1800,
  parameter integer  DATARATE_STACK_1   = 1800,

  parameter integer  READ_PERCENT_00    = 20,
  parameter integer  READ_PERCENT_01    = 20,
  parameter integer  READ_PERCENT_02    = 20,
  parameter integer  READ_PERCENT_03    = 20,
  parameter integer  READ_PERCENT_04    = 20,
  parameter integer  READ_PERCENT_05    = 20,
  parameter integer  READ_PERCENT_06    = 20,
  parameter integer  READ_PERCENT_07    = 20,
  parameter integer  READ_PERCENT_08    = 20,
  parameter integer  READ_PERCENT_09    = 20,
  parameter integer  READ_PERCENT_10    = 20,
  parameter integer  READ_PERCENT_11    = 20,
  parameter integer  READ_PERCENT_12    = 20,
  parameter integer  READ_PERCENT_13    = 20,
  parameter integer  READ_PERCENT_14    = 20,
  parameter integer  READ_PERCENT_15    = 20,
  parameter integer  READ_PERCENT_16    = 20,
  parameter integer  READ_PERCENT_17    = 20,
  parameter integer  READ_PERCENT_18    = 20,
  parameter integer  READ_PERCENT_19    = 20,
  parameter integer  READ_PERCENT_20    = 20,
  parameter integer  READ_PERCENT_21    = 20,
  parameter integer  READ_PERCENT_22    = 20,
  parameter integer  READ_PERCENT_23    = 20,
  parameter integer  READ_PERCENT_24    = 20,
  parameter integer  READ_PERCENT_25    = 20,
  parameter integer  READ_PERCENT_26    = 20,
  parameter integer  READ_PERCENT_27    = 20,
  parameter integer  READ_PERCENT_28    = 20,
  parameter integer  READ_PERCENT_29    = 20,
  parameter integer  READ_PERCENT_30    = 20,
  parameter integer  READ_PERCENT_31    = 20,
  parameter integer  WRITE_PERCENT_00   = 20,
  parameter integer  WRITE_PERCENT_01   = 20,
  parameter integer  WRITE_PERCENT_02   = 20,
  parameter integer  WRITE_PERCENT_03   = 20,
  parameter integer  WRITE_PERCENT_04   = 20,
  parameter integer  WRITE_PERCENT_05   = 20,
  parameter integer  WRITE_PERCENT_06   = 20,
  parameter integer  WRITE_PERCENT_07   = 20,
  parameter integer  WRITE_PERCENT_08   = 20,
  parameter integer  WRITE_PERCENT_09   = 20,
  parameter integer  WRITE_PERCENT_10   = 20,
  parameter integer  WRITE_PERCENT_11   = 20,
  parameter integer  WRITE_PERCENT_12   = 20,
  parameter integer  WRITE_PERCENT_13   = 20,
  parameter integer  WRITE_PERCENT_14   = 20,
  parameter integer  WRITE_PERCENT_15   = 20,
  parameter integer  WRITE_PERCENT_16   = 20,
  parameter integer  WRITE_PERCENT_17   = 20,
  parameter integer  WRITE_PERCENT_18   = 20,
  parameter integer  WRITE_PERCENT_19   = 20,
  parameter integer  WRITE_PERCENT_20   = 20,
  parameter integer  WRITE_PERCENT_21   = 20,
  parameter integer  WRITE_PERCENT_22   = 20,
  parameter integer  WRITE_PERCENT_23   = 20,
  parameter integer  WRITE_PERCENT_24   = 20,
  parameter integer  WRITE_PERCENT_25   = 20,
  parameter integer  WRITE_PERCENT_26   = 20,
  parameter integer  WRITE_PERCENT_27   = 20,
  parameter integer  WRITE_PERCENT_28   = 20,
  parameter integer  WRITE_PERCENT_29   = 20,
  parameter integer  WRITE_PERCENT_30   = 20,
  parameter integer  WRITE_PERCENT_31   = 20,
  parameter integer  PAGEHIT_PERCENT_00 = 50,
  parameter integer  PAGEHIT_PERCENT_01 = 50,

  parameter          MC_ENABLE_00 = "TRUE",
  parameter          MC_ENABLE_01 = "TRUE",
  parameter          MC_ENABLE_02 = "TRUE",
  parameter          MC_ENABLE_03 = "TRUE",
  parameter          MC_ENABLE_04 = "TRUE",
  parameter          MC_ENABLE_05 = "TRUE",
  parameter          MC_ENABLE_06 = "TRUE",
  parameter          MC_ENABLE_07 = "TRUE",
  parameter          MC_ENABLE_08 = "TRUE",
  parameter          MC_ENABLE_09 = "TRUE",
  parameter          MC_ENABLE_10 = "TRUE",
  parameter          MC_ENABLE_11 = "TRUE",
  parameter          MC_ENABLE_12 = "TRUE",
  parameter          MC_ENABLE_13 = "TRUE",
  parameter          MC_ENABLE_14 = "TRUE",
  parameter          MC_ENABLE_15 = "TRUE",
  parameter          MC_ENABLE_APB_00 = "TRUE",
  parameter          MC_ENABLE_APB_01 = "TRUE",
  
  parameter          PHY_ENABLE_00 = "TRUE",
  parameter          PHY_ENABLE_01 = "TRUE",
  parameter          PHY_ENABLE_02 = "TRUE",
  parameter          PHY_ENABLE_03 = "TRUE",
  parameter          PHY_ENABLE_04 = "TRUE",
  parameter          PHY_ENABLE_05 = "TRUE",
  parameter          PHY_ENABLE_06 = "TRUE",
  parameter          PHY_ENABLE_07 = "TRUE",
  parameter          PHY_ENABLE_08 = "TRUE",
  parameter          PHY_ENABLE_09 = "TRUE",
  parameter          PHY_ENABLE_10 = "TRUE",
  parameter          PHY_ENABLE_11 = "TRUE",
  parameter          PHY_ENABLE_12 = "TRUE",
  parameter          PHY_ENABLE_13 = "TRUE",
  parameter          PHY_ENABLE_14 = "TRUE",
  parameter          PHY_ENABLE_15 = "TRUE",
  parameter          PHY_ENABLE_16 = "TRUE",
  parameter          PHY_ENABLE_17 = "TRUE",
  parameter          PHY_ENABLE_18 = "TRUE",
  parameter          PHY_ENABLE_19 = "TRUE",
  parameter          PHY_ENABLE_20 = "TRUE",
  parameter          PHY_ENABLE_21 = "TRUE",
  parameter          PHY_ENABLE_22 = "TRUE",
  parameter          PHY_ENABLE_23 = "TRUE",
  parameter          PHY_ENABLE_24 = "TRUE",
  parameter          PHY_ENABLE_25 = "TRUE",
  parameter          PHY_ENABLE_26 = "TRUE",
  parameter          PHY_ENABLE_27 = "TRUE",
  parameter          PHY_ENABLE_28 = "TRUE",
  parameter          PHY_ENABLE_29 = "TRUE",
  parameter          PHY_ENABLE_30 = "TRUE",
  parameter          PHY_ENABLE_31 = "TRUE",
  parameter          PHY_ENABLE_APB_00 = "TRUE",
  parameter          PHY_ENABLE_APB_01 = "TRUE"
) (
  input          HBM_REF_CLK_0,
  input          HBM_REF_CLK_1,
  
  input          AXI_00_ACLK,
  input          AXI_00_ARESET_N,
  input [ 36:0]  AXI_00_ARADDR,
  input [  1:0]  AXI_00_ARBURST,
  input [  5:0]  AXI_00_ARID,
  input [  3:0]  AXI_00_ARLEN,
  input [  2:0]  AXI_00_ARSIZE,
  input          AXI_00_ARVALID,
  input [ 36:0]  AXI_00_AWADDR,
  input [  1:0]  AXI_00_AWBURST,
  input [  5:0]  AXI_00_AWID,
  input [  3:0]  AXI_00_AWLEN,
  input [  2:0]  AXI_00_AWSIZE,
  input          AXI_00_AWVALID,
  input          AXI_00_RREADY,
  input          AXI_00_BREADY,
  input [255:0]  AXI_00_WDATA,
  input          AXI_00_WLAST,
  input [ 31:0]  AXI_00_WSTRB,
  input [ 31:0]  AXI_00_WDATA_PARITY,
  input          AXI_00_WVALID,
//  input          AXI_00_DFI_DW_RX_INDX_LD,
  input          AXI_00_DFI_LP_PWR_X_REQ,
  
  input          AXI_01_ACLK,
  input          AXI_01_ARESET_N,
  input [ 36:0]  AXI_01_ARADDR,
  input [  1:0]  AXI_01_ARBURST,
  input [  5:0]  AXI_01_ARID,
  input [  3:0]  AXI_01_ARLEN,
  input [  2:0]  AXI_01_ARSIZE,
  input          AXI_01_ARVALID,
  input [ 36:0]  AXI_01_AWADDR,
  input [  1:0]  AXI_01_AWBURST,
  input [  5:0]  AXI_01_AWID,
  input [  3:0]  AXI_01_AWLEN,
  input [  2:0]  AXI_01_AWSIZE,
  input          AXI_01_AWVALID,
  input          AXI_01_RREADY,
  input          AXI_01_BREADY,
  input [255:0]  AXI_01_WDATA,
  input          AXI_01_WLAST,
  input [ 31:0]  AXI_01_WSTRB,
  input [ 31:0]  AXI_01_WDATA_PARITY,
  input          AXI_01_WVALID,
//  input          AXI_01_DFI_DW_RX_INDX_LD,
  input          AXI_01_DFI_LP_PWR_X_REQ,
  
  input          AXI_02_ACLK,
  input          AXI_02_ARESET_N,
  input [ 36:0]  AXI_02_ARADDR,
  input [  1:0]  AXI_02_ARBURST,
  input [  5:0]  AXI_02_ARID,
  input [  3:0]  AXI_02_ARLEN,
  input [  2:0]  AXI_02_ARSIZE,
  input          AXI_02_ARVALID,
  input [ 36:0]  AXI_02_AWADDR,
  input [  1:0]  AXI_02_AWBURST,
  input [  5:0]  AXI_02_AWID,
  input [  3:0]  AXI_02_AWLEN,
  input [  2:0]  AXI_02_AWSIZE,
  input          AXI_02_AWVALID,
  input          AXI_02_RREADY,
  input          AXI_02_BREADY,
  input [255:0]  AXI_02_WDATA,
  input          AXI_02_WLAST,
  input [ 31:0]  AXI_02_WSTRB,
  input [ 31:0]  AXI_02_WDATA_PARITY,
  input          AXI_02_WVALID,
//  input          AXI_02_DFI_DW_RX_INDX_LD,
  input          AXI_02_DFI_LP_PWR_X_REQ,
  
  input          AXI_03_ACLK,
  input          AXI_03_ARESET_N,
  input [ 36:0]  AXI_03_ARADDR,
  input [  1:0]  AXI_03_ARBURST,
  input [  5:0]  AXI_03_ARID,
  input [  3:0]  AXI_03_ARLEN,
  input [  2:0]  AXI_03_ARSIZE,
  input          AXI_03_ARVALID,
  input [ 36:0]  AXI_03_AWADDR,
  input [  1:0]  AXI_03_AWBURST,
  input [  5:0]  AXI_03_AWID,
  input [  3:0]  AXI_03_AWLEN,
  input [  2:0]  AXI_03_AWSIZE,
  input          AXI_03_AWVALID,
  input          AXI_03_RREADY,
  input          AXI_03_BREADY,
  input [255:0]  AXI_03_WDATA,
  input          AXI_03_WLAST,
  input [ 31:0]  AXI_03_WSTRB,
  input [ 31:0]  AXI_03_WDATA_PARITY,
  input          AXI_03_WVALID,
//  input          AXI_03_DFI_DW_RX_INDX_LD,
  input          AXI_03_DFI_LP_PWR_X_REQ,
  
  input          AXI_04_ACLK,
  input          AXI_04_ARESET_N,
  input [ 36:0]  AXI_04_ARADDR,
  input [  1:0]  AXI_04_ARBURST,
  input [  5:0]  AXI_04_ARID,
  input [  3:0]  AXI_04_ARLEN,
  input [  2:0]  AXI_04_ARSIZE,
  input          AXI_04_ARVALID,
  input [ 36:0]  AXI_04_AWADDR,
  input [  1:0]  AXI_04_AWBURST,
  input [  5:0]  AXI_04_AWID,
  input [  3:0]  AXI_04_AWLEN,
  input [  2:0]  AXI_04_AWSIZE,
  input          AXI_04_AWVALID,
  input          AXI_04_RREADY,
  input          AXI_04_BREADY,
  input [255:0]  AXI_04_WDATA,
  input          AXI_04_WLAST,
  input [ 31:0]  AXI_04_WSTRB,
  input [ 31:0]  AXI_04_WDATA_PARITY,
  input          AXI_04_WVALID,
//  input          AXI_04_DFI_DW_RX_INDX_LD,
  input          AXI_04_DFI_LP_PWR_X_REQ,
  
  input          AXI_05_ACLK,
  input          AXI_05_ARESET_N,
  input [ 36:0]  AXI_05_ARADDR,
  input [  1:0]  AXI_05_ARBURST,
  input [  5:0]  AXI_05_ARID,
  input [  3:0]  AXI_05_ARLEN,
  input [  2:0]  AXI_05_ARSIZE,
  input          AXI_05_ARVALID,
  input [ 36:0]  AXI_05_AWADDR,
  input [  1:0]  AXI_05_AWBURST,
  input [  5:0]  AXI_05_AWID,
  input [  3:0]  AXI_05_AWLEN,
  input [  2:0]  AXI_05_AWSIZE,
  input          AXI_05_AWVALID,
  input          AXI_05_RREADY,
  input          AXI_05_BREADY,
  input [255:0]  AXI_05_WDATA,
  input          AXI_05_WLAST,
  input [ 31:0]  AXI_05_WSTRB,
  input [ 31:0]  AXI_05_WDATA_PARITY,
  input          AXI_05_WVALID,
//  input          AXI_05_DFI_DW_RX_INDX_LD,
  input          AXI_05_DFI_LP_PWR_X_REQ,
  
  input          AXI_06_ACLK,
  input          AXI_06_ARESET_N,
  input [ 36:0]  AXI_06_ARADDR,
  input [  1:0]  AXI_06_ARBURST,
  input [  5:0]  AXI_06_ARID,
  input [  3:0]  AXI_06_ARLEN,
  input [  2:0]  AXI_06_ARSIZE,
  input          AXI_06_ARVALID,
  input [ 36:0]  AXI_06_AWADDR,
  input [  1:0]  AXI_06_AWBURST,
  input [  5:0]  AXI_06_AWID,
  input [  3:0]  AXI_06_AWLEN,
  input [  2:0]  AXI_06_AWSIZE,
  input          AXI_06_AWVALID,
  input          AXI_06_RREADY,
  input          AXI_06_BREADY,
  input [255:0]  AXI_06_WDATA,
  input          AXI_06_WLAST,
  input [ 31:0]  AXI_06_WSTRB,
  input [ 31:0]  AXI_06_WDATA_PARITY,
  input          AXI_06_WVALID,
//  input          AXI_06_DFI_DW_RX_INDX_LD,
  input          AXI_06_DFI_LP_PWR_X_REQ,
  
  input          AXI_07_ACLK,
  input          AXI_07_ARESET_N,
  input [ 36:0]  AXI_07_ARADDR,
  input [  1:0]  AXI_07_ARBURST,
  input [  5:0]  AXI_07_ARID,
  input [  3:0]  AXI_07_ARLEN,
  input [  2:0]  AXI_07_ARSIZE,
  input          AXI_07_ARVALID,
  input [ 36:0]  AXI_07_AWADDR,
  input [  1:0]  AXI_07_AWBURST,
  input [  5:0]  AXI_07_AWID,
  input [  3:0]  AXI_07_AWLEN,
  input [  2:0]  AXI_07_AWSIZE,
  input          AXI_07_AWVALID,
  input          AXI_07_RREADY,
  input          AXI_07_BREADY,
  input [255:0]  AXI_07_WDATA,
  input          AXI_07_WLAST,
  input [ 31:0]  AXI_07_WSTRB,
  input [ 31:0]  AXI_07_WDATA_PARITY,
  input          AXI_07_WVALID,
//  input          AXI_07_DFI_DW_RX_INDX_LD,
  input          AXI_07_DFI_LP_PWR_X_REQ,
  
  input          AXI_08_ACLK,
  input          AXI_08_ARESET_N,
  input [ 36:0]  AXI_08_ARADDR,
  input [  1:0]  AXI_08_ARBURST,
  input [  5:0]  AXI_08_ARID,
  input [  3:0]  AXI_08_ARLEN,
  input [  2:0]  AXI_08_ARSIZE,
  input          AXI_08_ARVALID,
  input [ 36:0]  AXI_08_AWADDR,
  input [  1:0]  AXI_08_AWBURST,
  input [  5:0]  AXI_08_AWID,
  input [  3:0]  AXI_08_AWLEN,
  input [  2:0]  AXI_08_AWSIZE,
  input          AXI_08_AWVALID,
  input          AXI_08_RREADY,
  input          AXI_08_BREADY,
  input [255:0]  AXI_08_WDATA,
  input          AXI_08_WLAST,
  input [ 31:0]  AXI_08_WSTRB,
  input [ 31:0]  AXI_08_WDATA_PARITY,
  input          AXI_08_WVALID,
//  input          AXI_08_DFI_DW_RX_INDX_LD,
  input          AXI_08_DFI_LP_PWR_X_REQ,
  
  input          AXI_09_ACLK,
  input          AXI_09_ARESET_N,
  input [ 36:0]  AXI_09_ARADDR,
  input [  1:0]  AXI_09_ARBURST,
  input [  5:0]  AXI_09_ARID,
  input [  3:0]  AXI_09_ARLEN,
  input [  2:0]  AXI_09_ARSIZE,
  input          AXI_09_ARVALID,
  input [ 36:0]  AXI_09_AWADDR,
  input [  1:0]  AXI_09_AWBURST,
  input [  5:0]  AXI_09_AWID,
  input [  3:0]  AXI_09_AWLEN,
  input [  2:0]  AXI_09_AWSIZE,
  input          AXI_09_AWVALID,
  input          AXI_09_RREADY,
  input          AXI_09_BREADY,
  input [255:0]  AXI_09_WDATA,
  input          AXI_09_WLAST,
  input [ 31:0]  AXI_09_WSTRB,
  input [ 31:0]  AXI_09_WDATA_PARITY,
  input          AXI_09_WVALID,
//  input          AXI_09_DFI_DW_RX_INDX_LD,
  input          AXI_09_DFI_LP_PWR_X_REQ,
  
  input          AXI_10_ACLK,
  input          AXI_10_ARESET_N,
  input [ 36:0]  AXI_10_ARADDR,
  input [  1:0]  AXI_10_ARBURST,
  input [  5:0]  AXI_10_ARID,
  input [  3:0]  AXI_10_ARLEN,
  input [  2:0]  AXI_10_ARSIZE,
  input          AXI_10_ARVALID,
  input [ 36:0]  AXI_10_AWADDR,
  input [  1:0]  AXI_10_AWBURST,
  input [  5:0]  AXI_10_AWID,
  input [  3:0]  AXI_10_AWLEN,
  input [  2:0]  AXI_10_AWSIZE,
  input          AXI_10_AWVALID,
  input          AXI_10_RREADY,
  input          AXI_10_BREADY,
  input [255:0]  AXI_10_WDATA,
  input          AXI_10_WLAST,
  input [ 31:0]  AXI_10_WSTRB,
  input [ 31:0]  AXI_10_WDATA_PARITY,
  input          AXI_10_WVALID,
//  input          AXI_10_DFI_DW_RX_INDX_LD,
  input          AXI_10_DFI_LP_PWR_X_REQ,
  
  input          AXI_11_ACLK,
  input          AXI_11_ARESET_N,
  input [ 36:0]  AXI_11_ARADDR,
  input [  1:0]  AXI_11_ARBURST,
  input [  5:0]  AXI_11_ARID,
  input [  3:0]  AXI_11_ARLEN,
  input [  2:0]  AXI_11_ARSIZE,
  input          AXI_11_ARVALID,
  input [ 36:0]  AXI_11_AWADDR,
  input [  1:0]  AXI_11_AWBURST,
  input [  5:0]  AXI_11_AWID,
  input [  3:0]  AXI_11_AWLEN,
  input [  2:0]  AXI_11_AWSIZE,
  input          AXI_11_AWVALID,
  input          AXI_11_RREADY,
  input          AXI_11_BREADY,
  input [255:0]  AXI_11_WDATA,
  input          AXI_11_WLAST,
  input [ 31:0]  AXI_11_WSTRB,
  input [ 31:0]  AXI_11_WDATA_PARITY,
  input          AXI_11_WVALID,
//  input          AXI_11_DFI_DW_RX_INDX_LD,
  input          AXI_11_DFI_LP_PWR_X_REQ,
  
  input          AXI_12_ACLK,
  input          AXI_12_ARESET_N,
  input [ 36:0]  AXI_12_ARADDR,
  input [  1:0]  AXI_12_ARBURST,
  input [  5:0]  AXI_12_ARID,
  input [  3:0]  AXI_12_ARLEN,
  input [  2:0]  AXI_12_ARSIZE,
  input          AXI_12_ARVALID,
  input [ 36:0]  AXI_12_AWADDR,
  input [  1:0]  AXI_12_AWBURST,
  input [  5:0]  AXI_12_AWID,
  input [  3:0]  AXI_12_AWLEN,
  input [  2:0]  AXI_12_AWSIZE,
  input          AXI_12_AWVALID,
  input          AXI_12_RREADY,
  input          AXI_12_BREADY,
  input [255:0]  AXI_12_WDATA,
  input          AXI_12_WLAST,
  input [ 31:0]  AXI_12_WSTRB,
  input [ 31:0]  AXI_12_WDATA_PARITY,
  input          AXI_12_WVALID,
//  input          AXI_12_DFI_DW_RX_INDX_LD,
  input          AXI_12_DFI_LP_PWR_X_REQ,
  
  input          AXI_13_ACLK,
  input          AXI_13_ARESET_N,
  input [ 36:0]  AXI_13_ARADDR,
  input [  1:0]  AXI_13_ARBURST,
  input [  5:0]  AXI_13_ARID,
  input [  3:0]  AXI_13_ARLEN,
  input [  2:0]  AXI_13_ARSIZE,
  input          AXI_13_ARVALID,
  input [ 36:0]  AXI_13_AWADDR,
  input [  1:0]  AXI_13_AWBURST,
  input [  5:0]  AXI_13_AWID,
  input [  3:0]  AXI_13_AWLEN,
  input [  2:0]  AXI_13_AWSIZE,
  input          AXI_13_AWVALID,
  input          AXI_13_RREADY,
  input          AXI_13_BREADY,
  input [255:0]  AXI_13_WDATA,
  input          AXI_13_WLAST,
  input [ 31:0]  AXI_13_WSTRB,
  input [ 31:0]  AXI_13_WDATA_PARITY,
  input          AXI_13_WVALID,
//  input          AXI_13_DFI_DW_RX_INDX_LD,
  input          AXI_13_DFI_LP_PWR_X_REQ,
  
  input          AXI_14_ACLK,
  input          AXI_14_ARESET_N,
  input [ 36:0]  AXI_14_ARADDR,
  input [  1:0]  AXI_14_ARBURST,
  input [  5:0]  AXI_14_ARID,
  input [  3:0]  AXI_14_ARLEN,
  input [  2:0]  AXI_14_ARSIZE,
  input          AXI_14_ARVALID,
  input [ 36:0]  AXI_14_AWADDR,
  input [  1:0]  AXI_14_AWBURST,
  input [  5:0]  AXI_14_AWID,
  input [  3:0]  AXI_14_AWLEN,
  input [  2:0]  AXI_14_AWSIZE,
  input          AXI_14_AWVALID,
  input          AXI_14_RREADY,
  input          AXI_14_BREADY,
  input [255:0]  AXI_14_WDATA,
  input          AXI_14_WLAST,
  input [ 31:0]  AXI_14_WSTRB,
  input [ 31:0]  AXI_14_WDATA_PARITY,
  input          AXI_14_WVALID,
//  input          AXI_14_DFI_DW_RX_INDX_LD,
  input          AXI_14_DFI_LP_PWR_X_REQ,
  
  input          AXI_15_ACLK,
  input          AXI_15_ARESET_N,
  input [ 36:0]  AXI_15_ARADDR,
  input [  1:0]  AXI_15_ARBURST,
  input [  5:0]  AXI_15_ARID,
  input [  3:0]  AXI_15_ARLEN,
  input [  2:0]  AXI_15_ARSIZE,
  input          AXI_15_ARVALID,
  input [ 36:0]  AXI_15_AWADDR,
  input [  1:0]  AXI_15_AWBURST,
  input [  5:0]  AXI_15_AWID,
  input [  3:0]  AXI_15_AWLEN,
  input [  2:0]  AXI_15_AWSIZE,
  input          AXI_15_AWVALID,
  input          AXI_15_RREADY,
  input          AXI_15_BREADY,
  input [255:0]  AXI_15_WDATA,
  input          AXI_15_WLAST,
  input [ 31:0]  AXI_15_WSTRB,
  input [ 31:0]  AXI_15_WDATA_PARITY,
  input          AXI_15_WVALID,
//  input          AXI_15_DFI_DW_RX_INDX_LD,
  input          AXI_15_DFI_LP_PWR_X_REQ,
  
  input          AXI_16_ACLK,
  input          AXI_16_ARESET_N,
  input [ 36:0]  AXI_16_ARADDR,
  input [  1:0]  AXI_16_ARBURST,
  input [  5:0]  AXI_16_ARID,
  input [  3:0]  AXI_16_ARLEN,
  input [  2:0]  AXI_16_ARSIZE,
  input          AXI_16_ARVALID,
  input [ 36:0]  AXI_16_AWADDR,
  input [  1:0]  AXI_16_AWBURST,
  input [  5:0]  AXI_16_AWID,
  input [  3:0]  AXI_16_AWLEN,
  input [  2:0]  AXI_16_AWSIZE,
  input          AXI_16_AWVALID,
  input          AXI_16_RREADY,
  input          AXI_16_BREADY,
  input [255:0]  AXI_16_WDATA,
  input          AXI_16_WLAST,
  input [ 31:0]  AXI_16_WSTRB,
  input [ 31:0]  AXI_16_WDATA_PARITY,
  input          AXI_16_WVALID,
//  input          AXI_16_DFI_DW_RX_INDX_LD,
  input          AXI_16_DFI_LP_PWR_X_REQ,
  
  input          AXI_17_ACLK,
  input          AXI_17_ARESET_N,
  input [ 36:0]  AXI_17_ARADDR,
  input [  1:0]  AXI_17_ARBURST,
  input [  5:0]  AXI_17_ARID,
  input [  3:0]  AXI_17_ARLEN,
  input [  2:0]  AXI_17_ARSIZE,
  input          AXI_17_ARVALID,
  input [ 36:0]  AXI_17_AWADDR,
  input [  1:0]  AXI_17_AWBURST,
  input [  5:0]  AXI_17_AWID,
  input [  3:0]  AXI_17_AWLEN,
  input [  2:0]  AXI_17_AWSIZE,
  input          AXI_17_AWVALID,
  input          AXI_17_RREADY,
  input          AXI_17_BREADY,
  input [255:0]  AXI_17_WDATA,
  input          AXI_17_WLAST,
  input [ 31:0]  AXI_17_WSTRB,
  input [ 31:0]  AXI_17_WDATA_PARITY,
  input          AXI_17_WVALID,
//  input          AXI_17_DFI_DW_RX_INDX_LD,
  input          AXI_17_DFI_LP_PWR_X_REQ,
  
  input          AXI_18_ACLK,
  input          AXI_18_ARESET_N,
  input [ 36:0]  AXI_18_ARADDR,
  input [  1:0]  AXI_18_ARBURST,
  input [  5:0]  AXI_18_ARID,
  input [  3:0]  AXI_18_ARLEN,
  input [  2:0]  AXI_18_ARSIZE,
  input          AXI_18_ARVALID,
  input [ 36:0]  AXI_18_AWADDR,
  input [  1:0]  AXI_18_AWBURST,
  input [  5:0]  AXI_18_AWID,
  input [  3:0]  AXI_18_AWLEN,
  input [  2:0]  AXI_18_AWSIZE,
  input          AXI_18_AWVALID,
  input          AXI_18_RREADY,
  input          AXI_18_BREADY,
  input [255:0]  AXI_18_WDATA,
  input          AXI_18_WLAST,
  input [ 31:0]  AXI_18_WSTRB,
  input [ 31:0]  AXI_18_WDATA_PARITY,
  input          AXI_18_WVALID,
//  input          AXI_18_DFI_DW_RX_INDX_LD,
  input          AXI_18_DFI_LP_PWR_X_REQ,
  
  input          AXI_19_ACLK,
  input          AXI_19_ARESET_N,
  input [ 36:0]  AXI_19_ARADDR,
  input [  1:0]  AXI_19_ARBURST,
  input [  5:0]  AXI_19_ARID,
  input [  3:0]  AXI_19_ARLEN,
  input [  2:0]  AXI_19_ARSIZE,
  input          AXI_19_ARVALID,
  input [ 36:0]  AXI_19_AWADDR,
  input [  1:0]  AXI_19_AWBURST,
  input [  5:0]  AXI_19_AWID,
  input [  3:0]  AXI_19_AWLEN,
  input [  2:0]  AXI_19_AWSIZE,
  input          AXI_19_AWVALID,
  input          AXI_19_RREADY,
  input          AXI_19_BREADY,
  input [255:0]  AXI_19_WDATA,
  input          AXI_19_WLAST,
  input [ 31:0]  AXI_19_WSTRB,
  input [ 31:0]  AXI_19_WDATA_PARITY,
  input          AXI_19_WVALID,
//  input          AXI_19_DFI_DW_RX_INDX_LD,
  input          AXI_19_DFI_LP_PWR_X_REQ,
  
  input          AXI_20_ACLK,
  input          AXI_20_ARESET_N,
  input [ 36:0]  AXI_20_ARADDR,
  input [  1:0]  AXI_20_ARBURST,
  input [  5:0]  AXI_20_ARID,
  input [  3:0]  AXI_20_ARLEN,
  input [  2:0]  AXI_20_ARSIZE,
  input          AXI_20_ARVALID,
  input [ 36:0]  AXI_20_AWADDR,
  input [  1:0]  AXI_20_AWBURST,
  input [  5:0]  AXI_20_AWID,
  input [  3:0]  AXI_20_AWLEN,
  input [  2:0]  AXI_20_AWSIZE,
  input          AXI_20_AWVALID,
  input          AXI_20_RREADY,
  input          AXI_20_BREADY,
  input [255:0]  AXI_20_WDATA,
  input          AXI_20_WLAST,
  input [ 31:0]  AXI_20_WSTRB,
  input [ 31:0]  AXI_20_WDATA_PARITY,
  input          AXI_20_WVALID,
//  input          AXI_20_DFI_DW_RX_INDX_LD,
  input          AXI_20_DFI_LP_PWR_X_REQ,
  
  input          AXI_21_ACLK,
  input          AXI_21_ARESET_N,
  input [ 36:0]  AXI_21_ARADDR,
  input [  1:0]  AXI_21_ARBURST,
  input [  5:0]  AXI_21_ARID,
  input [  3:0]  AXI_21_ARLEN,
  input [  2:0]  AXI_21_ARSIZE,
  input          AXI_21_ARVALID,
  input [ 36:0]  AXI_21_AWADDR,
  input [  1:0]  AXI_21_AWBURST,
  input [  5:0]  AXI_21_AWID,
  input [  3:0]  AXI_21_AWLEN,
  input [  2:0]  AXI_21_AWSIZE,
  input          AXI_21_AWVALID,
  input          AXI_21_RREADY,
  input          AXI_21_BREADY,
  input [255:0]  AXI_21_WDATA,
  input          AXI_21_WLAST,
  input [ 31:0]  AXI_21_WSTRB,
  input [ 31:0]  AXI_21_WDATA_PARITY,
  input          AXI_21_WVALID,
//  input          AXI_21_DFI_DW_RX_INDX_LD,
  input          AXI_21_DFI_LP_PWR_X_REQ,
  
  input          AXI_22_ACLK,
  input          AXI_22_ARESET_N,
  input [ 36:0]  AXI_22_ARADDR,
  input [  1:0]  AXI_22_ARBURST,
  input [  5:0]  AXI_22_ARID,
  input [  3:0]  AXI_22_ARLEN,
  input [  2:0]  AXI_22_ARSIZE,
  input          AXI_22_ARVALID,
  input [ 36:0]  AXI_22_AWADDR,
  input [  1:0]  AXI_22_AWBURST,
  input [  5:0]  AXI_22_AWID,
  input [  3:0]  AXI_22_AWLEN,
  input [  2:0]  AXI_22_AWSIZE,
  input          AXI_22_AWVALID,
  input          AXI_22_RREADY,
  input          AXI_22_BREADY,
  input [255:0]  AXI_22_WDATA,
  input          AXI_22_WLAST,
  input [ 31:0]  AXI_22_WSTRB,
  input [ 31:0]  AXI_22_WDATA_PARITY,
  input          AXI_22_WVALID,
//  input          AXI_22_DFI_DW_RX_INDX_LD,
  input          AXI_22_DFI_LP_PWR_X_REQ,
  
  input          AXI_23_ACLK,
  input          AXI_23_ARESET_N,
  input [ 36:0]  AXI_23_ARADDR,
  input [  1:0]  AXI_23_ARBURST,
  input [  5:0]  AXI_23_ARID,
  input [  3:0]  AXI_23_ARLEN,
  input [  2:0]  AXI_23_ARSIZE,
  input          AXI_23_ARVALID,
  input [ 36:0]  AXI_23_AWADDR,
  input [  1:0]  AXI_23_AWBURST,
  input [  5:0]  AXI_23_AWID,
  input [  3:0]  AXI_23_AWLEN,
  input [  2:0]  AXI_23_AWSIZE,
  input          AXI_23_AWVALID,
  input          AXI_23_RREADY,
  input          AXI_23_BREADY,
  input [255:0]  AXI_23_WDATA,
  input          AXI_23_WLAST,
  input [ 31:0]  AXI_23_WSTRB,
  input [ 31:0]  AXI_23_WDATA_PARITY,
  input          AXI_23_WVALID,
//  input          AXI_23_DFI_DW_RX_INDX_LD,
  input          AXI_23_DFI_LP_PWR_X_REQ,
  
  input          AXI_24_ACLK,
  input          AXI_24_ARESET_N,
  input [ 36:0]  AXI_24_ARADDR,
  input [  1:0]  AXI_24_ARBURST,
  input [  5:0]  AXI_24_ARID,
  input [  3:0]  AXI_24_ARLEN,
  input [  2:0]  AXI_24_ARSIZE,
  input          AXI_24_ARVALID,
  input [ 36:0]  AXI_24_AWADDR,
  input [  1:0]  AXI_24_AWBURST,
  input [  5:0]  AXI_24_AWID,
  input [  3:0]  AXI_24_AWLEN,
  input [  2:0]  AXI_24_AWSIZE,
  input          AXI_24_AWVALID,
  input          AXI_24_RREADY,
  input          AXI_24_BREADY,
  input [255:0]  AXI_24_WDATA,
  input          AXI_24_WLAST,
  input [ 31:0]  AXI_24_WSTRB,
  input [ 31:0]  AXI_24_WDATA_PARITY,
  input          AXI_24_WVALID,
//  input          AXI_24_DFI_DW_RX_INDX_LD,
  input          AXI_24_DFI_LP_PWR_X_REQ,
  
  input          AXI_25_ACLK,
  input          AXI_25_ARESET_N,
  input [ 36:0]  AXI_25_ARADDR,
  input [  1:0]  AXI_25_ARBURST,
  input [  5:0]  AXI_25_ARID,
  input [  3:0]  AXI_25_ARLEN,
  input [  2:0]  AXI_25_ARSIZE,
  input          AXI_25_ARVALID,
  input [ 36:0]  AXI_25_AWADDR,
  input [  1:0]  AXI_25_AWBURST,
  input [  5:0]  AXI_25_AWID,
  input [  3:0]  AXI_25_AWLEN,
  input [  2:0]  AXI_25_AWSIZE,
  input          AXI_25_AWVALID,
  input          AXI_25_RREADY,
  input          AXI_25_BREADY,
  input [255:0]  AXI_25_WDATA,
  input          AXI_25_WLAST,
  input [ 31:0]  AXI_25_WSTRB,
  input [ 31:0]  AXI_25_WDATA_PARITY,
  input          AXI_25_WVALID,
//  input          AXI_25_DFI_DW_RX_INDX_LD,
  input          AXI_25_DFI_LP_PWR_X_REQ,
  
  input          AXI_26_ACLK,
  input          AXI_26_ARESET_N,
  input [ 36:0]  AXI_26_ARADDR,
  input [  1:0]  AXI_26_ARBURST,
  input [  5:0]  AXI_26_ARID,
  input [  3:0]  AXI_26_ARLEN,
  input [  2:0]  AXI_26_ARSIZE,
  input          AXI_26_ARVALID,
  input [ 36:0]  AXI_26_AWADDR,
  input [  1:0]  AXI_26_AWBURST,
  input [  5:0]  AXI_26_AWID,
  input [  3:0]  AXI_26_AWLEN,
  input [  2:0]  AXI_26_AWSIZE,
  input          AXI_26_AWVALID,
  input          AXI_26_RREADY,
  input          AXI_26_BREADY,
  input [255:0]  AXI_26_WDATA,
  input          AXI_26_WLAST,
  input [ 31:0]  AXI_26_WSTRB,
  input [ 31:0]  AXI_26_WDATA_PARITY,
  input          AXI_26_WVALID,
//  input          AXI_26_DFI_DW_RX_INDX_LD,
  input          AXI_26_DFI_LP_PWR_X_REQ,
  
  input          AXI_27_ACLK,
  input          AXI_27_ARESET_N,
  input [ 36:0]  AXI_27_ARADDR,
  input [  1:0]  AXI_27_ARBURST,
  input [  5:0]  AXI_27_ARID,
  input [  3:0]  AXI_27_ARLEN,
  input [  2:0]  AXI_27_ARSIZE,
  input          AXI_27_ARVALID,
  input [ 36:0]  AXI_27_AWADDR,
  input [  1:0]  AXI_27_AWBURST,
  input [  5:0]  AXI_27_AWID,
  input [  3:0]  AXI_27_AWLEN,
  input [  2:0]  AXI_27_AWSIZE,
  input          AXI_27_AWVALID,
  input          AXI_27_RREADY,
  input          AXI_27_BREADY,
  input [255:0]  AXI_27_WDATA,
  input          AXI_27_WLAST,
  input [ 31:0]  AXI_27_WSTRB,
  input [ 31:0]  AXI_27_WDATA_PARITY,
  input          AXI_27_WVALID,
//  input          AXI_27_DFI_DW_RX_INDX_LD,
  input          AXI_27_DFI_LP_PWR_X_REQ,
  
  input          AXI_28_ACLK,
  input          AXI_28_ARESET_N,
  input [ 36:0]  AXI_28_ARADDR,
  input [  1:0]  AXI_28_ARBURST,
  input [  5:0]  AXI_28_ARID,
  input [  3:0]  AXI_28_ARLEN,
  input [  2:0]  AXI_28_ARSIZE,
  input          AXI_28_ARVALID,
  input [ 36:0]  AXI_28_AWADDR,
  input [  1:0]  AXI_28_AWBURST,
  input [  5:0]  AXI_28_AWID,
  input [  3:0]  AXI_28_AWLEN,
  input [  2:0]  AXI_28_AWSIZE,
  input          AXI_28_AWVALID,
  input          AXI_28_RREADY,
  input          AXI_28_BREADY,
  input [255:0]  AXI_28_WDATA,
  input          AXI_28_WLAST,
  input [ 31:0]  AXI_28_WSTRB,
  input [ 31:0]  AXI_28_WDATA_PARITY,
  input          AXI_28_WVALID,
//  input          AXI_28_DFI_DW_RX_INDX_LD,
  input          AXI_28_DFI_LP_PWR_X_REQ,
  
  input          AXI_29_ACLK,
  input          AXI_29_ARESET_N,
  input [ 36:0]  AXI_29_ARADDR,
  input [  1:0]  AXI_29_ARBURST,
  input [  5:0]  AXI_29_ARID,
  input [  3:0]  AXI_29_ARLEN,
  input [  2:0]  AXI_29_ARSIZE,
  input          AXI_29_ARVALID,
  input [ 36:0]  AXI_29_AWADDR,
  input [  1:0]  AXI_29_AWBURST,
  input [  5:0]  AXI_29_AWID,
  input [  3:0]  AXI_29_AWLEN,
  input [  2:0]  AXI_29_AWSIZE,
  input          AXI_29_AWVALID,
  input          AXI_29_RREADY,
  input          AXI_29_BREADY,
  input [255:0]  AXI_29_WDATA,
  input          AXI_29_WLAST,
  input [ 31:0]  AXI_29_WSTRB,
  input [ 31:0]  AXI_29_WDATA_PARITY,
  input          AXI_29_WVALID,
//  input          AXI_29_DFI_DW_RX_INDX_LD,
  input          AXI_29_DFI_LP_PWR_X_REQ,
  
  input          AXI_30_ACLK,
  input          AXI_30_ARESET_N,
  input [ 36:0]  AXI_30_ARADDR,
  input [  1:0]  AXI_30_ARBURST,
  input [  5:0]  AXI_30_ARID,
  input [  3:0]  AXI_30_ARLEN,
  input [  2:0]  AXI_30_ARSIZE,
  input          AXI_30_ARVALID,
  input [ 36:0]  AXI_30_AWADDR,
  input [  1:0]  AXI_30_AWBURST,
  input [  5:0]  AXI_30_AWID,
  input [  3:0]  AXI_30_AWLEN,
  input [  2:0]  AXI_30_AWSIZE,
  input          AXI_30_AWVALID,
  input          AXI_30_RREADY,
  input          AXI_30_BREADY,
  input [255:0]  AXI_30_WDATA,
  input          AXI_30_WLAST,
  input [ 31:0]  AXI_30_WSTRB,
  input [ 31:0]  AXI_30_WDATA_PARITY,
  input          AXI_30_WVALID,
//  input          AXI_30_DFI_DW_RX_INDX_LD,
  input          AXI_30_DFI_LP_PWR_X_REQ,
  
  input          AXI_31_ACLK,
  input          AXI_31_ARESET_N,
  input [ 36:0]  AXI_31_ARADDR,
  input [  1:0]  AXI_31_ARBURST,
  input [  5:0]  AXI_31_ARID,
  input [  3:0]  AXI_31_ARLEN,
  input [  2:0]  AXI_31_ARSIZE,
  input          AXI_31_ARVALID,
  input [ 36:0]  AXI_31_AWADDR,
  input [  1:0]  AXI_31_AWBURST,
  input [  5:0]  AXI_31_AWID,
  input [  3:0]  AXI_31_AWLEN,
  input [  2:0]  AXI_31_AWSIZE,
  input          AXI_31_AWVALID,
  input          AXI_31_RREADY,
  input          AXI_31_BREADY,
  input [255:0]  AXI_31_WDATA,
  input          AXI_31_WLAST,
  input [ 31:0]  AXI_31_WSTRB,
  input [ 31:0]  AXI_31_WDATA_PARITY,
  input          AXI_31_WVALID,
//  input          AXI_31_DFI_DW_RX_INDX_LD,
  input          AXI_31_DFI_LP_PWR_X_REQ,
  
  input [ 31:0]  APB_0_PWDATA,
  input [ 21:0]  APB_0_PADDR,
  input          APB_0_PCLK,
  input          APB_0_PENABLE,
  input          APB_0_PRESET_N,
  input          APB_0_PSEL,
  input          APB_0_PWRITE,
  
  input [ 31:0]  APB_1_PWDATA,
  input [ 21:0]  APB_1_PADDR,
  input          APB_1_PCLK,
  input          APB_1_PENABLE,
  input          APB_1_PRESET_N,
  input          APB_1_PSEL,
  input          APB_1_PWRITE,
  
  output          AXI_00_ARREADY,
  output          AXI_00_AWREADY,
  output [ 31:0]  AXI_00_RDATA_PARITY,
  output [255:0]  AXI_00_RDATA,
  output [  5:0]  AXI_00_RID,
  output          AXI_00_RLAST,
  output [  1:0]  AXI_00_RRESP,
  output          AXI_00_RVALID,
  output          AXI_00_WREADY,
  output [  5:0]  AXI_00_BID,
  output [  1:0]  AXI_00_BRESP,
  output          AXI_00_BVALID,
  output [  1:0]  AXI_00_DFI_AW_AERR_N,
  output          AXI_00_DFI_CLK_BUF,
  output [  7:0]  AXI_00_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_00_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_00_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_00_DFI_DW_RDDATA_VALID,
  output          AXI_00_DFI_INIT_COMPLETE,
  output          AXI_00_DFI_PHYUPD_REQ,
  output          AXI_00_DFI_PHY_LP_STATE,
  output          AXI_00_DFI_RST_N_BUF,
  output [5:0]    AXI_00_MC_STATUS,
  output [7:0]    AXI_00_PHY_STATUS,

  
  output          AXI_01_ARREADY,
  output          AXI_01_AWREADY,
  output [ 31:0]  AXI_01_RDATA_PARITY,
  output [255:0]  AXI_01_RDATA,
  output [  5:0]  AXI_01_RID,
  output          AXI_01_RLAST,
  output [  1:0]  AXI_01_RRESP,
  output          AXI_01_RVALID,
  output          AXI_01_WREADY,
  output [  5:0]  AXI_01_BID,
  output [  1:0]  AXI_01_BRESP,
  output          AXI_01_BVALID,
  output [  1:0]  AXI_01_DFI_AW_AERR_N,
  output          AXI_01_DFI_CLK_BUF,
  output [  7:0]  AXI_01_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_01_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_01_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_01_DFI_DW_RDDATA_VALID,
  output          AXI_01_DFI_INIT_COMPLETE,
  output          AXI_01_DFI_PHYUPD_REQ,
  output          AXI_01_DFI_PHY_LP_STATE,
  output          AXI_01_DFI_RST_N_BUF,
  
  output          AXI_02_ARREADY,
  output          AXI_02_AWREADY,
  output [ 31:0]  AXI_02_RDATA_PARITY,
  output [255:0]  AXI_02_RDATA,
  output [  5:0]  AXI_02_RID,
  output          AXI_02_RLAST,
  output [  1:0]  AXI_02_RRESP,
  output          AXI_02_RVALID,
  output          AXI_02_WREADY,
  output [  5:0]  AXI_02_BID,
  output [  1:0]  AXI_02_BRESP,
  output          AXI_02_BVALID,
  output [  1:0]  AXI_02_DFI_AW_AERR_N,
  output          AXI_02_DFI_CLK_BUF,
  output [  7:0]  AXI_02_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_02_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_02_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_02_DFI_DW_RDDATA_VALID,
  output          AXI_02_DFI_INIT_COMPLETE,
  output          AXI_02_DFI_PHYUPD_REQ,
  output          AXI_02_DFI_PHY_LP_STATE,
  output          AXI_02_DFI_RST_N_BUF,
  output [5:0]    AXI_02_MC_STATUS,
  output [7:0]    AXI_02_PHY_STATUS,
  
  output          AXI_03_ARREADY,
  output          AXI_03_AWREADY,
  output [ 31:0]  AXI_03_RDATA_PARITY,
  output [255:0]  AXI_03_RDATA,
  output [  5:0]  AXI_03_RID,
  output          AXI_03_RLAST,
  output [  1:0]  AXI_03_RRESP,
  output          AXI_03_RVALID,
  output          AXI_03_WREADY,
  output [  5:0]  AXI_03_BID,
  output [  1:0]  AXI_03_BRESP,
  output          AXI_03_BVALID,
  output [  1:0]  AXI_03_DFI_AW_AERR_N,
  output          AXI_03_DFI_CLK_BUF,
  output [  7:0]  AXI_03_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_03_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_03_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_03_DFI_DW_RDDATA_VALID,
  output          AXI_03_DFI_INIT_COMPLETE,
  output          AXI_03_DFI_PHYUPD_REQ,
  output          AXI_03_DFI_PHY_LP_STATE,
  output          AXI_03_DFI_RST_N_BUF,
  
  output          AXI_04_ARREADY,
  output          AXI_04_AWREADY,
  output [ 31:0]  AXI_04_RDATA_PARITY,
  output [255:0]  AXI_04_RDATA,
  output [  5:0]  AXI_04_RID,
  output          AXI_04_RLAST,
  output [  1:0]  AXI_04_RRESP,
  output          AXI_04_RVALID,
  output          AXI_04_WREADY,
  output [  5:0]  AXI_04_BID,
  output [  1:0]  AXI_04_BRESP,
  output          AXI_04_BVALID,
  output [  1:0]  AXI_04_DFI_AW_AERR_N,
  output          AXI_04_DFI_CLK_BUF,
  output [  7:0]  AXI_04_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_04_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_04_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_04_DFI_DW_RDDATA_VALID,
  output          AXI_04_DFI_INIT_COMPLETE,
  output          AXI_04_DFI_PHYUPD_REQ,
  output          AXI_04_DFI_PHY_LP_STATE,
  output          AXI_04_DFI_RST_N_BUF,
  output [5:0]    AXI_04_MC_STATUS,
  output [7:0]    AXI_04_PHY_STATUS,
  
  output          AXI_05_ARREADY,
  output          AXI_05_AWREADY,
  output [ 31:0]  AXI_05_RDATA_PARITY,
  output [255:0]  AXI_05_RDATA,
  output [  5:0]  AXI_05_RID,
  output          AXI_05_RLAST,
  output [  1:0]  AXI_05_RRESP,
  output          AXI_05_RVALID,
  output          AXI_05_WREADY,
  output [  5:0]  AXI_05_BID,
  output [  1:0]  AXI_05_BRESP,
  output          AXI_05_BVALID,
  output [  1:0]  AXI_05_DFI_AW_AERR_N,
  output          AXI_05_DFI_CLK_BUF,
  output [  7:0]  AXI_05_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_05_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_05_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_05_DFI_DW_RDDATA_VALID,
  output          AXI_05_DFI_INIT_COMPLETE,
  output          AXI_05_DFI_PHYUPD_REQ,
  output          AXI_05_DFI_PHY_LP_STATE,
  output          AXI_05_DFI_RST_N_BUF,
  
  output          AXI_06_ARREADY,
  output          AXI_06_AWREADY,
  output [ 31:0]  AXI_06_RDATA_PARITY,
  output [255:0]  AXI_06_RDATA,
  output [  5:0]  AXI_06_RID,
  output          AXI_06_RLAST,
  output [  1:0]  AXI_06_RRESP,
  output          AXI_06_RVALID,
  output          AXI_06_WREADY,
  output [  5:0]  AXI_06_BID,
  output [  1:0]  AXI_06_BRESP,
  output          AXI_06_BVALID,
  output [  1:0]  AXI_06_DFI_AW_AERR_N,
  output          AXI_06_DFI_CLK_BUF,
  output [  7:0]  AXI_06_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_06_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_06_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_06_DFI_DW_RDDATA_VALID,
  output          AXI_06_DFI_INIT_COMPLETE,
  output          AXI_06_DFI_PHYUPD_REQ,
  output          AXI_06_DFI_PHY_LP_STATE,
  output          AXI_06_DFI_RST_N_BUF,
  output [5:0]    AXI_06_MC_STATUS,
  output [7:0]    AXI_06_PHY_STATUS,
  
  output          AXI_07_ARREADY,
  output          AXI_07_AWREADY,
  output [ 31:0]  AXI_07_RDATA_PARITY,
  output [255:0]  AXI_07_RDATA,
  output [  5:0]  AXI_07_RID,
  output          AXI_07_RLAST,
  output [  1:0]  AXI_07_RRESP,
  output          AXI_07_RVALID,
  output          AXI_07_WREADY,
  output [  5:0]  AXI_07_BID,
  output [  1:0]  AXI_07_BRESP,
  output          AXI_07_BVALID,
  output [  1:0]  AXI_07_DFI_AW_AERR_N,
  output          AXI_07_DFI_CLK_BUF,
  output [  7:0]  AXI_07_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_07_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_07_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_07_DFI_DW_RDDATA_VALID,
  output          AXI_07_DFI_INIT_COMPLETE,
  output          AXI_07_DFI_PHYUPD_REQ,
  output          AXI_07_DFI_PHY_LP_STATE,
  output          AXI_07_DFI_RST_N_BUF,
  
  output          AXI_08_ARREADY,
  output          AXI_08_AWREADY,
  output [ 31:0]  AXI_08_RDATA_PARITY,
  output [255:0]  AXI_08_RDATA,
  output [  5:0]  AXI_08_RID,
  output          AXI_08_RLAST,
  output [  1:0]  AXI_08_RRESP,
  output          AXI_08_RVALID,
  output          AXI_08_WREADY,
  output [  5:0]  AXI_08_BID,
  output [  1:0]  AXI_08_BRESP,
  output          AXI_08_BVALID,
  output [  1:0]  AXI_08_DFI_AW_AERR_N,
  output          AXI_08_DFI_CLK_BUF,
  output [  7:0]  AXI_08_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_08_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_08_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_08_DFI_DW_RDDATA_VALID,
  output          AXI_08_DFI_INIT_COMPLETE,
  output          AXI_08_DFI_PHYUPD_REQ,
  output          AXI_08_DFI_PHY_LP_STATE,
  output          AXI_08_DFI_RST_N_BUF,
  output [5:0]    AXI_08_MC_STATUS,
  output [7:0]    AXI_08_PHY_STATUS,
  
  output          AXI_09_ARREADY,
  output          AXI_09_AWREADY,
  output [ 31:0]  AXI_09_RDATA_PARITY,
  output [255:0]  AXI_09_RDATA,
  output [  5:0]  AXI_09_RID,
  output          AXI_09_RLAST,
  output [  1:0]  AXI_09_RRESP,
  output          AXI_09_RVALID,
  output          AXI_09_WREADY,
  output [  5:0]  AXI_09_BID,
  output [  1:0]  AXI_09_BRESP,
  output          AXI_09_BVALID,
  output [  1:0]  AXI_09_DFI_AW_AERR_N,
  output          AXI_09_DFI_CLK_BUF,
  output [  7:0]  AXI_09_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_09_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_09_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_09_DFI_DW_RDDATA_VALID,
  output          AXI_09_DFI_INIT_COMPLETE,
  output          AXI_09_DFI_PHYUPD_REQ,
  output          AXI_09_DFI_PHY_LP_STATE,
  output          AXI_09_DFI_RST_N_BUF,
  
  output          AXI_10_ARREADY,
  output          AXI_10_AWREADY,
  output [ 31:0]  AXI_10_RDATA_PARITY,
  output [255:0]  AXI_10_RDATA,
  output [  5:0]  AXI_10_RID,
  output          AXI_10_RLAST,
  output [  1:0]  AXI_10_RRESP,
  output          AXI_10_RVALID,
  output          AXI_10_WREADY,
  output [  5:0]  AXI_10_BID,
  output [  1:0]  AXI_10_BRESP,
  output          AXI_10_BVALID,
  output [  1:0]  AXI_10_DFI_AW_AERR_N,
  output          AXI_10_DFI_CLK_BUF,
  output [  7:0]  AXI_10_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_10_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_10_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_10_DFI_DW_RDDATA_VALID,
  output          AXI_10_DFI_INIT_COMPLETE,
  output          AXI_10_DFI_PHYUPD_REQ,
  output          AXI_10_DFI_PHY_LP_STATE,
  output          AXI_10_DFI_RST_N_BUF,
  output [5:0]    AXI_10_MC_STATUS,
  output [7:0]    AXI_10_PHY_STATUS,
  
  output          AXI_11_ARREADY,
  output          AXI_11_AWREADY,
  output [ 31:0]  AXI_11_RDATA_PARITY,
  output [255:0]  AXI_11_RDATA,
  output [  5:0]  AXI_11_RID,
  output          AXI_11_RLAST,
  output [  1:0]  AXI_11_RRESP,
  output          AXI_11_RVALID,
  output          AXI_11_WREADY,
  output [  5:0]  AXI_11_BID,
  output [  1:0]  AXI_11_BRESP,
  output          AXI_11_BVALID,
  output [  1:0]  AXI_11_DFI_AW_AERR_N,
  output          AXI_11_DFI_CLK_BUF,
  output [  7:0]  AXI_11_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_11_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_11_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_11_DFI_DW_RDDATA_VALID,
  output          AXI_11_DFI_INIT_COMPLETE,
  output          AXI_11_DFI_PHYUPD_REQ,
  output          AXI_11_DFI_PHY_LP_STATE,
  output          AXI_11_DFI_RST_N_BUF,
  
  output          AXI_12_ARREADY,
  output          AXI_12_AWREADY,
  output [ 31:0]  AXI_12_RDATA_PARITY,
  output [255:0]  AXI_12_RDATA,
  output [  5:0]  AXI_12_RID,
  output          AXI_12_RLAST,
  output [  1:0]  AXI_12_RRESP,
  output          AXI_12_RVALID,
  output          AXI_12_WREADY,
  output [  5:0]  AXI_12_BID,
  output [  1:0]  AXI_12_BRESP,
  output          AXI_12_BVALID,
  output [  1:0]  AXI_12_DFI_AW_AERR_N,
  output          AXI_12_DFI_CLK_BUF,
  output [  7:0]  AXI_12_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_12_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_12_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_12_DFI_DW_RDDATA_VALID,
  output          AXI_12_DFI_INIT_COMPLETE,
  output          AXI_12_DFI_PHYUPD_REQ,
  output          AXI_12_DFI_PHY_LP_STATE,
  output          AXI_12_DFI_RST_N_BUF,
  output [5:0]    AXI_12_MC_STATUS,
  output [7:0]    AXI_12_PHY_STATUS,
  
  output          AXI_13_ARREADY,
  output          AXI_13_AWREADY,
  output [ 31:0]  AXI_13_RDATA_PARITY,
  output [255:0]  AXI_13_RDATA,
  output [  5:0]  AXI_13_RID,
  output          AXI_13_RLAST,
  output [  1:0]  AXI_13_RRESP,
  output          AXI_13_RVALID,
  output          AXI_13_WREADY,
  output [  5:0]  AXI_13_BID,
  output [  1:0]  AXI_13_BRESP,
  output          AXI_13_BVALID,
  output [  1:0]  AXI_13_DFI_AW_AERR_N,
  output          AXI_13_DFI_CLK_BUF,
  output [  7:0]  AXI_13_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_13_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_13_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_13_DFI_DW_RDDATA_VALID,
  output          AXI_13_DFI_INIT_COMPLETE,
  output          AXI_13_DFI_PHYUPD_REQ,
  output          AXI_13_DFI_PHY_LP_STATE,
  output          AXI_13_DFI_RST_N_BUF,
  
  output          AXI_14_ARREADY,
  output          AXI_14_AWREADY,
  output [ 31:0]  AXI_14_RDATA_PARITY,
  output [255:0]  AXI_14_RDATA,
  output [  5:0]  AXI_14_RID,
  output          AXI_14_RLAST,
  output [  1:0]  AXI_14_RRESP,
  output          AXI_14_RVALID,
  output          AXI_14_WREADY,
  output [  5:0]  AXI_14_BID,
  output [  1:0]  AXI_14_BRESP,
  output          AXI_14_BVALID,
  output [  1:0]  AXI_14_DFI_AW_AERR_N,
  output          AXI_14_DFI_CLK_BUF,
  output [  7:0]  AXI_14_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_14_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_14_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_14_DFI_DW_RDDATA_VALID,
  output          AXI_14_DFI_INIT_COMPLETE,
  output          AXI_14_DFI_PHYUPD_REQ,
  output          AXI_14_DFI_PHY_LP_STATE,
  output          AXI_14_DFI_RST_N_BUF,
  output [5:0]    AXI_14_MC_STATUS,
  output [7:0]    AXI_14_PHY_STATUS,
  
  output          AXI_15_ARREADY,
  output          AXI_15_AWREADY,
  output [ 31:0]  AXI_15_RDATA_PARITY,
  output [255:0]  AXI_15_RDATA,
  output [  5:0]  AXI_15_RID,
  output          AXI_15_RLAST,
  output [  1:0]  AXI_15_RRESP,
  output          AXI_15_RVALID,
  output          AXI_15_WREADY,
  output [  5:0]  AXI_15_BID,
  output [  1:0]  AXI_15_BRESP,
  output          AXI_15_BVALID,
  output [  1:0]  AXI_15_DFI_AW_AERR_N,
  output          AXI_15_DFI_CLK_BUF,
  output [  7:0]  AXI_15_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_15_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_15_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_15_DFI_DW_RDDATA_VALID,
  output          AXI_15_DFI_INIT_COMPLETE,
  output          AXI_15_DFI_PHYUPD_REQ,
  output          AXI_15_DFI_PHY_LP_STATE,
  output          AXI_15_DFI_RST_N_BUF,
  
  output          AXI_16_ARREADY,
  output          AXI_16_AWREADY,
  output [ 31:0]  AXI_16_RDATA_PARITY,
  output [255:0]  AXI_16_RDATA,
  output [  5:0]  AXI_16_RID,
  output          AXI_16_RLAST,
  output [  1:0]  AXI_16_RRESP,
  output          AXI_16_RVALID,
  output          AXI_16_WREADY,
  output [  5:0]  AXI_16_BID,
  output [  1:0]  AXI_16_BRESP,
  output          AXI_16_BVALID,
  output [  1:0]  AXI_16_DFI_AW_AERR_N,
  output          AXI_16_DFI_CLK_BUF,
  output [  7:0]  AXI_16_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_16_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_16_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_16_DFI_DW_RDDATA_VALID,
  output          AXI_16_DFI_INIT_COMPLETE,
  output          AXI_16_DFI_PHYUPD_REQ,
  output          AXI_16_DFI_PHY_LP_STATE,
  output          AXI_16_DFI_RST_N_BUF,
  output [5:0]    AXI_16_MC_STATUS,
  output [7:0]    AXI_16_PHY_STATUS,
  
  output          AXI_17_ARREADY,
  output          AXI_17_AWREADY,
  output [ 31:0]  AXI_17_RDATA_PARITY,
  output [255:0]  AXI_17_RDATA,
  output [  5:0]  AXI_17_RID,
  output          AXI_17_RLAST,
  output [  1:0]  AXI_17_RRESP,
  output          AXI_17_RVALID,
  output          AXI_17_WREADY,
  output [  5:0]  AXI_17_BID,
  output [  1:0]  AXI_17_BRESP,
  output          AXI_17_BVALID,
  output [  1:0]  AXI_17_DFI_AW_AERR_N,
  output          AXI_17_DFI_CLK_BUF,
  output [  7:0]  AXI_17_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_17_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_17_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_17_DFI_DW_RDDATA_VALID,
  output          AXI_17_DFI_INIT_COMPLETE,
  output          AXI_17_DFI_PHYUPD_REQ,
  output          AXI_17_DFI_PHY_LP_STATE,
  output          AXI_17_DFI_RST_N_BUF,
  
  output          AXI_18_ARREADY,
  output          AXI_18_AWREADY,
  output [ 31:0]  AXI_18_RDATA_PARITY,
  output [255:0]  AXI_18_RDATA,
  output [  5:0]  AXI_18_RID,
  output          AXI_18_RLAST,
  output [  1:0]  AXI_18_RRESP,
  output          AXI_18_RVALID,
  output          AXI_18_WREADY,
  output [  5:0]  AXI_18_BID,
  output [  1:0]  AXI_18_BRESP,
  output          AXI_18_BVALID,
  output [  1:0]  AXI_18_DFI_AW_AERR_N,
  output          AXI_18_DFI_CLK_BUF,
  output [  7:0]  AXI_18_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_18_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_18_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_18_DFI_DW_RDDATA_VALID,
  output          AXI_18_DFI_INIT_COMPLETE,
  output          AXI_18_DFI_PHYUPD_REQ,
  output          AXI_18_DFI_PHY_LP_STATE,
  output          AXI_18_DFI_RST_N_BUF,
  output [5:0]    AXI_18_MC_STATUS,
  output [7:0]    AXI_18_PHY_STATUS,
  
  output          AXI_19_ARREADY,
  output          AXI_19_AWREADY,
  output [ 31:0]  AXI_19_RDATA_PARITY,
  output [255:0]  AXI_19_RDATA,
  output [  5:0]  AXI_19_RID,
  output          AXI_19_RLAST,
  output [  1:0]  AXI_19_RRESP,
  output          AXI_19_RVALID,
  output          AXI_19_WREADY,
  output [  5:0]  AXI_19_BID,
  output [  1:0]  AXI_19_BRESP,
  output          AXI_19_BVALID,
  output [  1:0]  AXI_19_DFI_AW_AERR_N,
  output          AXI_19_DFI_CLK_BUF,
  output [  7:0]  AXI_19_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_19_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_19_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_19_DFI_DW_RDDATA_VALID,
  output          AXI_19_DFI_INIT_COMPLETE,
  output          AXI_19_DFI_PHYUPD_REQ,
  output          AXI_19_DFI_PHY_LP_STATE,
  output          AXI_19_DFI_RST_N_BUF,
  
  output          AXI_20_ARREADY,
  output          AXI_20_AWREADY,
  output [ 31:0]  AXI_20_RDATA_PARITY,
  output [255:0]  AXI_20_RDATA,
  output [  5:0]  AXI_20_RID,
  output          AXI_20_RLAST,
  output [  1:0]  AXI_20_RRESP,
  output          AXI_20_RVALID,
  output          AXI_20_WREADY,
  output [  5:0]  AXI_20_BID,
  output [  1:0]  AXI_20_BRESP,
  output          AXI_20_BVALID,
  output [  1:0]  AXI_20_DFI_AW_AERR_N,
  output          AXI_20_DFI_CLK_BUF,
  output [  7:0]  AXI_20_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_20_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_20_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_20_DFI_DW_RDDATA_VALID,
  output          AXI_20_DFI_INIT_COMPLETE,
  output          AXI_20_DFI_PHYUPD_REQ,
  output          AXI_20_DFI_PHY_LP_STATE,
  output          AXI_20_DFI_RST_N_BUF,
  output [5:0]    AXI_20_MC_STATUS,
  output [7:0]    AXI_20_PHY_STATUS,
  
  output          AXI_21_ARREADY,
  output          AXI_21_AWREADY,
  output [ 31:0]  AXI_21_RDATA_PARITY,
  output [255:0]  AXI_21_RDATA,
  output [  5:0]  AXI_21_RID,
  output          AXI_21_RLAST,
  output [  1:0]  AXI_21_RRESP,
  output          AXI_21_RVALID,
  output          AXI_21_WREADY,
  output [  5:0]  AXI_21_BID,
  output [  1:0]  AXI_21_BRESP,
  output          AXI_21_BVALID,
  output [  1:0]  AXI_21_DFI_AW_AERR_N,
  output          AXI_21_DFI_CLK_BUF,
  output [  7:0]  AXI_21_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_21_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_21_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_21_DFI_DW_RDDATA_VALID,
  output          AXI_21_DFI_INIT_COMPLETE,
  output          AXI_21_DFI_PHYUPD_REQ,
  output          AXI_21_DFI_PHY_LP_STATE,
  output          AXI_21_DFI_RST_N_BUF,
  
  output          AXI_22_ARREADY,
  output          AXI_22_AWREADY,
  output [ 31:0]  AXI_22_RDATA_PARITY,
  output [255:0]  AXI_22_RDATA,
  output [  5:0]  AXI_22_RID,
  output          AXI_22_RLAST,
  output [  1:0]  AXI_22_RRESP,
  output          AXI_22_RVALID,
  output          AXI_22_WREADY,
  output [  5:0]  AXI_22_BID,
  output [  1:0]  AXI_22_BRESP,
  output          AXI_22_BVALID,
  output [  1:0]  AXI_22_DFI_AW_AERR_N,
  output          AXI_22_DFI_CLK_BUF,
  output [  7:0]  AXI_22_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_22_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_22_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_22_DFI_DW_RDDATA_VALID,
  output          AXI_22_DFI_INIT_COMPLETE,
  output          AXI_22_DFI_PHYUPD_REQ,
  output          AXI_22_DFI_PHY_LP_STATE,
  output          AXI_22_DFI_RST_N_BUF,
  output [5:0]    AXI_22_MC_STATUS,
  output [7:0]    AXI_22_PHY_STATUS,
  
  output          AXI_23_ARREADY,
  output          AXI_23_AWREADY,
  output [ 31:0]  AXI_23_RDATA_PARITY,
  output [255:0]  AXI_23_RDATA,
  output [  5:0]  AXI_23_RID,
  output          AXI_23_RLAST,
  output [  1:0]  AXI_23_RRESP,
  output          AXI_23_RVALID,
  output          AXI_23_WREADY,
  output [  5:0]  AXI_23_BID,
  output [  1:0]  AXI_23_BRESP,
  output          AXI_23_BVALID,
  output [  1:0]  AXI_23_DFI_AW_AERR_N,
  output          AXI_23_DFI_CLK_BUF,
  output [  7:0]  AXI_23_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_23_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_23_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_23_DFI_DW_RDDATA_VALID,
  output          AXI_23_DFI_INIT_COMPLETE,
  output          AXI_23_DFI_PHYUPD_REQ,
  output          AXI_23_DFI_PHY_LP_STATE,
  output          AXI_23_DFI_RST_N_BUF,
  
  output          AXI_24_ARREADY,
  output          AXI_24_AWREADY,
  output [ 31:0]  AXI_24_RDATA_PARITY,
  output [255:0]  AXI_24_RDATA,
  output [  5:0]  AXI_24_RID,
  output          AXI_24_RLAST,
  output [  1:0]  AXI_24_RRESP,
  output          AXI_24_RVALID,
  output          AXI_24_WREADY,
  output [  5:0]  AXI_24_BID,
  output [  1:0]  AXI_24_BRESP,
  output          AXI_24_BVALID,
  output [  1:0]  AXI_24_DFI_AW_AERR_N,
  output          AXI_24_DFI_CLK_BUF,
  output [  7:0]  AXI_24_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_24_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_24_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_24_DFI_DW_RDDATA_VALID,
  output          AXI_24_DFI_INIT_COMPLETE,
  output          AXI_24_DFI_PHYUPD_REQ,
  output          AXI_24_DFI_PHY_LP_STATE,
  output          AXI_24_DFI_RST_N_BUF,
  output [5:0]    AXI_24_MC_STATUS,
  output [7:0]    AXI_24_PHY_STATUS,
  
  output          AXI_25_ARREADY,
  output          AXI_25_AWREADY,
  output [ 31:0]  AXI_25_RDATA_PARITY,
  output [255:0]  AXI_25_RDATA,
  output [  5:0]  AXI_25_RID,
  output          AXI_25_RLAST,
  output [  1:0]  AXI_25_RRESP,
  output          AXI_25_RVALID,
  output          AXI_25_WREADY,
  output [  5:0]  AXI_25_BID,
  output [  1:0]  AXI_25_BRESP,
  output          AXI_25_BVALID,
  output [  1:0]  AXI_25_DFI_AW_AERR_N,
  output          AXI_25_DFI_CLK_BUF,
  output [  7:0]  AXI_25_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_25_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_25_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_25_DFI_DW_RDDATA_VALID,
  output          AXI_25_DFI_INIT_COMPLETE,
  output          AXI_25_DFI_PHYUPD_REQ,
  output          AXI_25_DFI_PHY_LP_STATE,
  output          AXI_25_DFI_RST_N_BUF,
  
  output          AXI_26_ARREADY,
  output          AXI_26_AWREADY,
  output [ 31:0]  AXI_26_RDATA_PARITY,
  output [255:0]  AXI_26_RDATA,
  output [  5:0]  AXI_26_RID,
  output          AXI_26_RLAST,
  output [  1:0]  AXI_26_RRESP,
  output          AXI_26_RVALID,
  output          AXI_26_WREADY,
  output [  5:0]  AXI_26_BID,
  output [  1:0]  AXI_26_BRESP,
  output          AXI_26_BVALID,
  output [  1:0]  AXI_26_DFI_AW_AERR_N,
  output          AXI_26_DFI_CLK_BUF,
  output [  7:0]  AXI_26_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_26_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_26_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_26_DFI_DW_RDDATA_VALID,
  output          AXI_26_DFI_INIT_COMPLETE,
  output          AXI_26_DFI_PHYUPD_REQ,
  output          AXI_26_DFI_PHY_LP_STATE,
  output          AXI_26_DFI_RST_N_BUF,
  output [5:0]    AXI_26_MC_STATUS,
  output [7:0]    AXI_26_PHY_STATUS,
  
  output          AXI_27_ARREADY,
  output          AXI_27_AWREADY,
  output [ 31:0]  AXI_27_RDATA_PARITY,
  output [255:0]  AXI_27_RDATA,
  output [  5:0]  AXI_27_RID,
  output          AXI_27_RLAST,
  output [  1:0]  AXI_27_RRESP,
  output          AXI_27_RVALID,
  output          AXI_27_WREADY,
  output [  5:0]  AXI_27_BID,
  output [  1:0]  AXI_27_BRESP,
  output          AXI_27_BVALID,
  output [  1:0]  AXI_27_DFI_AW_AERR_N,
  output          AXI_27_DFI_CLK_BUF,
  output [  7:0]  AXI_27_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_27_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_27_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_27_DFI_DW_RDDATA_VALID,
  output          AXI_27_DFI_INIT_COMPLETE,
  output          AXI_27_DFI_PHYUPD_REQ,
  output          AXI_27_DFI_PHY_LP_STATE,
  output          AXI_27_DFI_RST_N_BUF,
  
  output          AXI_28_ARREADY,
  output          AXI_28_AWREADY,
  output [ 31:0]  AXI_28_RDATA_PARITY,
  output [255:0]  AXI_28_RDATA,
  output [  5:0]  AXI_28_RID,
  output          AXI_28_RLAST,
  output [  1:0]  AXI_28_RRESP,
  output          AXI_28_RVALID,
  output          AXI_28_WREADY,
  output [  5:0]  AXI_28_BID,
  output [  1:0]  AXI_28_BRESP,
  output          AXI_28_BVALID,
  output [  1:0]  AXI_28_DFI_AW_AERR_N,
  output          AXI_28_DFI_CLK_BUF,
  output [  7:0]  AXI_28_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_28_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_28_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_28_DFI_DW_RDDATA_VALID,
  output          AXI_28_DFI_INIT_COMPLETE,
  output          AXI_28_DFI_PHYUPD_REQ,
  output          AXI_28_DFI_PHY_LP_STATE,
  output          AXI_28_DFI_RST_N_BUF,
  output [5:0]    AXI_28_MC_STATUS,
  output [7:0]    AXI_28_PHY_STATUS,
  
  output          AXI_29_ARREADY,
  output          AXI_29_AWREADY,
  output [ 31:0]  AXI_29_RDATA_PARITY,
  output [255:0]  AXI_29_RDATA,
  output [  5:0]  AXI_29_RID,
  output          AXI_29_RLAST,
  output [  1:0]  AXI_29_RRESP,
  output          AXI_29_RVALID,
  output          AXI_29_WREADY,
  output [  5:0]  AXI_29_BID,
  output [  1:0]  AXI_29_BRESP,
  output          AXI_29_BVALID,
  output [  1:0]  AXI_29_DFI_AW_AERR_N,
  output          AXI_29_DFI_CLK_BUF,
  output [  7:0]  AXI_29_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_29_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_29_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_29_DFI_DW_RDDATA_VALID,
  output          AXI_29_DFI_INIT_COMPLETE,
  output          AXI_29_DFI_PHYUPD_REQ,
  output          AXI_29_DFI_PHY_LP_STATE,
  output          AXI_29_DFI_RST_N_BUF,
  
  output          AXI_30_ARREADY,
  output          AXI_30_AWREADY,
  output [ 31:0]  AXI_30_RDATA_PARITY,
  output [255:0]  AXI_30_RDATA,
  output [  5:0]  AXI_30_RID,
  output          AXI_30_RLAST,
  output [  1:0]  AXI_30_RRESP,
  output          AXI_30_RVALID,
  output          AXI_30_WREADY,
  output [  5:0]  AXI_30_BID,
  output [  1:0]  AXI_30_BRESP,
  output          AXI_30_BVALID,
  output [  1:0]  AXI_30_DFI_AW_AERR_N,
  output          AXI_30_DFI_CLK_BUF,
  output [  7:0]  AXI_30_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_30_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_30_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_30_DFI_DW_RDDATA_VALID,
  output          AXI_30_DFI_INIT_COMPLETE,
  output          AXI_30_DFI_PHYUPD_REQ,
  output          AXI_30_DFI_PHY_LP_STATE,
  output          AXI_30_DFI_RST_N_BUF,
  output [5:0]    AXI_30_MC_STATUS,
  output [7:0]    AXI_30_PHY_STATUS,
  
  output          AXI_31_ARREADY,
  output          AXI_31_AWREADY,
  output [ 31:0]  AXI_31_RDATA_PARITY,
  output [255:0]  AXI_31_RDATA,
  output [  5:0]  AXI_31_RID,
  output          AXI_31_RLAST,
  output [  1:0]  AXI_31_RRESP,
  output          AXI_31_RVALID,
  output          AXI_31_WREADY,
  output [  5:0]  AXI_31_BID,
  output [  1:0]  AXI_31_BRESP,
  output          AXI_31_BVALID,
  output [  1:0]  AXI_31_DFI_AW_AERR_N,
  output          AXI_31_DFI_CLK_BUF,
  output [  7:0]  AXI_31_DFI_DBI_BYTE_DISABLE,
  output [20:00]  AXI_31_DFI_DW_RDDATA_DBI,
  output [  7:0]  AXI_31_DFI_DW_RDDATA_DERR,
  output [  1:0]  AXI_31_DFI_DW_RDDATA_VALID,
  output          AXI_31_DFI_INIT_COMPLETE,
  output          AXI_31_DFI_PHYUPD_REQ,
  output          AXI_31_DFI_PHY_LP_STATE,
  output          AXI_31_DFI_RST_N_BUF,
  
  output [ 31:0]  APB_0_PRDATA,
  output          APB_0_PREADY,
  output          APB_0_PSLVERR,
  
  output [ 31:0]  APB_1_PRDATA,
  output          APB_1_PREADY,
  output          APB_1_PSLVERR,
  
  output [ 31:0]  APB_0_PWDATA_MON,
  output [ 21:0]  APB_0_PADDR_MON,
  output          APB_0_PENABLE_MON,
  output          APB_0_PSEL_MON,
  output          APB_0_PWRITE_MON,
  output [ 31:0]  APB_0_PRDATA_MON,
  output          APB_0_PREADY_MON,
  output          APB_0_PSLVERR_MON,
  
  output [ 31:0]  APB_1_PWDATA_MON,
  output [ 21:0]  APB_1_PADDR_MON,
  output          APB_1_PENABLE_MON,
  output          APB_1_PSEL_MON,
  output          APB_1_PWRITE_MON,
  output [ 31:0]  APB_1_PRDATA_MON,
  output          APB_1_PREADY_MON,
  output          APB_1_PSLVERR_MON,

  output          apb_complete_0,
  output          apb_complete_1,

  (* DONT_TOUCH = "true" *) input  [36:0]   sl_iport0,
  (* DONT_TOUCH = "true" *) output [16:0]   sl_oport0,
  (* DONT_TOUCH = "true" *) input  [36:0]   sl_iport1,
  (* DONT_TOUCH = "true" *) output [16:0]   sl_oport1,

  output          DRAM_0_STAT_CATTRIP,
  output [  6:0]  TEMP_STATUS_ST0,
  
  output          DRAM_1_STAT_CATTRIP,
  output [  6:0]  TEMP_STATUS_ST1
);

////////////////////////////////////////////////////////////////////////////////
// Local Parameter declaration
////////////////////////////////////////////////////////////////////////////////
localparam [15:0] AXI_SW_CLK_SEL_0 = (CLK_SEL_00 == "TRUE") ? 0   :
                                     ((CLK_SEL_01 == "TRUE") ? 1  :
                                     ((CLK_SEL_02 == "TRUE") ? 2  :
                                     ((CLK_SEL_03 == "TRUE") ? 3  :
                                     ((CLK_SEL_04 == "TRUE") ? 4  :
                                     ((CLK_SEL_05 == "TRUE") ? 5  :
                                     ((CLK_SEL_06 == "TRUE") ? 6  :
                                     ((CLK_SEL_07 == "TRUE") ? 7  :
                                     ((CLK_SEL_08 == "TRUE") ? 8  :
                                     ((CLK_SEL_09 == "TRUE") ? 9  :
                                     ((CLK_SEL_10 == "TRUE") ? 10 :
                                     ((CLK_SEL_11 == "TRUE") ? 11 :
                                     ((CLK_SEL_12 == "TRUE") ? 12 :
															       ((CLK_SEL_13 == "TRUE") ? 13 :
                                     ((CLK_SEL_14 == "TRUE") ? 14 :
                                     ((CLK_SEL_15 == "TRUE") ? 15 : 0)))))))))))))));
localparam [15:0] AXI_SW_CLK_SEL_1 = (CLK_SEL_16 == "TRUE") ? 16  :
                                     ((CLK_SEL_17 == "TRUE") ? 17 :
                                     ((CLK_SEL_18 == "TRUE") ? 18 :
                                     ((CLK_SEL_19 == "TRUE") ? 19 :
                                     ((CLK_SEL_20 == "TRUE") ? 20 :
                                     ((CLK_SEL_21 == "TRUE") ? 21 :
                                     ((CLK_SEL_22 == "TRUE") ? 22 :
                                     ((CLK_SEL_23 == "TRUE") ? 23 :
                                     ((CLK_SEL_24 == "TRUE") ? 24 :
                                     ((CLK_SEL_25 == "TRUE") ? 25 :
                                     ((CLK_SEL_26 == "TRUE") ? 26 :
                                     ((CLK_SEL_27 == "TRUE") ? 27 :
                                     ((CLK_SEL_28 == "TRUE") ? 28 :
															       ((CLK_SEL_29 == "TRUE") ? 29 :
                                     ((CLK_SEL_30 == "TRUE") ? 30 :
                                     ((CLK_SEL_31 == "TRUE") ? 31 : 0)))))))))))))));

////////////////////////////////////////////////////////////////////////////////
// Internal Wire declaration
////////////////////////////////////////////////////////////////////////////////
wire [2:0]            DRAM_0_STAT_TEMP;
wire [2:0]            DRAM_1_STAT_TEMP;

wire                  xpm_ena_0;
wire                  xpm_ena_1;
wire                  xpm_wea_0;
wire                  xpm_wea_1;
wire [10:0]           xpm_addra_0;
wire [10:0]           xpm_addra_1;
wire [31:0]           xpm_dina_0;
wire [31:0]           xpm_dina_1;
wire [31:0]           xpm_douta_0;
wire [31:0]           xpm_douta_1;
wire                  apb_back_press_0;
wire                  apb_poll_complete_0;
wire                  init_seq_complete_0;
wire                  gen_apb_tran_0;
wire                  gen_apb_wr_rd_r_0;
wire                  gen_poll_0;
wire [21:0]           gen_apb_addr_0;
wire [31:0]           gen_apb_data_0;
wire                  valid_window_fail_0;
wire                  apb_back_press_1;
wire                  apb_poll_complete_1;
wire                  init_seq_complete_1;
wire                  gen_apb_tran_1;
wire                  gen_apb_wr_rd_r_1;
wire                  gen_poll_1;
wire [21:0]           gen_apb_addr_1;
wire [31:0]           gen_apb_data_1;
wire                  valid_window_fail_1;
wire                  intrnl_apb_psel_0_s;
wire                  intrnl_apb_pwrite_0_s;
wire                  intrnl_apb_penable_0_s;
wire [21:0]           intrnl_apb_paddr_0_s;
wire [31:0]           intrnl_apb_pwdata_0_s;
wire [31:0]           intrnl_apb_prdata_0_s;
wire                  intrnl_apb_pready_0_s;
wire                  intrnl_apb_pslverr_0_s;
wire                  intrnl_apb_psel_1_s;
wire                  intrnl_apb_pwrite_1_s;
wire                  intrnl_apb_penable_1_s;
wire [21:0]           intrnl_apb_paddr_1_s;
wire [31:0]           intrnl_apb_pwdata_1_s;
wire [31:0]           intrnl_apb_prdata_1_s;
wire                  intrnl_apb_pready_1_s;
wire                  intrnl_apb_pslverr_1_s;
wire                  xsdb_apb_req_0_s;
wire                  xsdb_apb_psel_0_s;
wire                  xsdb_apb_pwrite_0_s;
wire                  xsdb_apb_penable_0_s;
wire [21:0]           xsdb_apb_paddr_0_s;
wire [31:0]           xsdb_apb_pwdata_0_s;
wire [31:0]           xsdb_apb_prdata_0_s;
wire                  xsdb_apb_pready_0_s;
wire                  xsdb_apb_pslverr_0_s;
wire                  xsdb_apb_req_1_s;
wire                  xsdb_apb_psel_1_s;
wire                  xsdb_apb_pwrite_1_s;
wire                  xsdb_apb_penable_1_s;
wire [21:0]           xsdb_apb_paddr_1_s;
wire [31:0]           xsdb_apb_pwdata_1_s;
wire [31:0]           xsdb_apb_prdata_1_s;
wire                  xsdb_apb_pready_1_s;
wire                  xsdb_apb_pslverr_1_s;
wire                  temp_apb_req_0_s;
wire                  temp_apb_grant_0_s;
wire                  temp_valid_0_s;
wire [6:0]            temp_value_0_s;
wire                  temp_apb_psel_0_s;
wire                  temp_apb_pwrite_0_s;
wire                  temp_apb_penable_0_s;
wire [21:0]           temp_apb_paddr_0_s;
wire [31:0]           temp_apb_pwdata_0_s;
wire [31:0]           temp_apb_prdata_0_s;
wire                  temp_apb_pready_0_s;
wire                  temp_apb_pslverr_0_s;

wire                  temp_apb_req_1_s;
wire                  temp_apb_grant_1_s;
wire                  temp_valid_1_s;
wire [6:0]            temp_value_1_s;
wire                  temp_apb_psel_1_s;
wire                  temp_apb_pwrite_1_s;
wire                  temp_apb_penable_1_s;
wire [21:0]           temp_apb_paddr_1_s;
wire [31:0]           temp_apb_pwdata_1_s;
wire [31:0]           temp_apb_prdata_1_s;
wire                  temp_apb_pready_1_s;
wire                  temp_apb_pslverr_1_s;

wire [240:0]          x2a_debug_0;
wire [240:0]          x2a_debug_1;
wire                  psel_0;
wire                  pwrite_0;
wire                  penable_0;
wire [21:0]           paddr_0;
wire [31:0]           pwdata_0;
wire [31:0]           prdata_0;
wire                  pready_0;
wire                  pslverr_0;
wire                  psel_1;
wire                  pwrite_1;
wire                  penable_1;
wire [21:0]           paddr_1;
wire [31:0]           pwdata_1;
wire [31:0]           prdata_1;
wire                  pready_1;
wire                  pslverr_1;

wire                  bready_00;
wire                  bready_01;
wire                  bready_02;
wire                  bready_03;
wire                  bready_04;
wire                  bready_05;
wire                  bready_06;
wire                  bready_07;
wire                  bready_08;
wire                  bready_09;
wire                  bready_10;
wire                  bready_11;
wire                  bready_12;
wire                  bready_13;
wire                  bready_14;
wire                  bready_15;
wire                  bready_16;
wire                  bready_17;
wire                  bready_18;
wire                  bready_19;
wire                  bready_20;
wire                  bready_21;
wire                  bready_22;
wire                  bready_23;
wire                  bready_24;
wire                  bready_25;
wire                  bready_26;
wire                  bready_27;
wire                  bready_28;
wire                  bready_29;
wire                  bready_30;
wire                  bready_31;

wire                  rready_00;
wire                  rready_01;
wire                  rready_02;
wire                  rready_03;
wire                  rready_04;
wire                  rready_05;
wire                  rready_06;
wire                  rready_07;
wire                  rready_08;
wire                  rready_09;
wire                  rready_10;
wire                  rready_11;
wire                  rready_12;
wire                  rready_13;
wire                  rready_14;
wire                  rready_15;
wire                  rready_16;
wire                  rready_17;
wire                  rready_18;
wire                  rready_19;
wire                  rready_20;
wire                  rready_21;
wire                  rready_22;
wire                  rready_23;
wire                  rready_24;
wire                  rready_25;
wire                  rready_26;
wire                  rready_27;
wire                  rready_28;
wire                  rready_29;
wire                  rready_30;
wire                  rready_31;

wire                  AXI_00_RST_N;
wire                  AXI_01_RST_N;
wire                  AXI_02_RST_N;
wire                  AXI_03_RST_N;
wire                  AXI_04_RST_N;
wire                  AXI_05_RST_N;
wire                  AXI_06_RST_N;
wire                  AXI_07_RST_N;
wire                  AXI_08_RST_N;
wire                  AXI_09_RST_N;
wire                  AXI_10_RST_N;
wire                  AXI_11_RST_N;
wire                  AXI_12_RST_N;
wire                  AXI_13_RST_N;
wire                  AXI_14_RST_N;
wire                  AXI_15_RST_N;
wire                  AXI_16_RST_N;
wire                  AXI_17_RST_N;
wire                  AXI_18_RST_N;
wire                  AXI_19_RST_N;
wire                  AXI_20_RST_N;
wire                  AXI_21_RST_N;
wire                  AXI_22_RST_N;
wire                  AXI_23_RST_N;
wire                  AXI_24_RST_N;
wire                  AXI_25_RST_N;
wire                  AXI_26_RST_N;
wire                  AXI_27_RST_N;
wire                  AXI_28_RST_N;
wire                  AXI_29_RST_N;
wire                  AXI_30_RST_N;
wire                  AXI_31_RST_N;

////////////////////////////////////////////////////////////////////////////////
// Generating internal BREADY as a work round for the issue discovered in
// CR-992493
////////////////////////////////////////////////////////////////////////////////
assign bready_00 = AXI_00_BREADY || (~AXI_00_BVALID);
assign bready_01 = AXI_01_BREADY || (~AXI_01_BVALID);
assign bready_02 = AXI_02_BREADY || (~AXI_02_BVALID);
assign bready_03 = AXI_03_BREADY || (~AXI_03_BVALID);
assign bready_04 = AXI_04_BREADY || (~AXI_04_BVALID);
assign bready_05 = AXI_05_BREADY || (~AXI_05_BVALID);
assign bready_06 = AXI_06_BREADY || (~AXI_06_BVALID);
assign bready_07 = AXI_07_BREADY || (~AXI_07_BVALID);
assign bready_08 = AXI_08_BREADY || (~AXI_08_BVALID);
assign bready_09 = AXI_09_BREADY || (~AXI_09_BVALID);
assign bready_10 = AXI_10_BREADY || (~AXI_10_BVALID);
assign bready_11 = AXI_11_BREADY || (~AXI_11_BVALID);
assign bready_12 = AXI_12_BREADY || (~AXI_12_BVALID);
assign bready_13 = AXI_13_BREADY || (~AXI_13_BVALID);
assign bready_14 = AXI_14_BREADY || (~AXI_14_BVALID);
assign bready_15 = AXI_15_BREADY || (~AXI_15_BVALID);
assign bready_16 = AXI_16_BREADY || (~AXI_16_BVALID);
assign bready_17 = AXI_17_BREADY || (~AXI_17_BVALID);
assign bready_18 = AXI_18_BREADY || (~AXI_18_BVALID);
assign bready_19 = AXI_19_BREADY || (~AXI_19_BVALID);
assign bready_20 = AXI_20_BREADY || (~AXI_20_BVALID);
assign bready_21 = AXI_21_BREADY || (~AXI_21_BVALID);
assign bready_22 = AXI_22_BREADY || (~AXI_22_BVALID);
assign bready_23 = AXI_23_BREADY || (~AXI_23_BVALID);
assign bready_24 = AXI_24_BREADY || (~AXI_24_BVALID);
assign bready_25 = AXI_25_BREADY || (~AXI_25_BVALID);
assign bready_26 = AXI_26_BREADY || (~AXI_26_BVALID);
assign bready_27 = AXI_27_BREADY || (~AXI_27_BVALID);
assign bready_28 = AXI_28_BREADY || (~AXI_28_BVALID);
assign bready_29 = AXI_29_BREADY || (~AXI_29_BVALID);
assign bready_30 = AXI_30_BREADY || (~AXI_30_BVALID);
assign bready_31 = AXI_31_BREADY || (~AXI_31_BVALID);

////////////////////////////////////////////////////////////////////////////////
// The workaround for CR-992493 also needs to be applied for RREADY-RVALID
// signals
////////////////////////////////////////////////////////////////////////////////
assign rready_00 = AXI_00_RREADY || (~AXI_00_RVALID);
assign rready_01 = AXI_01_RREADY || (~AXI_01_RVALID);
assign rready_02 = AXI_02_RREADY || (~AXI_02_RVALID);
assign rready_03 = AXI_03_RREADY || (~AXI_03_RVALID);
assign rready_04 = AXI_04_RREADY || (~AXI_04_RVALID);
assign rready_05 = AXI_05_RREADY || (~AXI_05_RVALID);
assign rready_06 = AXI_06_RREADY || (~AXI_06_RVALID);
assign rready_07 = AXI_07_RREADY || (~AXI_07_RVALID);
assign rready_08 = AXI_08_RREADY || (~AXI_08_RVALID);
assign rready_09 = AXI_09_RREADY || (~AXI_09_RVALID);
assign rready_10 = AXI_10_RREADY || (~AXI_10_RVALID);
assign rready_11 = AXI_11_RREADY || (~AXI_11_RVALID);
assign rready_12 = AXI_12_RREADY || (~AXI_12_RVALID);
assign rready_13 = AXI_13_RREADY || (~AXI_13_RVALID);
assign rready_14 = AXI_14_RREADY || (~AXI_14_RVALID);
assign rready_15 = AXI_15_RREADY || (~AXI_15_RVALID);
assign rready_16 = AXI_16_RREADY || (~AXI_16_RVALID);
assign rready_17 = AXI_17_RREADY || (~AXI_17_RVALID);
assign rready_18 = AXI_18_RREADY || (~AXI_18_RVALID);
assign rready_19 = AXI_19_RREADY || (~AXI_19_RVALID);
assign rready_20 = AXI_20_RREADY || (~AXI_20_RVALID);
assign rready_21 = AXI_21_RREADY || (~AXI_21_RVALID);
assign rready_22 = AXI_22_RREADY || (~AXI_22_RVALID);
assign rready_23 = AXI_23_RREADY || (~AXI_23_RVALID);
assign rready_24 = AXI_24_RREADY || (~AXI_24_RVALID);
assign rready_25 = AXI_25_RREADY || (~AXI_25_RVALID);
assign rready_26 = AXI_26_RREADY || (~AXI_26_RVALID);
assign rready_27 = AXI_27_RREADY || (~AXI_27_RVALID);
assign rready_28 = AXI_28_RREADY || (~AXI_28_RVALID);
assign rready_29 = AXI_29_RREADY || (~AXI_29_RVALID);
assign rready_30 = AXI_30_RREADY || (~AXI_30_RVALID);
assign rready_31 = AXI_31_RREADY || (~AXI_31_RVALID);

////////////////////////////////////////////////////////////////////////////////
// Module instances when HBM Stack selected is One
////////////////////////////////////////////////////////////////////////////////
generate 
if (HBM_STACK == 1) begin : ONE_STACK_HBM

assign TEMP_STATUS_ST0 = temp_value_0_s;
assign TEMP_STATUS_ST1 = temp_value_0_s;

////////////////////////////////////////////////////////////////////////////////
// Instantiating XPM memory
////////////////////////////////////////////////////////////////////////////////
xpm_memory_spram # (
  // Common module parameters
  .MEMORY_SIZE        (65536),                 //positive integer
  .MEMORY_PRIMITIVE   ("auto"),               //string; "auto", "distributed", "block" or "ultra";
  .ECC_MODE           ("no_ecc"),             //do not change
`ifdef SIMULATION_MODE
  .MEMORY_INIT_FILE   ("xpm_internal_config_file_sim_0.mem"), //string; "none" or "<filename>.mem" 
`else
`ifdef NETLIST_SIM
  .MEMORY_INIT_FILE   ("xpm_internal_config_file_sim_0.mem"), //string; "none" or "<filename>.mem" 
`else
  .MEMORY_INIT_FILE   ("xpm_internal_config_file_0.mem"), //string; "none" or "<filename>.mem" 
`endif
`endif
  .MEMORY_INIT_PARAM  (""    ),              //string;
  .WAKEUP_TIME        ("disable_sleep"),     //string; "disable_sleep" or "use_sleep_pin" 
  .MESSAGE_CONTROL    (0),
  // Port A module parameters
  .WRITE_DATA_WIDTH_A (32),               //positive integer
  .READ_DATA_WIDTH_A  (32),               //positive integer
  .BYTE_WRITE_WIDTH_A (32),               //integer; 8, 9, or WRITE_DATA_WIDTH_A value
  .ADDR_WIDTH_A       (11),                //positive integer
  .READ_RESET_VALUE_A ("0"),              //string
  .READ_LATENCY_A     (1),                //non-negative integer
  .WRITE_MODE_A       ("read_first")      //string; "write_first", "read_first", "no_change" 
) xpm_memory_spram_inst_0 (
  // Common module ports
  .sleep          (1'b0),  //do not change
  // Port A module ports
  .clka           (APB_0_PCLK),
  .rsta           (~APB_0_PRESET_N),
  .ena            (xpm_ena_0),
  .regcea         (1'b1),
  .wea            (xpm_wea_0),
  .addra          (xpm_addra_0),
  .dina           (xpm_dina_0),
  .injectsbiterra (1'b0),  //do not change
  .injectdbiterra (1'b0),  //do not change
  .douta          (xpm_douta_0),
  .sbiterra       (),      //do not change
  .dbiterra       ()       //do not change
);

////////////////////////////////////////////////////////////////////////////////
// Instantiating Module to fetch data from XPM memory
////////////////////////////////////////////////////////////////////////////////
hbm_data_fetch #(
  .XPM_ADDR_WIDTH (11),
  .XPM_DATA_WIDTH (32),
  .APB_ADDR_WIDTH (22),
  .APB_DATA_WIDTH (32)
) hbm_data_fetch_0 (
  .apb_clk    (APB_0_PCLK),
  .apb_rst_n  (APB_0_PRESET_N),
  .xpm_ena    (xpm_ena_0),
  .xpm_wea    (xpm_wea_0),
  .xpm_addra  (xpm_addra_0),
  .xpm_dina   (xpm_dina_0),
  .xpm_douta  (xpm_douta_0),

  .apb_back_press    (apb_back_press_0),
  .apb_poll_complete (apb_poll_complete_0),
  .init_seq_complete (init_seq_complete_0),
  .gen_apb_tran      (gen_apb_tran_0),
  .gen_apb_wr_rd     (gen_apb_wr_rd_r_0),
  .gen_poll          (gen_poll_0),
  .gen_apb_addr      (gen_apb_addr_0),
  .gen_apb_data      (gen_apb_data_0)
);

////////////////////////////////////////////////////////////////////////////////
// Instantiating Module for APB Master interface
////////////////////////////////////////////////////////////////////////////////
hbm_apb_mst #(
  .INIT_BYPASS (INIT_BYPASS), 
  .INIT_SEQ_TIMEOUT (INIT_SEQ_TIMEOUT),
  .APB_ADDR_WIDTH (22),
  .APB_DATA_WIDTH (32)
) hbm_apb_mst_0 (
  .apb_clk           (APB_0_PCLK),
  .apb_rst_n         (APB_0_PRESET_N),
  .apb_back_press    (apb_back_press_0),
  .init_seq_complete (init_seq_complete_0),
  .gen_apb_tran      (gen_apb_tran_0),
  .gen_apb_wr_rd     (gen_apb_wr_rd_r_0),
  .gen_poll          (gen_poll_0),
  .gen_apb_addr      (gen_apb_addr_0),
  .gen_apb_data      (gen_apb_data_0),
  .apb_switch        (apb_complete_0),
  .apb_poll_complete (apb_poll_complete_0),
  .valid_window_fail (valid_window_fail_0),

  .psel              (intrnl_apb_psel_0_s),
  .pwrite            (intrnl_apb_pwrite_0_s),
  .penable           (intrnl_apb_penable_0_s),
  .paddr             (intrnl_apb_paddr_0_s),
  .pwdata            (intrnl_apb_pwdata_0_s),
  .prdata            (intrnl_apb_prdata_0_s),
  .pready            (intrnl_apb_pready_0_s),
  .pslverr           (intrnl_apb_pslverr_0_s)

);

////////////////////////////////////////////////////////////////////////////////
// Instantiating Module for XSDB
////////////////////////////////////////////////////////////////////////////////
`ifdef EN_DBG_HUB
xsdb_top #(
  .PLL_CSV_VER        (16'h0001),
  .MC_CSV_VER         (16'h0002),
  .PHY_CSV_VER        (16'h0001),
  .HBM_STACK_CSV_VER  (16'h0001),
  .HBM_STACK_NUM      (HBM_STACK_NUM),
  .HBM_CLOCK_FREQ     (HBM_CLK_FREQ_0),
  .INT_VERSION        (16'h0003),
  .SWITCH_EN          (SWITCH_EN_0),
  .AXI_SW_CLK         (AXI_SW_CLK_SEL_0),
  .PLL_REF_CLK        (HBM_REF_CLK_FREQ_0)
) u_xsdb_top_0 (
  .clkb               (APB_0_PCLK           ),
  .sl_iport0          (sl_iport0            ),
  .sl_oport0          (sl_oport0            ),
  .x2a_debug          (x2a_debug_0          ),
  .TEMP_STATUS        (TEMP_STATUS_ST0      ),
  .CATTRIP            (DRAM_0_STAT_CATTRIP  ),
  .APB_COMPLETE       (apb_complete_0),
  .XSDB_APB_GRANT     (xsdb_apb_grant_0_s   ),
  .XSDB_APB_PRDATA    (xsdb_apb_prdata_0_s  ),
  .XSDB_APB_PREADY    (xsdb_apb_pready_0_s  ),
  .XSDB_APB_PSLVERR   (xsdb_apb_pslverr_0_s ),
  .XSDB_APB_PREQ      (xsdb_apb_req_0_s     ),
  .XSDB_APB_PSEL      (xsdb_apb_psel_0_s    ),
  .XSDB_APB_PWRITE    (xsdb_apb_pwrite_0_s  ),
  .XSDB_APB_PENABLE   (xsdb_apb_penable_0_s ),
  .XSDB_APB_PADDR     (xsdb_apb_paddr_0_s   ),
  .XSDB_APB_PWDATA    (xsdb_apb_pwdata_0_s  )
);
`else
assign sl_oport0            = 17'b0;
assign xsdb_apb_req_0_s     = 1'b0;
assign xsdb_apb_psel_0_s    = 1'b0;
assign xsdb_apb_pwrite_0_s  = 1'b0;
assign xsdb_apb_penable_0_s = 1'b0;
assign xsdb_apb_paddr_0_s   = 22'b0;
assign xsdb_apb_pwdata_0_s  = 32'b0;
`endif

////////////////////////////////////////////////////////////////////////////////
// Instantiating Module for Temperature Read
////////////////////////////////////////////////////////////////////////////////
hbm_temp_rd #(
  .TEMP_WAIT_PERIOD (TEMP_WAIT_PERIOD_0),
  .APB_ADDR_WIDTH   (22),
  .APB_DATA_WIDTH   (32)
) u_hbm_temp_rd_0 (
  .apb_clk            (APB_0_PCLK),
  .apb_rst_n          (APB_0_PRESET_N),

  .temp_apb_req       (temp_apb_req_0_s),
  .temp_apb_grant     (temp_apb_grant_0_s),
  .init_seq_complete  (apb_complete_0),

  .temp_valid         (temp_valid_0_s),
  .temp_value         (temp_value_0_s),

  .psel               (temp_apb_psel_0_s   ),
  .pwrite             (temp_apb_pwrite_0_s ),
  .penable            (temp_apb_penable_0_s),
  .paddr              (temp_apb_paddr_0_s  ),
  .pwdata             (temp_apb_pwdata_0_s ),
  .prdata             (temp_apb_prdata_0_s ),
  .pready             (temp_apb_pready_0_s ),
  .pslverr            (temp_apb_pslverr_0_s)
);

////////////////////////////////////////////////////////////////////////////////
// Instantiating Module for APB MUX
////////////////////////////////////////////////////////////////////////////////
hbm_apb_arbiter #(
  .INIT_BYPASS (INIT_BYPASS), 
  .APB_ADDR_WIDTH (22),
  .APB_DATA_WIDTH (32)
) hbm_apb_arbiter_0 (
  .apb_clk                (APB_0_PCLK),
  .apb_rst_n              (APB_0_PRESET_N),

  .intrnl_apb_complete    (apb_complete_0        ),
  .intrnl_apb_psel        (intrnl_apb_psel_0_s   ),
  .intrnl_apb_pwrite      (intrnl_apb_pwrite_0_s ),
  .intrnl_apb_penable     (intrnl_apb_penable_0_s),
  .intrnl_apb_paddr       (intrnl_apb_paddr_0_s  ),
  .intrnl_apb_pwdata      (intrnl_apb_pwdata_0_s ),
  .intrnl_apb_prdata      (intrnl_apb_prdata_0_s ),
  .intrnl_apb_pready      (intrnl_apb_pready_0_s ),
  .intrnl_apb_pslverr     (intrnl_apb_pslverr_0_s),

  .extrnl_apb_psel        (APB_0_PSEL            ),
  .extrnl_apb_pwrite      (APB_0_PWRITE          ),
  .extrnl_apb_penable     (APB_0_PENABLE         ),
  .extrnl_apb_paddr       (APB_0_PADDR           ),
  .extrnl_apb_pwdata      (APB_0_PWDATA          ),
  .extrnl_apb_prdata      (APB_0_PRDATA          ),
  .extrnl_apb_pready      (APB_0_PREADY          ),
  .extrnl_apb_pslverr     (APB_0_PSLVERR         ),

`ifdef SIMULATION_MODE
  .xsdb_apb_req           (1'b0                  ),
  .xsdb_apb_grant         (xsdb_apb_grant_0_s    ),
  .xsdb_apb_psel          (1'b0                  ),
  .xsdb_apb_pwrite        (1'b0                  ),
  .xsdb_apb_penable       (1'b0                  ),
  .xsdb_apb_paddr         (22'b0                 ),
  .xsdb_apb_pwdata        (32'b0                 ),
  .xsdb_apb_prdata        (xsdb_apb_prdata_0_s   ),
  .xsdb_apb_pready        (xsdb_apb_pready_0_s   ),
  .xsdb_apb_pslverr       (xsdb_apb_pslverr_0_s  ),
`else
  .xsdb_apb_req           (xsdb_apb_req_0_s      ),
  .xsdb_apb_grant         (xsdb_apb_grant_0_s    ),
  .xsdb_apb_psel          (xsdb_apb_psel_0_s     ),
  .xsdb_apb_pwrite        (xsdb_apb_pwrite_0_s   ),
  .xsdb_apb_penable       (xsdb_apb_penable_0_s  ),
  .xsdb_apb_paddr         (xsdb_apb_paddr_0_s    ),
  .xsdb_apb_pwdata        (xsdb_apb_pwdata_0_s   ),
  .xsdb_apb_prdata        (xsdb_apb_prdata_0_s   ),
  .xsdb_apb_pready        (xsdb_apb_pready_0_s   ),
  .xsdb_apb_pslverr       (xsdb_apb_pslverr_0_s  ),
`endif

  .temp_apb_req           (temp_apb_req_0_s      ),
  .temp_apb_grant         (temp_apb_grant_0_s    ),
  .temp_apb_psel          (temp_apb_psel_0_s     ),
  .temp_apb_pwrite        (temp_apb_pwrite_0_s   ),
  .temp_apb_penable       (temp_apb_penable_0_s  ),
  .temp_apb_paddr         (temp_apb_paddr_0_s    ),
  .temp_apb_pwdata        (temp_apb_pwdata_0_s   ),
  .temp_apb_prdata        (temp_apb_prdata_0_s   ),
  .temp_apb_pready        (temp_apb_pready_0_s   ),
  .temp_apb_pslverr       (temp_apb_pslverr_0_s  ),

  .psel                   (psel_0                ),
  .pwrite                 (pwrite_0              ),
  .penable                (penable_0             ),
  .paddr                  (paddr_0               ),
  .pwdata                 (pwdata_0              ),
  .prdata                 (prdata_0              ),
  .pready                 (pready_0              ),
  .pslverr                (pslverr_0             )
);

////////////////////////////////////////////////////////////////////////////////
// Driving out the APB interface for Monitor Shell for monitoring register
// write/read operations
////////////////////////////////////////////////////////////////////////////////
assign APB_0_PWDATA_MON  = pwdata_0 ;
assign APB_0_PADDR_MON   = paddr_0 ;
assign APB_0_PENABLE_MON = penable_0 ;
assign APB_0_PSEL_MON    = psel_0 ;
assign APB_0_PWRITE_MON  = pwrite_0 ;
assign APB_0_PRDATA_MON  = prdata_0 ;
assign APB_0_PREADY_MON  = pready_0 ;
assign APB_0_PSLVERR_MON = pslverr_0 ;

assign APB_1_PWDATA_MON  = 32'b0 ;
assign APB_1_PADDR_MON   = 22'b0 ;
assign APB_1_PENABLE_MON = 1'b0 ;
assign APB_1_PSEL_MON    = 1'b0 ;
assign APB_1_PWRITE_MON  = 1'b0 ;
assign APB_1_PRDATA_MON  = 32'b0 ;
assign APB_1_PREADY_MON  = 1'b0 ;
assign APB_1_PSLVERR_MON = 1'b0 ;

////////////////////////////////////////////////////////////////////////////////
// Instantiating Reset pulse generator:
// This is a workaround for the issue found in pileline register in SWITCH
// between tiles
////////////////////////////////////////////////////////////////////////////////
//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_00_rst_pulse_gen
//  (
//   .clk   (AXI_00_ACLK),
//   .rst_n (AXI_00_ARESET_N),
//   .pulse (AXI_00_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_01_rst_pulse_gen
//  (
//   .clk   (AXI_01_ACLK),
//   .rst_n (AXI_01_ARESET_N),
//   .pulse (AXI_01_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_02_rst_pulse_gen
//  (
//   .clk   (AXI_02_ACLK),
//   .rst_n (AXI_02_ARESET_N),
//   .pulse (AXI_02_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_03_rst_pulse_gen
//  (
//   .clk   (AXI_03_ACLK),
//   .rst_n (AXI_03_ARESET_N),
//   .pulse (AXI_03_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_04_rst_pulse_gen
//  (
//   .clk   (AXI_04_ACLK),
//   .rst_n (AXI_04_ARESET_N),
//   .pulse (AXI_04_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_05_rst_pulse_gen
//  (
//   .clk   (AXI_05_ACLK),
//   .rst_n (AXI_05_ARESET_N),
//   .pulse (AXI_05_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_06_rst_pulse_gen
//  (
//   .clk   (AXI_06_ACLK),
//   .rst_n (AXI_06_ARESET_N),
//   .pulse (AXI_06_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_07_rst_pulse_gen
//  (
//   .clk   (AXI_07_ACLK),
//   .rst_n (AXI_07_ARESET_N),
//   .pulse (AXI_07_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_08_rst_pulse_gen
//  (
//   .clk   (AXI_08_ACLK),
//   .rst_n (AXI_08_ARESET_N),
//   .pulse (AXI_08_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_09_rst_pulse_gen
//  (
//   .clk   (AXI_09_ACLK),
//   .rst_n (AXI_09_ARESET_N),
//   .pulse (AXI_09_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_10_rst_pulse_gen
//  (
//   .clk   (AXI_10_ACLK),
//   .rst_n (AXI_10_ARESET_N),
//   .pulse (AXI_10_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_11_rst_pulse_gen
//  (
//   .clk   (AXI_11_ACLK),
//   .rst_n (AXI_11_ARESET_N),
//   .pulse (AXI_11_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_12_rst_pulse_gen
//  (
//   .clk   (AXI_12_ACLK),
//   .rst_n (AXI_12_ARESET_N),
//   .pulse (AXI_12_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_13_rst_pulse_gen
//  (
//   .clk   (AXI_13_ACLK),
//   .rst_n (AXI_13_ARESET_N),
//   .pulse (AXI_13_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_14_rst_pulse_gen
//  (
//   .clk   (AXI_14_ACLK),
//   .rst_n (AXI_14_ARESET_N),
//   .pulse (AXI_14_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_15_rst_pulse_gen
//  (
//   .clk   (AXI_15_ACLK),
//   .rst_n (AXI_15_ARESET_N),
//   .pulse (AXI_15_RST_N)
//   );

////////////////////////////////////////////////////////////////////////////////
// Instantiating One stack HBM Unisim
////////////////////////////////////////////////////////////////////////////////
HBM_ONE_STACK_INTF  #(
  .STACK_LOCATION      (HBM_STACK_NUM),
  .CLK_SEL_00          (CLK_SEL_00),
  .CLK_SEL_01          (CLK_SEL_01),
  .CLK_SEL_02          (CLK_SEL_02),
  .CLK_SEL_03          (CLK_SEL_03),
  .CLK_SEL_04          (CLK_SEL_04),
  .CLK_SEL_05          (CLK_SEL_05),
  .CLK_SEL_06          (CLK_SEL_06),
  .CLK_SEL_07          (CLK_SEL_07),
  .CLK_SEL_08          (CLK_SEL_08),
  .CLK_SEL_09          (CLK_SEL_09),
  .CLK_SEL_10          (CLK_SEL_10),
  .CLK_SEL_11          (CLK_SEL_11),
  .CLK_SEL_12          (CLK_SEL_12),
  .CLK_SEL_13          (CLK_SEL_13),
  .CLK_SEL_14          (CLK_SEL_14),
  .CLK_SEL_15          (CLK_SEL_15),
  .MC_ENABLE_0         (MC_ENABLE_00),
  .MC_ENABLE_1         (MC_ENABLE_01),
  .MC_ENABLE_2         (MC_ENABLE_02),
  .MC_ENABLE_3         (MC_ENABLE_03),
  .MC_ENABLE_4         (MC_ENABLE_04),
  .MC_ENABLE_5         (MC_ENABLE_05),
  .MC_ENABLE_6         (MC_ENABLE_06),
  .MC_ENABLE_7         (MC_ENABLE_07),
  .MC_ENABLE_APB       (MC_ENABLE_APB_00),
  .PHY_ENABLE_00       (PHY_ENABLE_00),
  .PHY_ENABLE_01       (PHY_ENABLE_01),
  .PHY_ENABLE_02       (PHY_ENABLE_02),
  .PHY_ENABLE_03       (PHY_ENABLE_03),
  .PHY_ENABLE_04       (PHY_ENABLE_04),
  .PHY_ENABLE_05       (PHY_ENABLE_05),
  .PHY_ENABLE_06       (PHY_ENABLE_06),
  .PHY_ENABLE_07       (PHY_ENABLE_07),
  .PHY_ENABLE_08       (PHY_ENABLE_08),
  .PHY_ENABLE_09       (PHY_ENABLE_09),
  .PHY_ENABLE_10       (PHY_ENABLE_10),
  .PHY_ENABLE_11       (PHY_ENABLE_11),
  .PHY_ENABLE_12       (PHY_ENABLE_12),
  .PHY_ENABLE_13       (PHY_ENABLE_13),
  .PHY_ENABLE_14       (PHY_ENABLE_14),
  .PHY_ENABLE_15       (PHY_ENABLE_15),
  .PHY_ENABLE_APB      (PHY_ENABLE_APB_00),
  .DATARATE_00         (DATARATE_STACK_0),
  .DATARATE_01         (DATARATE_STACK_0),
  .DATARATE_02         (DATARATE_STACK_0),
  .DATARATE_03         (DATARATE_STACK_0),
  .DATARATE_04         (DATARATE_STACK_0),
  .DATARATE_05         (DATARATE_STACK_0),
  .DATARATE_06         (DATARATE_STACK_0),
  .DATARATE_07         (DATARATE_STACK_0),
  .READ_PERCENT_00     (READ_PERCENT_00),
  .READ_PERCENT_01     (READ_PERCENT_01),
  .READ_PERCENT_02     (READ_PERCENT_02),
  .READ_PERCENT_03     (READ_PERCENT_03),
  .READ_PERCENT_04     (READ_PERCENT_04),
  .READ_PERCENT_05     (READ_PERCENT_05),
  .READ_PERCENT_06     (READ_PERCENT_06),
  .READ_PERCENT_07     (READ_PERCENT_07),
  .READ_PERCENT_08     (READ_PERCENT_08),
  .READ_PERCENT_09     (READ_PERCENT_09),
  .READ_PERCENT_10     (READ_PERCENT_10),
  .READ_PERCENT_11     (READ_PERCENT_11),
  .READ_PERCENT_12     (READ_PERCENT_12),
  .READ_PERCENT_13     (READ_PERCENT_13),
  .READ_PERCENT_14     (READ_PERCENT_14),
  .READ_PERCENT_15     (READ_PERCENT_15),
  .WRITE_PERCENT_00    (WRITE_PERCENT_00),
  .WRITE_PERCENT_01    (WRITE_PERCENT_01),
  .WRITE_PERCENT_02    (WRITE_PERCENT_02),
  .WRITE_PERCENT_03    (WRITE_PERCENT_03),
  .WRITE_PERCENT_04    (WRITE_PERCENT_04),
  .WRITE_PERCENT_05    (WRITE_PERCENT_05),
  .WRITE_PERCENT_06    (WRITE_PERCENT_06),
  .WRITE_PERCENT_07    (WRITE_PERCENT_07),
  .WRITE_PERCENT_08    (WRITE_PERCENT_08),
  .WRITE_PERCENT_09    (WRITE_PERCENT_09),
  .WRITE_PERCENT_10    (WRITE_PERCENT_10),
  .WRITE_PERCENT_11    (WRITE_PERCENT_11),
  .WRITE_PERCENT_12    (WRITE_PERCENT_12),
  .WRITE_PERCENT_13    (WRITE_PERCENT_13),
  .WRITE_PERCENT_14    (WRITE_PERCENT_14),
  .WRITE_PERCENT_15    (WRITE_PERCENT_15),
  .PAGEHIT_PERCENT_00  (PAGEHIT_PERCENT_00),
  .SWITCH_ENABLE       (SWITCH_ENABLE_00)
) hbm_one_stack_intf (
  //Outputs
  .AXI_00_ARREADY(AXI_00_ARREADY),
  .AXI_00_AWREADY(AXI_00_AWREADY),
  .AXI_00_RDATA_PARITY(AXI_00_RDATA_PARITY),
  .AXI_00_RDATA(AXI_00_RDATA),
  .AXI_00_RID(AXI_00_RID),
  .AXI_00_RLAST(AXI_00_RLAST),
  .AXI_00_RRESP(AXI_00_RRESP),
  .AXI_00_RVALID(AXI_00_RVALID),
  .AXI_00_WREADY(AXI_00_WREADY),
  .AXI_00_BID(AXI_00_BID),
  .AXI_00_BRESP(AXI_00_BRESP),
  .AXI_00_BVALID(AXI_00_BVALID),
  .AXI_00_DFI_AW_AERR_N(AXI_00_DFI_AW_AERR_N),
  .AXI_00_DFI_DBI_BYTE_DISABLE(AXI_00_DFI_DBI_BYTE_DISABLE),
  .AXI_00_DFI_DW_RDDATA_DBI(AXI_00_DFI_DW_RDDATA_DBI),
  .AXI_00_DFI_DW_RDDATA_DERR(AXI_00_DFI_DW_RDDATA_DERR),
  .AXI_00_DFI_DW_RDDATA_VALID(AXI_00_DFI_DW_RDDATA_VALID),
  .AXI_00_DFI_INIT_COMPLETE(AXI_00_DFI_INIT_COMPLETE),
  .AXI_00_DFI_PHY_LP_STATE(AXI_00_DFI_PHY_LP_STATE),
  .AXI_00_DFI_PHYUPD_REQ(AXI_00_DFI_PHYUPD_REQ),
  .AXI_00_DFI_CLK_BUF(AXI_00_DFI_CLK_BUF),
  .AXI_00_DFI_RST_N_BUF(AXI_00_DFI_RST_N_BUF),
  .AXI_00_MC_STATUS(AXI_00_MC_STATUS),
  .AXI_00_PHY_STATUS(AXI_00_PHY_STATUS),
  .AXI_01_ARREADY(AXI_01_ARREADY),
  .AXI_01_AWREADY(AXI_01_AWREADY),
  .AXI_01_RDATA_PARITY(AXI_01_RDATA_PARITY),
  .AXI_01_RDATA(AXI_01_RDATA),
  .AXI_01_RID(AXI_01_RID),
  .AXI_01_RLAST(AXI_01_RLAST),
  .AXI_01_RRESP(AXI_01_RRESP),
  .AXI_01_RVALID(AXI_01_RVALID),
  .AXI_01_WREADY(AXI_01_WREADY),
  .AXI_01_BID(AXI_01_BID),
  .AXI_01_BRESP(AXI_01_BRESP),
  .AXI_01_BVALID(AXI_01_BVALID),
  .AXI_01_DFI_AW_AERR_N(AXI_01_DFI_AW_AERR_N),
  .AXI_01_DFI_DBI_BYTE_DISABLE(AXI_01_DFI_DBI_BYTE_DISABLE),
  .AXI_01_DFI_DW_RDDATA_DBI(AXI_01_DFI_DW_RDDATA_DBI),
  .AXI_01_DFI_DW_RDDATA_DERR(AXI_01_DFI_DW_RDDATA_DERR),
  .AXI_01_DFI_DW_RDDATA_VALID(AXI_01_DFI_DW_RDDATA_VALID),
  .AXI_01_DFI_INIT_COMPLETE(AXI_01_DFI_INIT_COMPLETE),
  .AXI_01_DFI_PHY_LP_STATE(AXI_01_DFI_PHY_LP_STATE),
  .AXI_01_DFI_PHYUPD_REQ(AXI_01_DFI_PHYUPD_REQ),
  .AXI_01_DFI_CLK_BUF(AXI_01_DFI_CLK_BUF),
  .AXI_01_DFI_RST_N_BUF(AXI_01_DFI_RST_N_BUF),
  .AXI_02_ARREADY(AXI_02_ARREADY),
  .AXI_02_AWREADY(AXI_02_AWREADY),
  .AXI_02_RDATA_PARITY(AXI_02_RDATA_PARITY),
  .AXI_02_RDATA(AXI_02_RDATA),
  .AXI_02_RID(AXI_02_RID),
  .AXI_02_RLAST(AXI_02_RLAST),
  .AXI_02_RRESP(AXI_02_RRESP),
  .AXI_02_RVALID(AXI_02_RVALID),
  .AXI_02_WREADY(AXI_02_WREADY),
  .AXI_02_BID(AXI_02_BID),
  .AXI_02_BRESP(AXI_02_BRESP),
  .AXI_02_BVALID(AXI_02_BVALID),
  .AXI_02_DFI_AW_AERR_N(AXI_02_DFI_AW_AERR_N),
  .AXI_02_DFI_DBI_BYTE_DISABLE(AXI_02_DFI_DBI_BYTE_DISABLE),
  .AXI_02_DFI_DW_RDDATA_DBI(AXI_02_DFI_DW_RDDATA_DBI),
  .AXI_02_DFI_DW_RDDATA_DERR(AXI_02_DFI_DW_RDDATA_DERR),
  .AXI_02_DFI_DW_RDDATA_VALID(AXI_02_DFI_DW_RDDATA_VALID),
  .AXI_02_DFI_INIT_COMPLETE(AXI_02_DFI_INIT_COMPLETE),
  .AXI_02_DFI_PHY_LP_STATE(AXI_02_DFI_PHY_LP_STATE),
  .AXI_02_DFI_PHYUPD_REQ(AXI_02_DFI_PHYUPD_REQ),
  .AXI_02_DFI_CLK_BUF(AXI_02_DFI_CLK_BUF),
  .AXI_02_DFI_RST_N_BUF(AXI_02_DFI_RST_N_BUF),
  .AXI_02_MC_STATUS(AXI_02_MC_STATUS),
  .AXI_02_PHY_STATUS(AXI_02_PHY_STATUS),
  .AXI_03_ARREADY(AXI_03_ARREADY),
  .AXI_03_AWREADY(AXI_03_AWREADY),
  .AXI_03_RDATA_PARITY(AXI_03_RDATA_PARITY),
  .AXI_03_RDATA(AXI_03_RDATA),
  .AXI_03_RID(AXI_03_RID),
  .AXI_03_RLAST(AXI_03_RLAST),
  .AXI_03_RRESP(AXI_03_RRESP),
  .AXI_03_RVALID(AXI_03_RVALID),
  .AXI_03_WREADY(AXI_03_WREADY),
  .AXI_03_BID(AXI_03_BID),
  .AXI_03_BRESP(AXI_03_BRESP),
  .AXI_03_BVALID(AXI_03_BVALID),
  .AXI_03_DFI_AW_AERR_N(AXI_03_DFI_AW_AERR_N),
  .AXI_03_DFI_DBI_BYTE_DISABLE(AXI_03_DFI_DBI_BYTE_DISABLE),
  .AXI_03_DFI_DW_RDDATA_DBI(AXI_03_DFI_DW_RDDATA_DBI),
  .AXI_03_DFI_DW_RDDATA_DERR(AXI_03_DFI_DW_RDDATA_DERR),
  .AXI_03_DFI_DW_RDDATA_VALID(AXI_03_DFI_DW_RDDATA_VALID),
  .AXI_03_DFI_INIT_COMPLETE(AXI_03_DFI_INIT_COMPLETE),
  .AXI_03_DFI_PHY_LP_STATE(AXI_03_DFI_PHY_LP_STATE),
  .AXI_03_DFI_PHYUPD_REQ(AXI_03_DFI_PHYUPD_REQ),
  .AXI_03_DFI_CLK_BUF(AXI_03_DFI_CLK_BUF),
  .AXI_03_DFI_RST_N_BUF(AXI_03_DFI_RST_N_BUF),
  .AXI_04_ARREADY(AXI_04_ARREADY),
  .AXI_04_AWREADY(AXI_04_AWREADY),
  .AXI_04_RDATA_PARITY(AXI_04_RDATA_PARITY),
  .AXI_04_RDATA(AXI_04_RDATA),
  .AXI_04_RID(AXI_04_RID),
  .AXI_04_RLAST(AXI_04_RLAST),
  .AXI_04_RRESP(AXI_04_RRESP),
  .AXI_04_RVALID(AXI_04_RVALID),
  .AXI_04_WREADY(AXI_04_WREADY),
  .AXI_04_BID(AXI_04_BID),
  .AXI_04_BRESP(AXI_04_BRESP),
  .AXI_04_BVALID(AXI_04_BVALID),
  .AXI_04_DFI_AW_AERR_N(AXI_04_DFI_AW_AERR_N),
  .AXI_04_DFI_DBI_BYTE_DISABLE(AXI_04_DFI_DBI_BYTE_DISABLE),
  .AXI_04_DFI_DW_RDDATA_DBI(AXI_04_DFI_DW_RDDATA_DBI),
  .AXI_04_DFI_DW_RDDATA_DERR(AXI_04_DFI_DW_RDDATA_DERR),
  .AXI_04_DFI_DW_RDDATA_VALID(AXI_04_DFI_DW_RDDATA_VALID),
  .AXI_04_DFI_INIT_COMPLETE(AXI_04_DFI_INIT_COMPLETE),
  .AXI_04_DFI_PHY_LP_STATE(AXI_04_DFI_PHY_LP_STATE),
  .AXI_04_DFI_PHYUPD_REQ(AXI_04_DFI_PHYUPD_REQ),
  .AXI_04_DFI_CLK_BUF(AXI_04_DFI_CLK_BUF),
  .AXI_04_DFI_RST_N_BUF(AXI_04_DFI_RST_N_BUF),
  .AXI_04_MC_STATUS(AXI_04_MC_STATUS),
  .AXI_04_PHY_STATUS(AXI_04_PHY_STATUS),
  .AXI_05_ARREADY(AXI_05_ARREADY),
  .AXI_05_AWREADY(AXI_05_AWREADY),
  .AXI_05_RDATA_PARITY(AXI_05_RDATA_PARITY),
  .AXI_05_RDATA(AXI_05_RDATA),
  .AXI_05_RID(AXI_05_RID),
  .AXI_05_RLAST(AXI_05_RLAST),
  .AXI_05_RRESP(AXI_05_RRESP),
  .AXI_05_RVALID(AXI_05_RVALID),
  .AXI_05_WREADY(AXI_05_WREADY),
  .AXI_05_BID(AXI_05_BID),
  .AXI_05_BRESP(AXI_05_BRESP),
  .AXI_05_BVALID(AXI_05_BVALID),
  .AXI_05_DFI_AW_AERR_N(AXI_05_DFI_AW_AERR_N),
  .AXI_05_DFI_DBI_BYTE_DISABLE(AXI_05_DFI_DBI_BYTE_DISABLE),
  .AXI_05_DFI_DW_RDDATA_DBI(AXI_05_DFI_DW_RDDATA_DBI),
  .AXI_05_DFI_DW_RDDATA_DERR(AXI_05_DFI_DW_RDDATA_DERR),
  .AXI_05_DFI_DW_RDDATA_VALID(AXI_05_DFI_DW_RDDATA_VALID),
  .AXI_05_DFI_INIT_COMPLETE(AXI_05_DFI_INIT_COMPLETE),
  .AXI_05_DFI_PHY_LP_STATE(AXI_05_DFI_PHY_LP_STATE),
  .AXI_05_DFI_PHYUPD_REQ(AXI_05_DFI_PHYUPD_REQ),
  .AXI_05_DFI_CLK_BUF(AXI_05_DFI_CLK_BUF),
  .AXI_05_DFI_RST_N_BUF(AXI_05_DFI_RST_N_BUF),
  .AXI_06_ARREADY(AXI_06_ARREADY),
  .AXI_06_AWREADY(AXI_06_AWREADY),
  .AXI_06_RDATA_PARITY(AXI_06_RDATA_PARITY),
  .AXI_06_RDATA(AXI_06_RDATA),
  .AXI_06_RID(AXI_06_RID),
  .AXI_06_RLAST(AXI_06_RLAST),
  .AXI_06_RRESP(AXI_06_RRESP),
  .AXI_06_RVALID(AXI_06_RVALID),
  .AXI_06_WREADY(AXI_06_WREADY),
  .AXI_06_BID(AXI_06_BID),
  .AXI_06_BRESP(AXI_06_BRESP),
  .AXI_06_BVALID(AXI_06_BVALID),
  .AXI_06_DFI_AW_AERR_N(AXI_06_DFI_AW_AERR_N),
  .AXI_06_DFI_DBI_BYTE_DISABLE(AXI_06_DFI_DBI_BYTE_DISABLE),
  .AXI_06_DFI_DW_RDDATA_DBI(AXI_06_DFI_DW_RDDATA_DBI),
  .AXI_06_DFI_DW_RDDATA_DERR(AXI_06_DFI_DW_RDDATA_DERR),
  .AXI_06_DFI_DW_RDDATA_VALID(AXI_06_DFI_DW_RDDATA_VALID),
  .AXI_06_DFI_INIT_COMPLETE(AXI_06_DFI_INIT_COMPLETE),
  .AXI_06_DFI_PHY_LP_STATE(AXI_06_DFI_PHY_LP_STATE),
  .AXI_06_DFI_PHYUPD_REQ(AXI_06_DFI_PHYUPD_REQ),
  .AXI_06_DFI_CLK_BUF(AXI_06_DFI_CLK_BUF),
  .AXI_06_DFI_RST_N_BUF(AXI_06_DFI_RST_N_BUF),
  .AXI_06_MC_STATUS(AXI_06_MC_STATUS),
  .AXI_06_PHY_STATUS(AXI_06_PHY_STATUS),
  .AXI_07_ARREADY(AXI_07_ARREADY),
  .AXI_07_AWREADY(AXI_07_AWREADY),
  .AXI_07_RDATA_PARITY(AXI_07_RDATA_PARITY),
  .AXI_07_RDATA(AXI_07_RDATA),
  .AXI_07_RID(AXI_07_RID),
  .AXI_07_RLAST(AXI_07_RLAST),
  .AXI_07_RRESP(AXI_07_RRESP),
  .AXI_07_RVALID(AXI_07_RVALID),
  .AXI_07_WREADY(AXI_07_WREADY),
  .AXI_07_BID(AXI_07_BID),
  .AXI_07_BRESP(AXI_07_BRESP),
  .AXI_07_BVALID(AXI_07_BVALID),
  .AXI_07_DFI_AW_AERR_N(AXI_07_DFI_AW_AERR_N),
  .AXI_07_DFI_DBI_BYTE_DISABLE(AXI_07_DFI_DBI_BYTE_DISABLE),
  .AXI_07_DFI_DW_RDDATA_DBI(AXI_07_DFI_DW_RDDATA_DBI),
  .AXI_07_DFI_DW_RDDATA_DERR(AXI_07_DFI_DW_RDDATA_DERR),
  .AXI_07_DFI_DW_RDDATA_VALID(AXI_07_DFI_DW_RDDATA_VALID),
  .AXI_07_DFI_INIT_COMPLETE(AXI_07_DFI_INIT_COMPLETE),
  .AXI_07_DFI_PHY_LP_STATE(AXI_07_DFI_PHY_LP_STATE),
  .AXI_07_DFI_PHYUPD_REQ(AXI_07_DFI_PHYUPD_REQ),
  .AXI_07_DFI_CLK_BUF(AXI_07_DFI_CLK_BUF),
  .AXI_07_DFI_RST_N_BUF(AXI_07_DFI_RST_N_BUF),
  .AXI_08_ARREADY(AXI_08_ARREADY),
  .AXI_08_AWREADY(AXI_08_AWREADY),
  .AXI_08_RDATA_PARITY(AXI_08_RDATA_PARITY),
  .AXI_08_RDATA(AXI_08_RDATA),
  .AXI_08_RID(AXI_08_RID),
  .AXI_08_RLAST(AXI_08_RLAST),
  .AXI_08_RRESP(AXI_08_RRESP),
  .AXI_08_RVALID(AXI_08_RVALID),
  .AXI_08_WREADY(AXI_08_WREADY),
  .AXI_08_BID(AXI_08_BID),
  .AXI_08_BRESP(AXI_08_BRESP),
  .AXI_08_BVALID(AXI_08_BVALID),
  .AXI_08_DFI_AW_AERR_N(AXI_08_DFI_AW_AERR_N),
  .AXI_08_DFI_DBI_BYTE_DISABLE(AXI_08_DFI_DBI_BYTE_DISABLE),
  .AXI_08_DFI_DW_RDDATA_DBI(AXI_08_DFI_DW_RDDATA_DBI),
  .AXI_08_DFI_DW_RDDATA_DERR(AXI_08_DFI_DW_RDDATA_DERR),
  .AXI_08_DFI_DW_RDDATA_VALID(AXI_08_DFI_DW_RDDATA_VALID),
  .AXI_08_DFI_INIT_COMPLETE(AXI_08_DFI_INIT_COMPLETE),
  .AXI_08_DFI_PHY_LP_STATE(AXI_08_DFI_PHY_LP_STATE),
  .AXI_08_DFI_PHYUPD_REQ(AXI_08_DFI_PHYUPD_REQ),
  .AXI_08_DFI_CLK_BUF(AXI_08_DFI_CLK_BUF),
  .AXI_08_DFI_RST_N_BUF(AXI_08_DFI_RST_N_BUF),
  .AXI_08_MC_STATUS(AXI_08_MC_STATUS),
  .AXI_08_PHY_STATUS(AXI_08_PHY_STATUS),
  .AXI_09_ARREADY(AXI_09_ARREADY),
  .AXI_09_AWREADY(AXI_09_AWREADY),
  .AXI_09_RDATA_PARITY(AXI_09_RDATA_PARITY),
  .AXI_09_RDATA(AXI_09_RDATA),
  .AXI_09_RID(AXI_09_RID),
  .AXI_09_RLAST(AXI_09_RLAST),
  .AXI_09_RRESP(AXI_09_RRESP),
  .AXI_09_RVALID(AXI_09_RVALID),
  .AXI_09_WREADY(AXI_09_WREADY),
  .AXI_09_BID(AXI_09_BID),
  .AXI_09_BRESP(AXI_09_BRESP),
  .AXI_09_BVALID(AXI_09_BVALID),
  .AXI_09_DFI_AW_AERR_N(AXI_09_DFI_AW_AERR_N),
  .AXI_09_DFI_DBI_BYTE_DISABLE(AXI_09_DFI_DBI_BYTE_DISABLE),
  .AXI_09_DFI_DW_RDDATA_DBI(AXI_09_DFI_DW_RDDATA_DBI),
  .AXI_09_DFI_DW_RDDATA_DERR(AXI_09_DFI_DW_RDDATA_DERR),
  .AXI_09_DFI_DW_RDDATA_VALID(AXI_09_DFI_DW_RDDATA_VALID),
  .AXI_09_DFI_INIT_COMPLETE(AXI_09_DFI_INIT_COMPLETE),
  .AXI_09_DFI_PHY_LP_STATE(AXI_09_DFI_PHY_LP_STATE),
  .AXI_09_DFI_PHYUPD_REQ(AXI_09_DFI_PHYUPD_REQ),
  .AXI_09_DFI_CLK_BUF(AXI_09_DFI_CLK_BUF),
  .AXI_09_DFI_RST_N_BUF(AXI_09_DFI_RST_N_BUF),
  .AXI_10_ARREADY(AXI_10_ARREADY),
  .AXI_10_AWREADY(AXI_10_AWREADY),
  .AXI_10_RDATA_PARITY(AXI_10_RDATA_PARITY),
  .AXI_10_RDATA(AXI_10_RDATA),
  .AXI_10_RID(AXI_10_RID),
  .AXI_10_RLAST(AXI_10_RLAST),
  .AXI_10_RRESP(AXI_10_RRESP),
  .AXI_10_RVALID(AXI_10_RVALID),
  .AXI_10_WREADY(AXI_10_WREADY),
  .AXI_10_BID(AXI_10_BID),
  .AXI_10_BRESP(AXI_10_BRESP),
  .AXI_10_BVALID(AXI_10_BVALID),
  .AXI_10_DFI_AW_AERR_N(AXI_10_DFI_AW_AERR_N),
  .AXI_10_DFI_DBI_BYTE_DISABLE(AXI_10_DFI_DBI_BYTE_DISABLE),
  .AXI_10_DFI_DW_RDDATA_DBI(AXI_10_DFI_DW_RDDATA_DBI),
  .AXI_10_DFI_DW_RDDATA_DERR(AXI_10_DFI_DW_RDDATA_DERR),
  .AXI_10_DFI_DW_RDDATA_VALID(AXI_10_DFI_DW_RDDATA_VALID),
  .AXI_10_DFI_INIT_COMPLETE(AXI_10_DFI_INIT_COMPLETE),
  .AXI_10_DFI_PHY_LP_STATE(AXI_10_DFI_PHY_LP_STATE),
  .AXI_10_DFI_PHYUPD_REQ(AXI_10_DFI_PHYUPD_REQ),
  .AXI_10_DFI_CLK_BUF(AXI_10_DFI_CLK_BUF),
  .AXI_10_DFI_RST_N_BUF(AXI_10_DFI_RST_N_BUF),
  .AXI_10_MC_STATUS(AXI_10_MC_STATUS),
  .AXI_10_PHY_STATUS(AXI_10_PHY_STATUS),
  .AXI_11_ARREADY(AXI_11_ARREADY),
  .AXI_11_AWREADY(AXI_11_AWREADY),
  .AXI_11_RDATA_PARITY(AXI_11_RDATA_PARITY),
  .AXI_11_RDATA(AXI_11_RDATA),
  .AXI_11_RID(AXI_11_RID),
  .AXI_11_RLAST(AXI_11_RLAST),
  .AXI_11_RRESP(AXI_11_RRESP),
  .AXI_11_RVALID(AXI_11_RVALID),
  .AXI_11_WREADY(AXI_11_WREADY),
  .AXI_11_BID(AXI_11_BID),
  .AXI_11_BRESP(AXI_11_BRESP),
  .AXI_11_BVALID(AXI_11_BVALID),
  .AXI_11_DFI_AW_AERR_N(AXI_11_DFI_AW_AERR_N),
  .AXI_11_DFI_DBI_BYTE_DISABLE(AXI_11_DFI_DBI_BYTE_DISABLE),
  .AXI_11_DFI_DW_RDDATA_DBI(AXI_11_DFI_DW_RDDATA_DBI),
  .AXI_11_DFI_DW_RDDATA_DERR(AXI_11_DFI_DW_RDDATA_DERR),
  .AXI_11_DFI_DW_RDDATA_VALID(AXI_11_DFI_DW_RDDATA_VALID),
  .AXI_11_DFI_INIT_COMPLETE(AXI_11_DFI_INIT_COMPLETE),
  .AXI_11_DFI_PHY_LP_STATE(AXI_11_DFI_PHY_LP_STATE),
  .AXI_11_DFI_PHYUPD_REQ(AXI_11_DFI_PHYUPD_REQ),
  .AXI_11_DFI_CLK_BUF(AXI_11_DFI_CLK_BUF),
  .AXI_11_DFI_RST_N_BUF(AXI_11_DFI_RST_N_BUF),
  .AXI_12_ARREADY(AXI_12_ARREADY),
  .AXI_12_AWREADY(AXI_12_AWREADY),
  .AXI_12_RDATA_PARITY(AXI_12_RDATA_PARITY),
  .AXI_12_RDATA(AXI_12_RDATA),
  .AXI_12_RID(AXI_12_RID),
  .AXI_12_RLAST(AXI_12_RLAST),
  .AXI_12_RRESP(AXI_12_RRESP),
  .AXI_12_RVALID(AXI_12_RVALID),
  .AXI_12_WREADY(AXI_12_WREADY),
  .AXI_12_BID(AXI_12_BID),
  .AXI_12_BRESP(AXI_12_BRESP),
  .AXI_12_BVALID(AXI_12_BVALID),
  .AXI_12_DFI_AW_AERR_N(AXI_12_DFI_AW_AERR_N),
  .AXI_12_DFI_DBI_BYTE_DISABLE(AXI_12_DFI_DBI_BYTE_DISABLE),
  .AXI_12_DFI_DW_RDDATA_DBI(AXI_12_DFI_DW_RDDATA_DBI),
  .AXI_12_DFI_DW_RDDATA_DERR(AXI_12_DFI_DW_RDDATA_DERR),
  .AXI_12_DFI_DW_RDDATA_VALID(AXI_12_DFI_DW_RDDATA_VALID),
  .AXI_12_DFI_INIT_COMPLETE(AXI_12_DFI_INIT_COMPLETE),
  .AXI_12_DFI_PHY_LP_STATE(AXI_12_DFI_PHY_LP_STATE),
  .AXI_12_DFI_PHYUPD_REQ(AXI_12_DFI_PHYUPD_REQ),
  .AXI_12_DFI_CLK_BUF(AXI_12_DFI_CLK_BUF),
  .AXI_12_DFI_RST_N_BUF(AXI_12_DFI_RST_N_BUF),
  .AXI_12_MC_STATUS(AXI_12_MC_STATUS),
  .AXI_12_PHY_STATUS(AXI_12_PHY_STATUS),
  .AXI_13_ARREADY(AXI_13_ARREADY),
  .AXI_13_AWREADY(AXI_13_AWREADY),
  .AXI_13_RDATA_PARITY(AXI_13_RDATA_PARITY),
  .AXI_13_RDATA(AXI_13_RDATA),
  .AXI_13_RID(AXI_13_RID),
  .AXI_13_RLAST(AXI_13_RLAST),
  .AXI_13_RRESP(AXI_13_RRESP),
  .AXI_13_RVALID(AXI_13_RVALID),
  .AXI_13_WREADY(AXI_13_WREADY),
  .AXI_13_BID(AXI_13_BID),
  .AXI_13_BRESP(AXI_13_BRESP),
  .AXI_13_BVALID(AXI_13_BVALID),
  .AXI_13_DFI_AW_AERR_N(AXI_13_DFI_AW_AERR_N),
  .AXI_13_DFI_DBI_BYTE_DISABLE(AXI_13_DFI_DBI_BYTE_DISABLE),
  .AXI_13_DFI_DW_RDDATA_DBI(AXI_13_DFI_DW_RDDATA_DBI),
  .AXI_13_DFI_DW_RDDATA_DERR(AXI_13_DFI_DW_RDDATA_DERR),
  .AXI_13_DFI_DW_RDDATA_VALID(AXI_13_DFI_DW_RDDATA_VALID),
  .AXI_13_DFI_INIT_COMPLETE(AXI_13_DFI_INIT_COMPLETE),
  .AXI_13_DFI_PHY_LP_STATE(AXI_13_DFI_PHY_LP_STATE),
  .AXI_13_DFI_PHYUPD_REQ(AXI_13_DFI_PHYUPD_REQ),
  .AXI_13_DFI_CLK_BUF(AXI_13_DFI_CLK_BUF),
  .AXI_13_DFI_RST_N_BUF(AXI_13_DFI_RST_N_BUF),
  .AXI_14_ARREADY(AXI_14_ARREADY),
  .AXI_14_AWREADY(AXI_14_AWREADY),
  .AXI_14_RDATA_PARITY(AXI_14_RDATA_PARITY),
  .AXI_14_RDATA(AXI_14_RDATA),
  .AXI_14_RID(AXI_14_RID),
  .AXI_14_RLAST(AXI_14_RLAST),
  .AXI_14_RRESP(AXI_14_RRESP),
  .AXI_14_RVALID(AXI_14_RVALID),
  .AXI_14_WREADY(AXI_14_WREADY),
  .AXI_14_BID(AXI_14_BID),
  .AXI_14_BRESP(AXI_14_BRESP),
  .AXI_14_BVALID(AXI_14_BVALID),
  .AXI_14_DFI_AW_AERR_N(AXI_14_DFI_AW_AERR_N),
  .AXI_14_DFI_DBI_BYTE_DISABLE(AXI_14_DFI_DBI_BYTE_DISABLE),
  .AXI_14_DFI_DW_RDDATA_DBI(AXI_14_DFI_DW_RDDATA_DBI),
  .AXI_14_DFI_DW_RDDATA_DERR(AXI_14_DFI_DW_RDDATA_DERR),
  .AXI_14_DFI_DW_RDDATA_VALID(AXI_14_DFI_DW_RDDATA_VALID),
  .AXI_14_DFI_INIT_COMPLETE(AXI_14_DFI_INIT_COMPLETE),
  .AXI_14_DFI_PHY_LP_STATE(AXI_14_DFI_PHY_LP_STATE),
  .AXI_14_DFI_PHYUPD_REQ(AXI_14_DFI_PHYUPD_REQ),
  .AXI_14_DFI_CLK_BUF(AXI_14_DFI_CLK_BUF),
  .AXI_14_DFI_RST_N_BUF(AXI_14_DFI_RST_N_BUF),
  .AXI_14_MC_STATUS(AXI_14_MC_STATUS),
  .AXI_14_PHY_STATUS(AXI_14_PHY_STATUS),
  .AXI_15_ARREADY(AXI_15_ARREADY),
  .AXI_15_AWREADY(AXI_15_AWREADY),
  .AXI_15_RDATA_PARITY(AXI_15_RDATA_PARITY),
  .AXI_15_RDATA(AXI_15_RDATA),
  .AXI_15_RID(AXI_15_RID),
  .AXI_15_RLAST(AXI_15_RLAST),
  .AXI_15_RRESP(AXI_15_RRESP),
  .AXI_15_RVALID(AXI_15_RVALID),
  .AXI_15_WREADY(AXI_15_WREADY),
  .AXI_15_BID(AXI_15_BID),
  .AXI_15_BRESP(AXI_15_BRESP),
  .AXI_15_BVALID(AXI_15_BVALID),
  .AXI_15_DFI_AW_AERR_N(AXI_15_DFI_AW_AERR_N),
  .AXI_15_DFI_DBI_BYTE_DISABLE(AXI_15_DFI_DBI_BYTE_DISABLE),
  .AXI_15_DFI_DW_RDDATA_DBI(AXI_15_DFI_DW_RDDATA_DBI),
  .AXI_15_DFI_DW_RDDATA_DERR(AXI_15_DFI_DW_RDDATA_DERR),
  .AXI_15_DFI_DW_RDDATA_VALID(AXI_15_DFI_DW_RDDATA_VALID),
  .AXI_15_DFI_INIT_COMPLETE(AXI_15_DFI_INIT_COMPLETE),
  .AXI_15_DFI_PHY_LP_STATE(AXI_15_DFI_PHY_LP_STATE),
  .AXI_15_DFI_PHYUPD_REQ(AXI_15_DFI_PHYUPD_REQ),
  .AXI_15_DFI_CLK_BUF(AXI_15_DFI_CLK_BUF),
  .AXI_15_DFI_RST_N_BUF(AXI_15_DFI_RST_N_BUF),
  .APB_0_PRDATA(prdata_0),
  .APB_0_PREADY(pready_0),
  .APB_0_PSLVERR(pslverr_0),
  .DRAM_0_STAT_CATTRIP(DRAM_0_STAT_CATTRIP),
  .DRAM_0_STAT_TEMP(DRAM_0_STAT_TEMP),
  // Inputs
  .HBM_REF_CLK(HBM_REF_CLK_0),
  .AXI_00_ACLK(AXI_00_ACLK),
  .AXI_00_ARESET_N(AXI_00_ARESET_N),
  .AXI_00_ARADDR(AXI_00_ARADDR),
  .AXI_00_ARBURST(AXI_00_ARBURST),
  .AXI_00_ARID(AXI_00_ARID),
  .AXI_00_ARLEN(AXI_00_ARLEN[3:0]),
  .AXI_00_ARSIZE(AXI_00_ARSIZE),
  .AXI_00_ARVALID(AXI_00_ARVALID),
  .AXI_00_AWADDR(AXI_00_AWADDR),
  .AXI_00_AWBURST(AXI_00_AWBURST),
  .AXI_00_AWID(AXI_00_AWID),
  .AXI_00_AWLEN(AXI_00_AWLEN[3:0]),
  .AXI_00_AWSIZE(AXI_00_AWSIZE),
  .AXI_00_AWVALID(AXI_00_AWVALID),
  .AXI_00_RREADY(rready_00),
  .AXI_00_BREADY(bready_00),
  .AXI_00_WDATA(AXI_00_WDATA),
  .AXI_00_WLAST(AXI_00_WLAST),
  .AXI_00_WSTRB(AXI_00_WSTRB),
  .AXI_00_WDATA_PARITY(AXI_00_WDATA_PARITY),
  .AXI_00_WVALID(AXI_00_WVALID),
  //.AXI_00_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_00_DFI_LP_PWR_X_REQ(AXI_00_DFI_LP_PWR_X_REQ),
  .AXI_01_ACLK(AXI_01_ACLK),
  .AXI_01_ARESET_N(AXI_01_ARESET_N),
  .AXI_01_ARADDR(AXI_01_ARADDR),
  .AXI_01_ARBURST(AXI_01_ARBURST),
  .AXI_01_ARID(AXI_01_ARID),
  .AXI_01_ARLEN(AXI_01_ARLEN[3:0]),
  .AXI_01_ARSIZE(AXI_01_ARSIZE),
  .AXI_01_ARVALID(AXI_01_ARVALID),
  .AXI_01_AWADDR(AXI_01_AWADDR),
  .AXI_01_AWBURST(AXI_01_AWBURST),
  .AXI_01_AWID(AXI_01_AWID),
  .AXI_01_AWLEN(AXI_01_AWLEN[3:0]),
  .AXI_01_AWSIZE(AXI_01_AWSIZE),
  .AXI_01_AWVALID(AXI_01_AWVALID),
  .AXI_01_RREADY(rready_01),
  .AXI_01_BREADY(bready_01),
  .AXI_01_WDATA(AXI_01_WDATA),
  .AXI_01_WLAST(AXI_01_WLAST),
  .AXI_01_WSTRB(AXI_01_WSTRB),
  .AXI_01_WDATA_PARITY(AXI_01_WDATA_PARITY),
  .AXI_01_WVALID(AXI_01_WVALID),
  //.AXI_01_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_01_DFI_LP_PWR_X_REQ(AXI_01_DFI_LP_PWR_X_REQ),
  .AXI_02_ACLK(AXI_02_ACLK),
  .AXI_02_ARESET_N(AXI_02_ARESET_N),
  .AXI_02_ARADDR(AXI_02_ARADDR),
  .AXI_02_ARBURST(AXI_02_ARBURST),
  .AXI_02_ARID(AXI_02_ARID),
  .AXI_02_ARLEN(AXI_02_ARLEN[3:0]),
  .AXI_02_ARSIZE(AXI_02_ARSIZE),
  .AXI_02_ARVALID(AXI_02_ARVALID),
  .AXI_02_AWADDR(AXI_02_AWADDR),
  .AXI_02_AWBURST(AXI_02_AWBURST),
  .AXI_02_AWID(AXI_02_AWID),
  .AXI_02_AWLEN(AXI_02_AWLEN[3:0]),
  .AXI_02_AWSIZE(AXI_02_AWSIZE),
  .AXI_02_AWVALID(AXI_02_AWVALID),
  .AXI_02_RREADY(rready_02),
  .AXI_02_BREADY(bready_02),
  .AXI_02_WDATA(AXI_02_WDATA),
  .AXI_02_WLAST(AXI_02_WLAST),
  .AXI_02_WSTRB(AXI_02_WSTRB),
  .AXI_02_WDATA_PARITY(AXI_02_WDATA_PARITY),
  .AXI_02_WVALID(AXI_02_WVALID),
  //.AXI_02_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_02_DFI_LP_PWR_X_REQ(AXI_02_DFI_LP_PWR_X_REQ),
  .AXI_03_ACLK(AXI_03_ACLK),
  .AXI_03_ARESET_N(AXI_03_ARESET_N),
  .AXI_03_ARADDR(AXI_03_ARADDR),
  .AXI_03_ARBURST(AXI_03_ARBURST),
  .AXI_03_ARID(AXI_03_ARID),
  .AXI_03_ARLEN(AXI_03_ARLEN[3:0]),
  .AXI_03_ARSIZE(AXI_03_ARSIZE),
  .AXI_03_ARVALID(AXI_03_ARVALID),
  .AXI_03_AWADDR(AXI_03_AWADDR),
  .AXI_03_AWBURST(AXI_03_AWBURST),
  .AXI_03_AWID(AXI_03_AWID),
  .AXI_03_AWLEN(AXI_03_AWLEN[3:0]),
  .AXI_03_AWSIZE(AXI_03_AWSIZE),
  .AXI_03_AWVALID(AXI_03_AWVALID),
  .AXI_03_RREADY(rready_03),
  .AXI_03_BREADY(bready_03),
  .AXI_03_WDATA(AXI_03_WDATA),
  .AXI_03_WLAST(AXI_03_WLAST),
  .AXI_03_WSTRB(AXI_03_WSTRB),
  .AXI_03_WDATA_PARITY(AXI_03_WDATA_PARITY),
  .AXI_03_WVALID(AXI_03_WVALID),
  //.AXI_03_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_03_DFI_LP_PWR_X_REQ(AXI_03_DFI_LP_PWR_X_REQ),
  .AXI_04_ACLK(AXI_04_ACLK),
  .AXI_04_ARESET_N(AXI_04_ARESET_N),
  .AXI_04_ARADDR(AXI_04_ARADDR),
  .AXI_04_ARBURST(AXI_04_ARBURST),
  .AXI_04_ARID(AXI_04_ARID),
  .AXI_04_ARLEN(AXI_04_ARLEN[3:0]),
  .AXI_04_ARSIZE(AXI_04_ARSIZE),
  .AXI_04_ARVALID(AXI_04_ARVALID),
  .AXI_04_AWADDR(AXI_04_AWADDR),
  .AXI_04_AWBURST(AXI_04_AWBURST),
  .AXI_04_AWID(AXI_04_AWID),
  .AXI_04_AWLEN(AXI_04_AWLEN[3:0]),
  .AXI_04_AWSIZE(AXI_04_AWSIZE),
  .AXI_04_AWVALID(AXI_04_AWVALID),
  .AXI_04_RREADY(rready_04),
  .AXI_04_BREADY(bready_04),
  .AXI_04_WDATA(AXI_04_WDATA),
  .AXI_04_WLAST(AXI_04_WLAST),
  .AXI_04_WSTRB(AXI_04_WSTRB),
  .AXI_04_WDATA_PARITY(AXI_04_WDATA_PARITY),
  .AXI_04_WVALID(AXI_04_WVALID),
  //.AXI_04_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_04_DFI_LP_PWR_X_REQ(AXI_04_DFI_LP_PWR_X_REQ),
  .AXI_05_ACLK(AXI_05_ACLK),
  .AXI_05_ARESET_N(AXI_05_ARESET_N),
  .AXI_05_ARADDR(AXI_05_ARADDR),
  .AXI_05_ARBURST(AXI_05_ARBURST),
  .AXI_05_ARID(AXI_05_ARID),
  .AXI_05_ARLEN(AXI_05_ARLEN[3:0]),
  .AXI_05_ARSIZE(AXI_05_ARSIZE),
  .AXI_05_ARVALID(AXI_05_ARVALID),
  .AXI_05_AWADDR(AXI_05_AWADDR),
  .AXI_05_AWBURST(AXI_05_AWBURST),
  .AXI_05_AWID(AXI_05_AWID),
  .AXI_05_AWLEN(AXI_05_AWLEN[3:0]),
  .AXI_05_AWSIZE(AXI_05_AWSIZE),
  .AXI_05_AWVALID(AXI_05_AWVALID),
  .AXI_05_RREADY(rready_05),
  .AXI_05_BREADY(bready_05),
  .AXI_05_WDATA(AXI_05_WDATA),
  .AXI_05_WLAST(AXI_05_WLAST),
  .AXI_05_WSTRB(AXI_05_WSTRB),
  .AXI_05_WDATA_PARITY(AXI_05_WDATA_PARITY),
  .AXI_05_WVALID(AXI_05_WVALID),
  //.AXI_05_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_05_DFI_LP_PWR_X_REQ(AXI_05_DFI_LP_PWR_X_REQ),
  .AXI_06_ACLK(AXI_06_ACLK),
  .AXI_06_ARESET_N(AXI_06_ARESET_N),
  .AXI_06_ARADDR(AXI_06_ARADDR),
  .AXI_06_ARBURST(AXI_06_ARBURST),
  .AXI_06_ARID(AXI_06_ARID),
  .AXI_06_ARLEN(AXI_06_ARLEN[3:0]),
  .AXI_06_ARSIZE(AXI_06_ARSIZE),
  .AXI_06_ARVALID(AXI_06_ARVALID),
  .AXI_06_AWADDR(AXI_06_AWADDR),
  .AXI_06_AWBURST(AXI_06_AWBURST),
  .AXI_06_AWID(AXI_06_AWID),
  .AXI_06_AWLEN(AXI_06_AWLEN[3:0]),
  .AXI_06_AWSIZE(AXI_06_AWSIZE),
  .AXI_06_AWVALID(AXI_06_AWVALID),
  .AXI_06_RREADY(rready_06),
  .AXI_06_BREADY(bready_06),
  .AXI_06_WDATA(AXI_06_WDATA),
  .AXI_06_WLAST(AXI_06_WLAST),
  .AXI_06_WSTRB(AXI_06_WSTRB),
  .AXI_06_WDATA_PARITY(AXI_06_WDATA_PARITY),
  .AXI_06_WVALID(AXI_06_WVALID),
  //.AXI_06_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_06_DFI_LP_PWR_X_REQ(AXI_06_DFI_LP_PWR_X_REQ),
  .AXI_07_ACLK(AXI_07_ACLK),
  .AXI_07_ARESET_N(AXI_07_ARESET_N),
  .AXI_07_ARADDR(AXI_07_ARADDR),
  .AXI_07_ARBURST(AXI_07_ARBURST),
  .AXI_07_ARID(AXI_07_ARID),
  .AXI_07_ARLEN(AXI_07_ARLEN[3:0]),
  .AXI_07_ARSIZE(AXI_07_ARSIZE),
  .AXI_07_ARVALID(AXI_07_ARVALID),
  .AXI_07_AWADDR(AXI_07_AWADDR),
  .AXI_07_AWBURST(AXI_07_AWBURST),
  .AXI_07_AWID(AXI_07_AWID),
  .AXI_07_AWLEN(AXI_07_AWLEN[3:0]),
  .AXI_07_AWSIZE(AXI_07_AWSIZE),
  .AXI_07_AWVALID(AXI_07_AWVALID),
  .AXI_07_RREADY(rready_07),
  .AXI_07_BREADY(bready_07),
  .AXI_07_WDATA(AXI_07_WDATA),
  .AXI_07_WLAST(AXI_07_WLAST),
  .AXI_07_WSTRB(AXI_07_WSTRB),
  .AXI_07_WDATA_PARITY(AXI_07_WDATA_PARITY),
  .AXI_07_WVALID(AXI_07_WVALID),
  //.AXI_07_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_07_DFI_LP_PWR_X_REQ(AXI_07_DFI_LP_PWR_X_REQ),
  .AXI_08_ACLK(AXI_08_ACLK),
  .AXI_08_ARESET_N(AXI_08_ARESET_N),
  .AXI_08_ARADDR(AXI_08_ARADDR),
  .AXI_08_ARBURST(AXI_08_ARBURST),
  .AXI_08_ARID(AXI_08_ARID),
  .AXI_08_ARLEN(AXI_08_ARLEN[3:0]),
  .AXI_08_ARSIZE(AXI_08_ARSIZE),
  .AXI_08_ARVALID(AXI_08_ARVALID),
  .AXI_08_AWADDR(AXI_08_AWADDR),
  .AXI_08_AWBURST(AXI_08_AWBURST),
  .AXI_08_AWID(AXI_08_AWID),
  .AXI_08_AWLEN(AXI_08_AWLEN[3:0]),
  .AXI_08_AWSIZE(AXI_08_AWSIZE),
  .AXI_08_AWVALID(AXI_08_AWVALID),
  .AXI_08_RREADY(rready_08),
  .AXI_08_BREADY(bready_08),
  .AXI_08_WDATA(AXI_08_WDATA),
  .AXI_08_WLAST(AXI_08_WLAST),
  .AXI_08_WSTRB(AXI_08_WSTRB),
  .AXI_08_WDATA_PARITY(AXI_08_WDATA_PARITY),
  .AXI_08_WVALID(AXI_08_WVALID),
  //.AXI_08_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_08_DFI_LP_PWR_X_REQ(AXI_08_DFI_LP_PWR_X_REQ),
  .AXI_09_ACLK(AXI_09_ACLK),
  .AXI_09_ARESET_N(AXI_09_ARESET_N),
  .AXI_09_ARADDR(AXI_09_ARADDR),
  .AXI_09_ARBURST(AXI_09_ARBURST),
  .AXI_09_ARID(AXI_09_ARID),
  .AXI_09_ARLEN(AXI_09_ARLEN[3:0]),
  .AXI_09_ARSIZE(AXI_09_ARSIZE),
  .AXI_09_ARVALID(AXI_09_ARVALID),
  .AXI_09_AWADDR(AXI_09_AWADDR),
  .AXI_09_AWBURST(AXI_09_AWBURST),
  .AXI_09_AWID(AXI_09_AWID),
  .AXI_09_AWLEN(AXI_09_AWLEN[3:0]),
  .AXI_09_AWSIZE(AXI_09_AWSIZE),
  .AXI_09_AWVALID(AXI_09_AWVALID),
  .AXI_09_RREADY(rready_09),
  .AXI_09_BREADY(bready_09),
  .AXI_09_WDATA(AXI_09_WDATA),
  .AXI_09_WLAST(AXI_09_WLAST),
  .AXI_09_WSTRB(AXI_09_WSTRB),
  .AXI_09_WDATA_PARITY(AXI_09_WDATA_PARITY),
  .AXI_09_WVALID(AXI_09_WVALID),
  //.AXI_09_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_09_DFI_LP_PWR_X_REQ(AXI_09_DFI_LP_PWR_X_REQ),
  .AXI_10_ACLK(AXI_10_ACLK),
  .AXI_10_ARESET_N(AXI_10_ARESET_N),
  .AXI_10_ARADDR(AXI_10_ARADDR),
  .AXI_10_ARBURST(AXI_10_ARBURST),
  .AXI_10_ARID(AXI_10_ARID),
  .AXI_10_ARLEN(AXI_10_ARLEN[3:0]),
  .AXI_10_ARSIZE(AXI_10_ARSIZE),
  .AXI_10_ARVALID(AXI_10_ARVALID),
  .AXI_10_AWADDR(AXI_10_AWADDR),
  .AXI_10_AWBURST(AXI_10_AWBURST),
  .AXI_10_AWID(AXI_10_AWID),
  .AXI_10_AWLEN(AXI_10_AWLEN[3:0]),
  .AXI_10_AWSIZE(AXI_10_AWSIZE),
  .AXI_10_AWVALID(AXI_10_AWVALID),
  .AXI_10_RREADY(rready_10),
  .AXI_10_BREADY(bready_10),
  .AXI_10_WDATA(AXI_10_WDATA),
  .AXI_10_WLAST(AXI_10_WLAST),
  .AXI_10_WSTRB(AXI_10_WSTRB),
  .AXI_10_WDATA_PARITY(AXI_10_WDATA_PARITY),
  .AXI_10_WVALID(AXI_10_WVALID),
  //.AXI_10_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_10_DFI_LP_PWR_X_REQ(AXI_10_DFI_LP_PWR_X_REQ),
  .AXI_11_ACLK(AXI_11_ACLK),
  .AXI_11_ARESET_N(AXI_11_ARESET_N),
  .AXI_11_ARADDR(AXI_11_ARADDR),
  .AXI_11_ARBURST(AXI_11_ARBURST),
  .AXI_11_ARID(AXI_11_ARID),
  .AXI_11_ARLEN(AXI_11_ARLEN[3:0]),
  .AXI_11_ARSIZE(AXI_11_ARSIZE),
  .AXI_11_ARVALID(AXI_11_ARVALID),
  .AXI_11_AWADDR(AXI_11_AWADDR),
  .AXI_11_AWBURST(AXI_11_AWBURST),
  .AXI_11_AWID(AXI_11_AWID),
  .AXI_11_AWLEN(AXI_11_AWLEN[3:0]),
  .AXI_11_AWSIZE(AXI_11_AWSIZE),
  .AXI_11_AWVALID(AXI_11_AWVALID),
  .AXI_11_RREADY(rready_11),
  .AXI_11_BREADY(bready_11),
  .AXI_11_WDATA(AXI_11_WDATA),
  .AXI_11_WLAST(AXI_11_WLAST),
  .AXI_11_WSTRB(AXI_11_WSTRB),
  .AXI_11_WDATA_PARITY(AXI_11_WDATA_PARITY),
  .AXI_11_WVALID(AXI_11_WVALID),
  //.AXI_11_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_11_DFI_LP_PWR_X_REQ(AXI_11_DFI_LP_PWR_X_REQ),
  .AXI_12_ACLK(AXI_12_ACLK),
  .AXI_12_ARESET_N(AXI_12_ARESET_N),
  .AXI_12_ARADDR(AXI_12_ARADDR),
  .AXI_12_ARBURST(AXI_12_ARBURST),
  .AXI_12_ARID(AXI_12_ARID),
  .AXI_12_ARLEN(AXI_12_ARLEN[3:0]),
  .AXI_12_ARSIZE(AXI_12_ARSIZE),
  .AXI_12_ARVALID(AXI_12_ARVALID),
  .AXI_12_AWADDR(AXI_12_AWADDR),
  .AXI_12_AWBURST(AXI_12_AWBURST),
  .AXI_12_AWID(AXI_12_AWID),
  .AXI_12_AWLEN(AXI_12_AWLEN[3:0]),
  .AXI_12_AWSIZE(AXI_12_AWSIZE),
  .AXI_12_AWVALID(AXI_12_AWVALID),
  .AXI_12_RREADY(rready_12),
  .AXI_12_BREADY(bready_12),
  .AXI_12_WDATA(AXI_12_WDATA),
  .AXI_12_WLAST(AXI_12_WLAST),
  .AXI_12_WSTRB(AXI_12_WSTRB),
  .AXI_12_WDATA_PARITY(AXI_12_WDATA_PARITY),
  .AXI_12_WVALID(AXI_12_WVALID),
  //.AXI_12_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_12_DFI_LP_PWR_X_REQ(AXI_12_DFI_LP_PWR_X_REQ),
  .AXI_13_ACLK(AXI_13_ACLK),
  .AXI_13_ARESET_N(AXI_13_ARESET_N),
  .AXI_13_ARADDR(AXI_13_ARADDR),
  .AXI_13_ARBURST(AXI_13_ARBURST),
  .AXI_13_ARID(AXI_13_ARID),
  .AXI_13_ARLEN(AXI_13_ARLEN[3:0]),
  .AXI_13_ARSIZE(AXI_13_ARSIZE),
  .AXI_13_ARVALID(AXI_13_ARVALID),
  .AXI_13_AWADDR(AXI_13_AWADDR),
  .AXI_13_AWBURST(AXI_13_AWBURST),
  .AXI_13_AWID(AXI_13_AWID),
  .AXI_13_AWLEN(AXI_13_AWLEN[3:0]),
  .AXI_13_AWSIZE(AXI_13_AWSIZE),
  .AXI_13_AWVALID(AXI_13_AWVALID),
  .AXI_13_RREADY(rready_13),
  .AXI_13_BREADY(bready_13),
  .AXI_13_WDATA(AXI_13_WDATA),
  .AXI_13_WLAST(AXI_13_WLAST),
  .AXI_13_WSTRB(AXI_13_WSTRB),
  .AXI_13_WDATA_PARITY(AXI_13_WDATA_PARITY),
  .AXI_13_WVALID(AXI_13_WVALID),
  //.AXI_13_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_13_DFI_LP_PWR_X_REQ(AXI_13_DFI_LP_PWR_X_REQ),
  .AXI_14_ACLK(AXI_14_ACLK),
  .AXI_14_ARESET_N(AXI_14_ARESET_N),
  .AXI_14_ARADDR(AXI_14_ARADDR),
  .AXI_14_ARBURST(AXI_14_ARBURST),
  .AXI_14_ARID(AXI_14_ARID),
  .AXI_14_ARLEN(AXI_14_ARLEN[3:0]),
  .AXI_14_ARSIZE(AXI_14_ARSIZE),
  .AXI_14_ARVALID(AXI_14_ARVALID),
  .AXI_14_AWADDR(AXI_14_AWADDR),
  .AXI_14_AWBURST(AXI_14_AWBURST),
  .AXI_14_AWID(AXI_14_AWID),
  .AXI_14_AWLEN(AXI_14_AWLEN[3:0]),
  .AXI_14_AWSIZE(AXI_14_AWSIZE),
  .AXI_14_AWVALID(AXI_14_AWVALID),
  .AXI_14_RREADY(rready_14),
  .AXI_14_BREADY(bready_14),
  .AXI_14_WDATA(AXI_14_WDATA),
  .AXI_14_WLAST(AXI_14_WLAST),
  .AXI_14_WSTRB(AXI_14_WSTRB),
  .AXI_14_WDATA_PARITY(AXI_14_WDATA_PARITY),
  .AXI_14_WVALID(AXI_14_WVALID),
  //.AXI_14_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_14_DFI_LP_PWR_X_REQ(AXI_14_DFI_LP_PWR_X_REQ),
  .AXI_15_ACLK(AXI_15_ACLK),
  .AXI_15_ARESET_N(AXI_15_ARESET_N),
  .AXI_15_ARADDR(AXI_15_ARADDR),
  .AXI_15_ARBURST(AXI_15_ARBURST),
  .AXI_15_ARID(AXI_15_ARID),
  .AXI_15_ARLEN(AXI_15_ARLEN[3:0]),
  .AXI_15_ARSIZE(AXI_15_ARSIZE),
  .AXI_15_ARVALID(AXI_15_ARVALID),
  .AXI_15_AWADDR(AXI_15_AWADDR),
  .AXI_15_AWBURST(AXI_15_AWBURST),
  .AXI_15_AWID(AXI_15_AWID),
  .AXI_15_AWLEN(AXI_15_AWLEN[3:0]),
  .AXI_15_AWSIZE(AXI_15_AWSIZE),
  .AXI_15_AWVALID(AXI_15_AWVALID),
  .AXI_15_RREADY(rready_15),
  .AXI_15_BREADY(bready_15),
  .AXI_15_WDATA(AXI_15_WDATA),
  .AXI_15_WLAST(AXI_15_WLAST),
  .AXI_15_WSTRB(AXI_15_WSTRB),
  .AXI_15_WDATA_PARITY(AXI_15_WDATA_PARITY),
  .AXI_15_WVALID(AXI_15_WVALID),
  //.AXI_15_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_15_DFI_LP_PWR_X_REQ(AXI_15_DFI_LP_PWR_X_REQ),
  .APB_0_PWDATA(pwdata_0),
  .APB_0_PADDR(paddr_0),
  .APB_0_PCLK(APB_0_PCLK),
  .APB_0_PENABLE(penable_0),
  .APB_0_PRESET_N(APB_0_PRESET_N),
  .APB_0_PSEL(psel_0),
  .APB_0_PWRITE(pwrite_0),
  .BSCAN_DRCK (1'b0),
  .BSCAN_TCK (1'b0),
  .MBIST_EN_00 (1'b1),
  .MBIST_EN_01 (1'b1),
  .MBIST_EN_02 (1'b1),
  .MBIST_EN_03 (1'b1),
  .MBIST_EN_04 (1'b1),
  .MBIST_EN_05 (1'b1),
  .MBIST_EN_06 (1'b1),
  .MBIST_EN_07 (1'b1)
  );

////////////////////////////////////////////////////////////////////////////////
// Tieing off output ports of two stack unisim 
////////////////////////////////////////////////////////////////////////////////
  assign AXI_16_ARREADY = 1'b0;
  assign AXI_16_AWREADY = 1'b0;
  assign AXI_16_RDATA_PARITY = 32'b0;
  assign AXI_16_RDATA = 256'b0;
  assign AXI_16_RID = 6'b0;
  assign AXI_16_RLAST = 1'b0;
  assign AXI_16_RRESP = 2'b0;
  assign AXI_16_RVALID = 1'b0;
  assign AXI_16_WREADY = 1'b0;
  assign AXI_16_BID = 6'b0;
  assign AXI_16_BRESP = 2'b0;
  assign AXI_16_BVALID = 1'b0;

  assign AXI_17_ARREADY = 1'b0;
  assign AXI_17_AWREADY = 1'b0;
  assign AXI_17_RDATA_PARITY = 32'b0;
  assign AXI_17_RDATA = 256'b0;
  assign AXI_17_RID = 6'b0;
  assign AXI_17_RLAST = 1'b0;
  assign AXI_17_RRESP = 2'b0;
  assign AXI_17_RVALID = 1'b0;
  assign AXI_17_WREADY = 1'b0;
  assign AXI_17_BID = 6'b0;
  assign AXI_17_BRESP = 2'b0;
  assign AXI_17_BVALID = 1'b0;

  assign AXI_18_ARREADY = 1'b0;
  assign AXI_18_AWREADY = 1'b0;
  assign AXI_18_RDATA_PARITY = 32'b0;
  assign AXI_18_RDATA = 256'b0;
  assign AXI_18_RID = 6'b0;
  assign AXI_18_RLAST = 1'b0;
  assign AXI_18_RRESP = 2'b0;
  assign AXI_18_RVALID = 1'b0;
  assign AXI_18_WREADY = 1'b0;
  assign AXI_18_BID = 6'b0;
  assign AXI_18_BRESP = 2'b0;
  assign AXI_18_BVALID = 1'b0;

  assign AXI_19_ARREADY = 1'b0;
  assign AXI_19_AWREADY = 1'b0;
  assign AXI_19_RDATA_PARITY = 32'b0;
  assign AXI_19_RDATA = 256'b0;
  assign AXI_19_RID = 6'b0;
  assign AXI_19_RLAST = 1'b0;
  assign AXI_19_RRESP = 2'b0;
  assign AXI_19_RVALID = 1'b0;
  assign AXI_19_WREADY = 1'b0;
  assign AXI_19_BID = 6'b0;
  assign AXI_19_BRESP = 2'b0;
  assign AXI_19_BVALID = 1'b0;

  assign AXI_20_ARREADY = 1'b0;
  assign AXI_20_AWREADY = 1'b0;
  assign AXI_20_RDATA_PARITY = 32'b0;
  assign AXI_20_RDATA = 256'b0;
  assign AXI_20_RID = 6'b0;
  assign AXI_20_RLAST = 1'b0;
  assign AXI_20_RRESP = 2'b0;
  assign AXI_20_RVALID = 1'b0;
  assign AXI_20_WREADY = 1'b0;
  assign AXI_20_BID = 6'b0;
  assign AXI_20_BRESP = 2'b0;
  assign AXI_20_BVALID = 1'b0;

  assign AXI_21_ARREADY = 1'b0;
  assign AXI_21_AWREADY = 1'b0;
  assign AXI_21_RDATA_PARITY = 32'b0;
  assign AXI_21_RDATA = 256'b0;
  assign AXI_21_RID = 6'b0;
  assign AXI_21_RLAST = 1'b0;
  assign AXI_21_RRESP = 2'b0;
  assign AXI_21_RVALID = 1'b0;
  assign AXI_21_WREADY = 1'b0;
  assign AXI_21_BID = 6'b0;
  assign AXI_21_BRESP = 2'b0;
  assign AXI_21_BVALID = 1'b0;

  assign AXI_22_ARREADY = 1'b0;
  assign AXI_22_AWREADY = 1'b0;
  assign AXI_22_RDATA_PARITY = 32'b0;
  assign AXI_22_RDATA = 256'b0;
  assign AXI_22_RID = 6'b0;
  assign AXI_22_RLAST = 1'b0;
  assign AXI_22_RRESP = 2'b0;
  assign AXI_22_RVALID = 1'b0;
  assign AXI_22_WREADY = 1'b0;
  assign AXI_22_BID = 6'b0;
  assign AXI_22_BRESP = 2'b0;
  assign AXI_22_BVALID = 1'b0;

  assign AXI_23_ARREADY = 1'b0;
  assign AXI_23_AWREADY = 1'b0;
  assign AXI_23_RDATA_PARITY = 32'b0;
  assign AXI_23_RDATA = 256'b0;
  assign AXI_23_RID = 6'b0;
  assign AXI_23_RLAST = 1'b0;
  assign AXI_23_RRESP = 2'b0;
  assign AXI_23_RVALID = 1'b0;
  assign AXI_23_WREADY = 1'b0;
  assign AXI_23_BID = 6'b0;
  assign AXI_23_BRESP = 2'b0;
  assign AXI_23_BVALID = 1'b0;

  assign AXI_24_ARREADY = 1'b0;
  assign AXI_24_AWREADY = 1'b0;
  assign AXI_24_RDATA_PARITY = 32'b0;
  assign AXI_24_RDATA = 256'b0;
  assign AXI_24_RID = 6'b0;
  assign AXI_24_RLAST = 1'b0;
  assign AXI_24_RRESP = 2'b0;
  assign AXI_24_RVALID = 1'b0;
  assign AXI_24_WREADY = 1'b0;
  assign AXI_24_BID = 6'b0;
  assign AXI_24_BRESP = 2'b0;
  assign AXI_24_BVALID = 1'b0;

  assign AXI_25_ARREADY = 1'b0;
  assign AXI_25_AWREADY = 1'b0;
  assign AXI_25_RDATA_PARITY = 32'b0;
  assign AXI_25_RDATA = 256'b0;
  assign AXI_25_RID = 6'b0;
  assign AXI_25_RLAST = 1'b0;
  assign AXI_25_RRESP = 2'b0;
  assign AXI_25_RVALID = 1'b0;
  assign AXI_25_WREADY = 1'b0;
  assign AXI_25_BID = 6'b0;
  assign AXI_25_BRESP = 2'b0;
  assign AXI_25_BVALID = 1'b0;

  assign AXI_26_ARREADY = 1'b0;
  assign AXI_26_AWREADY = 1'b0;
  assign AXI_26_RDATA_PARITY = 32'b0;
  assign AXI_26_RDATA = 256'b0;
  assign AXI_26_RID = 6'b0;
  assign AXI_26_RLAST = 1'b0;
  assign AXI_26_RRESP = 2'b0;
  assign AXI_26_RVALID = 1'b0;
  assign AXI_26_WREADY = 1'b0;
  assign AXI_26_BID = 6'b0;
  assign AXI_26_BRESP = 2'b0;
  assign AXI_26_BVALID = 1'b0;

  assign AXI_27_ARREADY = 1'b0;
  assign AXI_27_AWREADY = 1'b0;
  assign AXI_27_RDATA_PARITY = 32'b0;
  assign AXI_27_RDATA = 256'b0;
  assign AXI_27_RID = 6'b0;
  assign AXI_27_RLAST = 1'b0;
  assign AXI_27_RRESP = 2'b0;
  assign AXI_27_RVALID = 1'b0;
  assign AXI_27_WREADY = 1'b0;
  assign AXI_27_BID = 6'b0;
  assign AXI_27_BRESP = 2'b0;
  assign AXI_27_BVALID = 1'b0;

  assign AXI_28_ARREADY = 1'b0;
  assign AXI_28_AWREADY = 1'b0;
  assign AXI_28_RDATA_PARITY = 32'b0;
  assign AXI_28_RDATA = 256'b0;
  assign AXI_28_RID = 6'b0;
  assign AXI_28_RLAST = 1'b0;
  assign AXI_28_RRESP = 2'b0;
  assign AXI_28_RVALID = 1'b0;
  assign AXI_28_WREADY = 1'b0;
  assign AXI_28_BID = 6'b0;
  assign AXI_28_BRESP = 2'b0;
  assign AXI_28_BVALID = 1'b0;

  assign AXI_29_ARREADY = 1'b0;
  assign AXI_29_AWREADY = 1'b0;
  assign AXI_29_RDATA_PARITY = 32'b0;
  assign AXI_29_RDATA = 256'b0;
  assign AXI_29_RID = 6'b0;
  assign AXI_29_RLAST = 1'b0;
  assign AXI_29_RRESP = 2'b0;
  assign AXI_29_RVALID = 1'b0;
  assign AXI_29_WREADY = 1'b0;
  assign AXI_29_BID = 6'b0;
  assign AXI_29_BRESP = 2'b0;
  assign AXI_29_BVALID = 1'b0;

  assign AXI_30_ARREADY = 1'b0;
  assign AXI_30_AWREADY = 1'b0;
  assign AXI_30_RDATA_PARITY = 32'b0;
  assign AXI_30_RDATA = 256'b0;
  assign AXI_30_RID = 6'b0;
  assign AXI_30_RLAST = 1'b0;
  assign AXI_30_RRESP = 2'b0;
  assign AXI_30_RVALID = 1'b0;
  assign AXI_30_WREADY = 1'b0;
  assign AXI_30_BID = 6'b0;
  assign AXI_30_BRESP = 2'b0;
  assign AXI_30_BVALID = 1'b0;

  assign AXI_31_ARREADY = 1'b0;
  assign AXI_31_AWREADY = 1'b0;
  assign AXI_31_RDATA_PARITY = 32'b0;
  assign AXI_31_RDATA = 256'b0;
  assign AXI_31_RID = 6'b0;
  assign AXI_31_RLAST = 1'b0;
  assign AXI_31_RRESP = 2'b0;
  assign AXI_31_RVALID = 1'b0;
  assign AXI_31_WREADY = 1'b0;
  assign AXI_31_BID = 6'b0;
  assign AXI_31_BRESP = 2'b0;
  assign AXI_31_BVALID = 1'b0;

  assign APB_1_PRDATA = 32'b0;
  assign APB_1_PREADY = 1'b0;
  assign APB_1_PSLVERR = 1'b0;
  
  assign DRAM_1_STAT_CATTRIP = 1'b0;
  assign DRAM_1_STAT_TEMP = 3'b0;

  assign apb_complete_1 = 1'b0;

end
endgenerate

////////////////////////////////////////////////////////////////////////////////
// Module instances when HBM Stack selected is Two
////////////////////////////////////////////////////////////////////////////////
generate 
if (HBM_STACK == 2) begin : TWO_STACK_HBM

assign TEMP_STATUS_ST0 = ((temp_value_0_s > 7'h05) && (temp_value_1_s > 7'h05)) ? ((temp_value_0_s > temp_value_1_s) ? temp_value_0_s : temp_value_1_s) : ((temp_value_0_s < temp_value_1_s) ? temp_value_0_s : temp_value_1_s) ;
assign TEMP_STATUS_ST1 = ((temp_value_0_s > 7'h05) && (temp_value_1_s > 7'h05)) ? ((temp_value_0_s > temp_value_1_s) ? temp_value_0_s : temp_value_1_s) : ((temp_value_0_s < temp_value_1_s) ? temp_value_0_s : temp_value_1_s) ;

//////////////////////////////////////////////////////////////////////////////////////
// Instantiating XPM memory - 0
////////////////////////////////////////////////////////////////////////////////
xpm_memory_spram # (
  // Common module parameters
  .MEMORY_SIZE        (65536),                 //positive integer
  .MEMORY_PRIMITIVE   ("auto"),               //string; "auto", "distributed", "block" or "ultra";
  .ECC_MODE           ("no_ecc"),             //do not change
`ifdef SIMULATION_MODE
  .MEMORY_INIT_FILE   ("xpm_internal_config_file_sim_0.mem"), //string; "none" or "<filename>.mem" 
`else
`ifdef NETLIST_SIM
  .MEMORY_INIT_FILE   ("xpm_internal_config_file_sim_0.mem"), //string; "none" or "<filename>.mem" 
`else
  .MEMORY_INIT_FILE   ("xpm_internal_config_file_0.mem"), //string; "none" or "<filename>.mem" 
`endif
`endif
  .MEMORY_INIT_PARAM  (""    ),              //string;
  .WAKEUP_TIME        ("disable_sleep"),     //string; "disable_sleep" or "use_sleep_pin" 
  .MESSAGE_CONTROL    (0),
  // Port A module parameters
  .WRITE_DATA_WIDTH_A (32),               //positive integer
  .READ_DATA_WIDTH_A  (32),               //positive integer
  .BYTE_WRITE_WIDTH_A (32),               //integer; 8, 9, or WRITE_DATA_WIDTH_A value
  .ADDR_WIDTH_A       (11),                //positive integer
  .READ_RESET_VALUE_A ("0"),              //string
  .READ_LATENCY_A     (1),                //non-negative integer
  .WRITE_MODE_A       ("read_first")      //string; "write_first", "read_first", "no_change" 
) xpm_memory_spram_inst_0 (
  // Common module ports
  .sleep          (1'b0),  //do not change
  // Port A module ports
  .clka           (APB_0_PCLK),
  .rsta           (~APB_0_PRESET_N),
  .ena            (xpm_ena_0),
  .regcea         (1'b1),
  .wea            (xpm_wea_0),
  .addra          (xpm_addra_0),
  .dina           (xpm_dina_0),
  .injectsbiterra (1'b0),  //do not change
  .injectdbiterra (1'b0),  //do not change
  .douta          (xpm_douta_0),
  .sbiterra       (),      //do not change
  .dbiterra       ()       //do not change
);

////////////////////////////////////////////////////////////////////////////////
// Instantiating Module to fetch data from XPM memory - 0
////////////////////////////////////////////////////////////////////////////////
hbm_data_fetch #(
  .XPM_ADDR_WIDTH (11),
  .XPM_DATA_WIDTH (32),
  .APB_ADDR_WIDTH (22),
  .APB_DATA_WIDTH (32)
) hbm_data_fetch_0 (
  .apb_clk    (APB_0_PCLK),
  .apb_rst_n  (APB_0_PRESET_N),
  .xpm_ena    (xpm_ena_0),
  .xpm_wea    (xpm_wea_0),
  .xpm_addra  (xpm_addra_0),
  .xpm_dina   (xpm_dina_0),
  .xpm_douta  (xpm_douta_0),

  .apb_back_press    (apb_back_press_0),
  .apb_poll_complete (apb_poll_complete_0),
  .init_seq_complete (init_seq_complete_0),
  .gen_apb_tran      (gen_apb_tran_0),
  .gen_apb_wr_rd     (gen_apb_wr_rd_0),
  .gen_poll          (gen_poll_0),
  .gen_apb_addr      (gen_apb_addr_0),
  .gen_apb_data      (gen_apb_data_0)
);

////////////////////////////////////////////////////////////////////////////////
// Instantiating Module for APB Master interface - 0
////////////////////////////////////////////////////////////////////////////////
hbm_apb_mst #(
  .INIT_BYPASS (INIT_BYPASS), 
  .INIT_SEQ_TIMEOUT (INIT_SEQ_TIMEOUT),
  .APB_ADDR_WIDTH (22),
  .APB_DATA_WIDTH (32)
) hbm_apb_mst_0 (
  .apb_clk           (APB_0_PCLK),
  .apb_rst_n         (APB_0_PRESET_N),
  .apb_back_press    (apb_back_press_0),
  .apb_poll_complete (apb_poll_complete_0),
  .init_seq_complete (init_seq_complete_0),
  .gen_apb_tran      (gen_apb_tran_0),
  .gen_apb_wr_rd     (gen_apb_wr_rd_0),
  .gen_poll          (gen_poll_0),
  .gen_apb_addr      (gen_apb_addr_0),
  .gen_apb_data      (gen_apb_data_0),
  .apb_switch        (apb_complete_0),
  .valid_window_fail (valid_window_fail_0),

  .psel              (intrnl_apb_psel_0_s   ),
  .pwrite            (intrnl_apb_pwrite_0_s ),
  .penable           (intrnl_apb_penable_0_s),
  .paddr             (intrnl_apb_paddr_0_s  ),
  .pwdata            (intrnl_apb_pwdata_0_s ),
  .prdata            (intrnl_apb_prdata_0_s ),
  .pready            (intrnl_apb_pready_0_s ),
  .pslverr           (intrnl_apb_pslverr_0_s)

);

////////////////////////////////////////////////////////////////////////////////
// Instantiating Module for XSDB - 0
////////////////////////////////////////////////////////////////////////////////
`ifdef EN_DBG_HUB
xsdb_top #(
  .PLL_CSV_VER        (16'h0001),
  .MC_CSV_VER         (16'h0002),
  .PHY_CSV_VER        (16'h0001),
  .HBM_STACK_CSV_VER  (16'h0001),
  .HBM_STACK_NUM      (16'h0000),
  .HBM_CLOCK_FREQ     (HBM_CLK_FREQ_0),
  .INT_VERSION        (16'h0002),
  .SWITCH_EN          (SWITCH_EN_0),
  .AXI_SW_CLK         (AXI_SW_CLK_SEL_0),
  .PLL_REF_CLK        (HBM_REF_CLK_FREQ_0)
) u_xsdb_top_0 (
  .clkb               (APB_0_PCLK           ),
  .sl_iport0          (sl_iport0            ),
  .sl_oport0          (sl_oport0            ),
  .x2a_debug          (x2a_debug_0          ),
  .TEMP_STATUS        (TEMP_STATUS_ST0      ),
  .CATTRIP            (DRAM_0_STAT_CATTRIP  ),
  .APB_COMPLETE       (apb_complete_0       ),
  .XSDB_APB_GRANT     (xsdb_apb_grant_0_s   ),
  .XSDB_APB_PRDATA    (xsdb_apb_prdata_0_s  ),
  .XSDB_APB_PREADY    (xsdb_apb_pready_0_s  ),
  .XSDB_APB_PSLVERR   (xsdb_apb_pslverr_0_s ),
  .XSDB_APB_PREQ      (xsdb_apb_req_0_s     ),
  .XSDB_APB_PSEL      (xsdb_apb_psel_0_s    ),
  .XSDB_APB_PWRITE    (xsdb_apb_pwrite_0_s  ),
  .XSDB_APB_PENABLE   (xsdb_apb_penable_0_s ),
  .XSDB_APB_PADDR     (xsdb_apb_paddr_0_s   ),
  .XSDB_APB_PWDATA    (xsdb_apb_pwdata_0_s  )
);
`else
assign sl_oport0            = 17'b0;
assign xsdb_apb_req_0_s     = 1'b0;
assign xsdb_apb_psel_0_s    = 1'b0;
assign xsdb_apb_pwrite_0_s  = 1'b0;
assign xsdb_apb_penable_0_s = 1'b0;
assign xsdb_apb_paddr_0_s   = 22'b0;
assign xsdb_apb_pwdata_0_s  = 32'b0;
`endif

////////////////////////////////////////////////////////////////////////////////
// Instantiating Module for Temperature Read
////////////////////////////////////////////////////////////////////////////////
hbm_temp_rd #(
  .TEMP_WAIT_PERIOD (TEMP_WAIT_PERIOD_0),
  .APB_ADDR_WIDTH   (22),
  .APB_DATA_WIDTH   (32)
) u_hbm_temp_rd_0 (
  .apb_clk            (APB_0_PCLK),
  .apb_rst_n          (APB_0_PRESET_N),

  .temp_apb_req       (temp_apb_req_0_s),
  .temp_apb_grant     (temp_apb_grant_0_s),
  .init_seq_complete  (apb_complete_0),

  .temp_valid         (temp_valid_0_s),
  .temp_value         (temp_value_0_s),

  .psel               (temp_apb_psel_0_s   ),
  .pwrite             (temp_apb_pwrite_0_s ),
  .penable            (temp_apb_penable_0_s),
  .paddr              (temp_apb_paddr_0_s  ),
  .pwdata             (temp_apb_pwdata_0_s ),
  .prdata             (temp_apb_prdata_0_s ),
  .pready             (temp_apb_pready_0_s ),
  .pslverr            (temp_apb_pslverr_0_s)
);

////////////////////////////////////////////////////////////////////////////////
// Instantiating Module for APB MUX-0
////////////////////////////////////////////////////////////////////////////////
hbm_apb_arbiter #(
  .INIT_BYPASS (INIT_BYPASS), 
  .APB_ADDR_WIDTH (22),
  .APB_DATA_WIDTH (32)
) hbm_apb_arbiter_0 (
  .apb_clk                (APB_0_PCLK),
  .apb_rst_n              (APB_0_PRESET_N),

  .intrnl_apb_complete    (apb_complete_0        ),
  .intrnl_apb_psel        (intrnl_apb_psel_0_s   ),
  .intrnl_apb_pwrite      (intrnl_apb_pwrite_0_s ),
  .intrnl_apb_penable     (intrnl_apb_penable_0_s),
  .intrnl_apb_paddr       (intrnl_apb_paddr_0_s  ),
  .intrnl_apb_pwdata      (intrnl_apb_pwdata_0_s ),
  .intrnl_apb_prdata      (intrnl_apb_prdata_0_s ),
  .intrnl_apb_pready      (intrnl_apb_pready_0_s ),
  .intrnl_apb_pslverr     (intrnl_apb_pslverr_0_s),

  .extrnl_apb_psel        (APB_0_PSEL            ),
  .extrnl_apb_pwrite      (APB_0_PWRITE          ),
  .extrnl_apb_penable     (APB_0_PENABLE         ),
  .extrnl_apb_paddr       (APB_0_PADDR           ),
  .extrnl_apb_pwdata      (APB_0_PWDATA          ),
  .extrnl_apb_prdata      (APB_0_PRDATA          ),
  .extrnl_apb_pready      (APB_0_PREADY          ),
  .extrnl_apb_pslverr     (APB_0_PSLVERR         ),

`ifdef SIMULATION_MODE
  .xsdb_apb_req           (1'b0                  ),
  .xsdb_apb_grant         (xsdb_apb_grant_0_s    ),
  .xsdb_apb_psel          (1'b0                  ),
  .xsdb_apb_pwrite        (1'b0                  ),
  .xsdb_apb_penable       (1'b0                  ),
  .xsdb_apb_paddr         (22'b0                 ),
  .xsdb_apb_pwdata        (32'b0                 ),
  .xsdb_apb_prdata        (xsdb_apb_prdata_0_s   ),
  .xsdb_apb_pready        (xsdb_apb_pready_0_s   ),
  .xsdb_apb_pslverr       (xsdb_apb_pslverr_0_s  ),
`else
  .xsdb_apb_req           (xsdb_apb_req_0_s      ),
  .xsdb_apb_grant         (xsdb_apb_grant_0_s    ),
  .xsdb_apb_psel          (xsdb_apb_psel_0_s     ),
  .xsdb_apb_pwrite        (xsdb_apb_pwrite_0_s   ),
  .xsdb_apb_penable       (xsdb_apb_penable_0_s  ),
  .xsdb_apb_paddr         (xsdb_apb_paddr_0_s    ),
  .xsdb_apb_pwdata        (xsdb_apb_pwdata_0_s   ),
  .xsdb_apb_prdata        (xsdb_apb_prdata_0_s   ),
  .xsdb_apb_pready        (xsdb_apb_pready_0_s   ),
  .xsdb_apb_pslverr       (xsdb_apb_pslverr_0_s  ),
`endif

  .temp_apb_req           (temp_apb_req_0_s      ),
  .temp_apb_grant         (temp_apb_grant_0_s    ),
  .temp_apb_psel          (temp_apb_psel_0_s     ),
  .temp_apb_pwrite        (temp_apb_pwrite_0_s   ),
  .temp_apb_penable       (temp_apb_penable_0_s  ),
  .temp_apb_paddr         (temp_apb_paddr_0_s    ),
  .temp_apb_pwdata        (temp_apb_pwdata_0_s   ),
  .temp_apb_prdata        (temp_apb_prdata_0_s   ),
  .temp_apb_pready        (temp_apb_pready_0_s   ),
  .temp_apb_pslverr       (temp_apb_pslverr_0_s  ),

  .psel                   (psel_0                ),
  .pwrite                 (pwrite_0              ),
  .penable                (penable_0             ),
  .paddr                  (paddr_0               ),
  .pwdata                 (pwdata_0              ),
  .prdata                 (prdata_0              ),
  .pready                 (pready_0              ),
  .pslverr                (pslverr_0             )
);

////////////////////////////////////////////////////////////////////////////////
// Instantiating XPM memory - 1
////////////////////////////////////////////////////////////////////////////////
xpm_memory_spram # (
  // Common module parameters
  .MEMORY_SIZE        (65536),                 //positive integer
  .MEMORY_PRIMITIVE   ("auto"),               //string; "auto", "distributed", "block" or "ultra";
  .ECC_MODE           ("no_ecc"),             //do not change
`ifdef SIMULATION_MODE
  .MEMORY_INIT_FILE   ("xpm_internal_config_file_sim_1.mem"), //string; "none" or "<filename>.mem" 
`else
`ifdef NETLIST_SIM
  .MEMORY_INIT_FILE   ("xpm_internal_config_file_sim_1.mem"), //string; "none" or "<filename>.mem" 
`else
  .MEMORY_INIT_FILE   ("xpm_internal_config_file_1.mem"), //string; "none" or "<filename>.mem" 
`endif
`endif
  .MEMORY_INIT_PARAM  (""    ),              //string;
  .WAKEUP_TIME        ("disable_sleep"),     //string; "disable_sleep" or "use_sleep_pin" 
  .MESSAGE_CONTROL    (0),
  // Port A module parameters
  .WRITE_DATA_WIDTH_A (32),               //positive integer
  .READ_DATA_WIDTH_A  (32),               //positive integer
  .BYTE_WRITE_WIDTH_A (32),               //integer; 8, 9, or WRITE_DATA_WIDTH_A value
  .ADDR_WIDTH_A       (11),                //positive integer
  .READ_RESET_VALUE_A ("0"),              //string
  .READ_LATENCY_A     (1),                //non-negative integer
  .WRITE_MODE_A       ("read_first")      //string; "write_first", "read_first", "no_change" 
) xpm_memory_spram_inst_1 (
  // Common module ports
  .sleep          (1'b0),  //do not change
  // Port A module ports
  .clka           (APB_1_PCLK),
  .rsta           (~APB_1_PRESET_N),
  .ena            (xpm_ena_1),
  .regcea         (1'b1),
  .wea            (xpm_wea_1),
  .addra          (xpm_addra_1),
  .dina           (xpm_dina_1),
  .injectsbiterra (1'b0),  //do not change
  .injectdbiterra (1'b0),  //do not change
  .douta          (xpm_douta_1),
  .sbiterra       (),      //do not change
  .dbiterra       ()       //do not change
);

////////////////////////////////////////////////////////////////////////////////
// Instantiating Module to fetch data from XPM memory - 1
////////////////////////////////////////////////////////////////////////////////
hbm_data_fetch #(
  .XPM_ADDR_WIDTH (11),
  .XPM_DATA_WIDTH (32),
  .APB_ADDR_WIDTH (22),
  .APB_DATA_WIDTH (32)
) hbm_data_fetch_1 (
  .apb_clk    (APB_1_PCLK),
  .apb_rst_n  (APB_1_PRESET_N),
  .xpm_ena    (xpm_ena_1),
  .xpm_wea    (xpm_wea_1),
  .xpm_addra  (xpm_addra_1),
  .xpm_dina   (xpm_dina_1),
  .xpm_douta  (xpm_douta_1),

  .apb_back_press    (apb_back_press_1),
  .apb_poll_complete (apb_poll_complete_1),
  .init_seq_complete (init_seq_complete_1),
  .gen_apb_tran      (gen_apb_tran_1),
  .gen_apb_wr_rd     (gen_apb_wr_rd_1),
  .gen_poll          (gen_poll_1),
  .gen_apb_addr      (gen_apb_addr_1),
  .gen_apb_data      (gen_apb_data_1)
);

////////////////////////////////////////////////////////////////////////////////
// Instantiating Module for APB Master interface - 1
////////////////////////////////////////////////////////////////////////////////
hbm_apb_mst #(
  .INIT_BYPASS (INIT_BYPASS), 
  .INIT_SEQ_TIMEOUT (INIT_SEQ_TIMEOUT),
  .APB_ADDR_WIDTH (22),
  .APB_DATA_WIDTH (32)
) hbm_apb_mst_1 (
  .apb_clk           (APB_1_PCLK),
  .apb_rst_n         (APB_1_PRESET_N),
  .apb_back_press    (apb_back_press_1),
  .init_seq_complete (init_seq_complete_1),
  .apb_poll_complete (apb_poll_complete_1),
  .gen_apb_tran      (gen_apb_tran_1),
  .gen_apb_wr_rd     (gen_apb_wr_rd_1),
  .gen_poll          (gen_poll_1),
  .gen_apb_addr      (gen_apb_addr_1),
  .gen_apb_data      (gen_apb_data_1),
  .apb_switch        (apb_complete_1),
  .valid_window_fail (valid_window_fail_1),

  .psel              (intrnl_apb_psel_1_s   ),
  .pwrite            (intrnl_apb_pwrite_1_s ),
  .penable           (intrnl_apb_penable_1_s),
  .paddr             (intrnl_apb_paddr_1_s  ),
  .pwdata            (intrnl_apb_pwdata_1_s ),
  .prdata            (intrnl_apb_prdata_1_s ),
  .pready            (intrnl_apb_pready_1_s ),
  .pslverr           (intrnl_apb_pslverr_1_s)
);

////////////////////////////////////////////////////////////////////////////////
// Instantiating Module for XSDB - 1
////////////////////////////////////////////////////////////////////////////////
`ifdef EN_DBG_HUB
xsdb_top #(
  .PLL_CSV_VER        (16'h0001),
  .MC_CSV_VER         (16'h0002),
  .PHY_CSV_VER        (16'h0001),
  .HBM_STACK_CSV_VER  (16'h0001),
  .HBM_STACK_NUM      (16'h0001),
  .HBM_CLOCK_FREQ     (HBM_CLK_FREQ_1),
  .INT_VERSION        (16'h0002),
  .SWITCH_EN          (SWITCH_EN_1),
  .AXI_SW_CLK         (AXI_SW_CLK_SEL_1),
  .PLL_REF_CLK        (HBM_REF_CLK_FREQ_1)
) u_xsdb_top_1 (
  .clkb               (APB_1_PCLK           ),
  .sl_iport0          (sl_iport1            ),
  .sl_oport0          (sl_oport1            ),
  .x2a_debug          (x2a_debug_1          ),
  .TEMP_STATUS        (TEMP_STATUS_ST1      ),
  .CATTRIP            (DRAM_0_STAT_CATTRIP  ),
  .APB_COMPLETE       (apb_complete_1       ),
  .XSDB_APB_GRANT     (xsdb_apb_grant_1_s   ),
  .XSDB_APB_PRDATA    (xsdb_apb_prdata_1_s  ),
  .XSDB_APB_PREADY    (xsdb_apb_pready_1_s  ),
  .XSDB_APB_PSLVERR   (xsdb_apb_pslverr_1_s ),
  .XSDB_APB_PREQ      (xsdb_apb_req_1_s     ),
  .XSDB_APB_PSEL      (xsdb_apb_psel_1_s    ),
  .XSDB_APB_PWRITE    (xsdb_apb_pwrite_1_s  ),
  .XSDB_APB_PENABLE   (xsdb_apb_penable_1_s ),
  .XSDB_APB_PADDR     (xsdb_apb_paddr_1_s   ),
  .XSDB_APB_PWDATA    (xsdb_apb_pwdata_1_s  )
);
`else
assign sl_oport1            = 17'b0;
assign xsdb_apb_req_1_s     = 1'b0;
assign xsdb_apb_psel_1_s    = 1'b0;
assign xsdb_apb_pwrite_1_s  = 1'b0;
assign xsdb_apb_penable_1_s = 1'b0;
assign xsdb_apb_paddr_1_s   = 22'b0;
assign xsdb_apb_pwdata_1_s  = 32'b0;
`endif

////////////////////////////////////////////////////////////////////////////////
// Instantiating Module for Temperature Read
////////////////////////////////////////////////////////////////////////////////
hbm_temp_rd #(
  .TEMP_WAIT_PERIOD (TEMP_WAIT_PERIOD_1),
  .APB_ADDR_WIDTH   (22),
  .APB_DATA_WIDTH   (32)
) u_hbm_temp_rd_1 (
  .apb_clk            (APB_1_PCLK),
  .apb_rst_n          (APB_1_PRESET_N),

  .temp_apb_req       (temp_apb_req_1_s),
  .temp_apb_grant     (temp_apb_grant_1_s),
  .init_seq_complete  (apb_complete_1),

  .temp_valid         (temp_valid_1_s),
  .temp_value         (temp_value_1_s),

  .psel               (temp_apb_psel_1_s   ),
  .pwrite             (temp_apb_pwrite_1_s ),
  .penable            (temp_apb_penable_1_s),
  .paddr              (temp_apb_paddr_1_s  ),
  .pwdata             (temp_apb_pwdata_1_s ),
  .prdata             (temp_apb_prdata_1_s ),
  .pready             (temp_apb_pready_1_s ),
  .pslverr            (temp_apb_pslverr_1_s)
);

////////////////////////////////////////////////////////////////////////////////
// Instantiating Module for APB MUX-1
////////////////////////////////////////////////////////////////////////////////
hbm_apb_arbiter #(
  .INIT_BYPASS (INIT_BYPASS), 
  .APB_ADDR_WIDTH (22),
  .APB_DATA_WIDTH (32)
) hbm_apb_arbiter_1 (
  .apb_clk                (APB_1_PCLK),
  .apb_rst_n              (APB_1_PRESET_N),

  .intrnl_apb_complete    (apb_complete_1        ),
  .intrnl_apb_psel        (intrnl_apb_psel_1_s   ),
  .intrnl_apb_pwrite      (intrnl_apb_pwrite_1_s ),
  .intrnl_apb_penable     (intrnl_apb_penable_1_s),
  .intrnl_apb_paddr       (intrnl_apb_paddr_1_s  ),
  .intrnl_apb_pwdata      (intrnl_apb_pwdata_1_s ),
  .intrnl_apb_prdata      (intrnl_apb_prdata_1_s ),
  .intrnl_apb_pready      (intrnl_apb_pready_1_s ),
  .intrnl_apb_pslverr     (intrnl_apb_pslverr_1_s),

  .extrnl_apb_psel        (APB_1_PSEL            ),
  .extrnl_apb_pwrite      (APB_1_PWRITE          ),
  .extrnl_apb_penable     (APB_1_PENABLE         ),
  .extrnl_apb_paddr       (APB_1_PADDR           ),
  .extrnl_apb_pwdata      (APB_1_PWDATA          ),
  .extrnl_apb_prdata      (APB_1_PRDATA          ),
  .extrnl_apb_pready      (APB_1_PREADY          ),
  .extrnl_apb_pslverr     (APB_1_PSLVERR         ),

`ifdef SIMULATION_MODE
  .xsdb_apb_req           (1'b0                  ),
  .xsdb_apb_grant         (xsdb_apb_grant_1_s    ),
  .xsdb_apb_psel          (1'b0                  ),
  .xsdb_apb_pwrite        (1'b0                  ),
  .xsdb_apb_penable       (1'b0                  ),
  .xsdb_apb_paddr         (22'b0                 ),
  .xsdb_apb_pwdata        (32'b0                 ),
  .xsdb_apb_prdata        (xsdb_apb_prdata_1_s   ),
  .xsdb_apb_pready        (xsdb_apb_pready_1_s   ),
  .xsdb_apb_pslverr       (xsdb_apb_pslverr_1_s  ),
`else
  .xsdb_apb_req           (xsdb_apb_req_1_s      ),
  .xsdb_apb_grant         (xsdb_apb_grant_1_s    ),
  .xsdb_apb_psel          (xsdb_apb_psel_1_s     ),
  .xsdb_apb_pwrite        (xsdb_apb_pwrite_1_s   ),
  .xsdb_apb_penable       (xsdb_apb_penable_1_s  ),
  .xsdb_apb_paddr         (xsdb_apb_paddr_1_s    ),
  .xsdb_apb_pwdata        (xsdb_apb_pwdata_1_s   ),
  .xsdb_apb_prdata        (xsdb_apb_prdata_1_s   ),
  .xsdb_apb_pready        (xsdb_apb_pready_1_s   ),
  .xsdb_apb_pslverr       (xsdb_apb_pslverr_1_s  ),
`endif

  .temp_apb_req           (temp_apb_req_1_s      ),
  .temp_apb_grant         (temp_apb_grant_1_s    ),
  .temp_apb_psel          (temp_apb_psel_1_s     ),
  .temp_apb_pwrite        (temp_apb_pwrite_1_s   ),
  .temp_apb_penable       (temp_apb_penable_1_s  ),
  .temp_apb_paddr         (temp_apb_paddr_1_s    ),
  .temp_apb_pwdata        (temp_apb_pwdata_1_s   ),
  .temp_apb_prdata        (temp_apb_prdata_1_s   ),
  .temp_apb_pready        (temp_apb_pready_1_s   ),
  .temp_apb_pslverr       (temp_apb_pslverr_1_s  ),

  .psel                   (psel_1                ),
  .pwrite                 (pwrite_1              ),
  .penable                (penable_1             ),
  .paddr                  (paddr_1               ),
  .pwdata                 (pwdata_1              ),
  .prdata                 (prdata_1              ),
  .pready                 (pready_1              ),
  .pslverr                (pslverr_1             )
);

////////////////////////////////////////////////////////////////////////////////
// Driving out the APB interface for Monitor Shell for monitoring register
// write/read operations
////////////////////////////////////////////////////////////////////////////////
assign APB_0_PWDATA_MON  = pwdata_0 ;
assign APB_0_PADDR_MON   = paddr_0 ;
assign APB_0_PENABLE_MON = penable_0 ;
assign APB_0_PSEL_MON    = psel_0 ;
assign APB_0_PWRITE_MON  = pwrite_0 ;
assign APB_0_PRDATA_MON  = prdata_0 ;
assign APB_0_PREADY_MON  = pready_0 ;
assign APB_0_PSLVERR_MON = pslverr_0 ;

assign APB_1_PWDATA_MON  = pwdata_1 ;
assign APB_1_PADDR_MON   = paddr_1 ;
assign APB_1_PENABLE_MON = penable_1 ;
assign APB_1_PSEL_MON    = psel_1 ;
assign APB_1_PWRITE_MON  = pwrite_1 ;
assign APB_1_PRDATA_MON  = prdata_1 ;
assign APB_1_PREADY_MON  = pready_1 ;
assign APB_1_PSLVERR_MON = pslverr_1 ;

////////////////////////////////////////////////////////////////////////////////
// Instantiating Reset pulse generator:
// This is a workaround for the issue found in pileline register in SWITCH
// between tiles
////////////////////////////////////////////////////////////////////////////////
//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_00_rst_pulse_gen
//  (
//   .clk   (AXI_00_ACLK),
//   .rst_n (AXI_00_ARESET_N),
//   .pulse (AXI_00_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_01_rst_pulse_gen
//  (
//   .clk   (AXI_01_ACLK),
//   .rst_n (AXI_01_ARESET_N),
//   .pulse (AXI_01_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_02_rst_pulse_gen
//  (
//   .clk   (AXI_02_ACLK),
//   .rst_n (AXI_02_ARESET_N),
//   .pulse (AXI_02_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_03_rst_pulse_gen
//  (
//   .clk   (AXI_03_ACLK),
//   .rst_n (AXI_03_ARESET_N),
//   .pulse (AXI_03_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_04_rst_pulse_gen
//  (
//   .clk   (AXI_04_ACLK),
//   .rst_n (AXI_04_ARESET_N),
//   .pulse (AXI_04_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_05_rst_pulse_gen
//  (
//   .clk   (AXI_05_ACLK),
//   .rst_n (AXI_05_ARESET_N),
//   .pulse (AXI_05_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_06_rst_pulse_gen
//  (
//   .clk   (AXI_06_ACLK),
//   .rst_n (AXI_06_ARESET_N),
//   .pulse (AXI_06_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_07_rst_pulse_gen
//  (
//   .clk   (AXI_07_ACLK),
//   .rst_n (AXI_07_ARESET_N),
//   .pulse (AXI_07_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_08_rst_pulse_gen
//  (
//   .clk   (AXI_08_ACLK),
//   .rst_n (AXI_08_ARESET_N),
//   .pulse (AXI_08_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_09_rst_pulse_gen
//  (
//   .clk   (AXI_09_ACLK),
//   .rst_n (AXI_09_ARESET_N),
//   .pulse (AXI_09_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_10_rst_pulse_gen
//  (
//   .clk   (AXI_10_ACLK),
//   .rst_n (AXI_10_ARESET_N),
//   .pulse (AXI_10_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_11_rst_pulse_gen
//  (
//   .clk   (AXI_11_ACLK),
//   .rst_n (AXI_11_ARESET_N),
//   .pulse (AXI_11_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_12_rst_pulse_gen
//  (
//   .clk   (AXI_12_ACLK),
//   .rst_n (AXI_12_ARESET_N),
//   .pulse (AXI_12_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_13_rst_pulse_gen
//  (
//   .clk   (AXI_13_ACLK),
//   .rst_n (AXI_13_ARESET_N),
//   .pulse (AXI_13_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_14_rst_pulse_gen
//  (
//   .clk   (AXI_14_ACLK),
//   .rst_n (AXI_14_ARESET_N),
//   .pulse (AXI_14_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_15_rst_pulse_gen
//  (
//   .clk   (AXI_15_ACLK),
//   .rst_n (AXI_15_ARESET_N),
//   .pulse (AXI_15_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_16_rst_pulse_gen
//  (
//   .clk   (AXI_16_ACLK),
//   .rst_n (AXI_16_ARESET_N),
//   .pulse (AXI_16_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_17_rst_pulse_gen
//  (
//   .clk   (AXI_17_ACLK),
//   .rst_n (AXI_17_ARESET_N),
//   .pulse (AXI_17_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_18_rst_pulse_gen
//  (
//   .clk   (AXI_18_ACLK),
//   .rst_n (AXI_18_ARESET_N),
//   .pulse (AXI_18_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_19_rst_pulse_gen
//  (
//   .clk   (AXI_19_ACLK),
//   .rst_n (AXI_19_ARESET_N),
//   .pulse (AXI_19_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_20_rst_pulse_gen
//  (
//   .clk   (AXI_20_ACLK),
//   .rst_n (AXI_20_ARESET_N),
//   .pulse (AXI_20_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_21_rst_pulse_gen
//  (
//   .clk   (AXI_21_ACLK),
//   .rst_n (AXI_21_ARESET_N),
//   .pulse (AXI_21_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_22_rst_pulse_gen
//  (
//   .clk   (AXI_22_ACLK),
//   .rst_n (AXI_22_ARESET_N),
//   .pulse (AXI_22_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_23_rst_pulse_gen
//  (
//   .clk   (AXI_23_ACLK),
//   .rst_n (AXI_23_ARESET_N),
//   .pulse (AXI_23_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_24_rst_pulse_gen
//  (
//   .clk   (AXI_24_ACLK),
//   .rst_n (AXI_24_ARESET_N),
//   .pulse (AXI_24_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_25_rst_pulse_gen
//  (
//   .clk   (AXI_25_ACLK),
//   .rst_n (AXI_25_ARESET_N),
//   .pulse (AXI_25_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_26_rst_pulse_gen
//  (
//   .clk   (AXI_26_ACLK),
//   .rst_n (AXI_26_ARESET_N),
//   .pulse (AXI_26_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_27_rst_pulse_gen
//  (
//   .clk   (AXI_27_ACLK),
//   .rst_n (AXI_27_ARESET_N),
//   .pulse (AXI_27_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_28_rst_pulse_gen
//  (
//   .clk   (AXI_28_ACLK),
//   .rst_n (AXI_28_ARESET_N),
//   .pulse (AXI_28_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_29_rst_pulse_gen
//  (
//   .clk   (AXI_29_ACLK),
//   .rst_n (AXI_29_ARESET_N),
//   .pulse (AXI_29_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_30_rst_pulse_gen
//  (
//   .clk   (AXI_30_ACLK),
//   .rst_n (AXI_30_ARESET_N),
//   .pulse (AXI_30_RST_N)
//   );

//rst_pulse_gen
// #(
//   .ASSERT_WIDTH   (AXI_RST_ASSERT_WIDTH), //= 16,
//   .DEASSERT_WIDTH (AXI_RST_DEASSERT_WIDTH), //= 2,
//   .ASSERT_VALUE   (1'b0)
//   ) axi_31_rst_pulse_gen
//  (
//   .clk   (AXI_31_ACLK),
//   .rst_n (AXI_31_ARESET_N),
//   .pulse (AXI_31_RST_N)
//   );

////////////////////////////////////////////////////////////////////////////////
// Instantiating Two stack HBM Unisim
////////////////////////////////////////////////////////////////////////////////
HBM_TWO_STACK_INTF  #(
  .CLK_SEL_00          (CLK_SEL_00),
  .CLK_SEL_01          (CLK_SEL_01),
  .CLK_SEL_02          (CLK_SEL_02),
  .CLK_SEL_03          (CLK_SEL_03),
  .CLK_SEL_04          (CLK_SEL_04),
  .CLK_SEL_05          (CLK_SEL_05),
  .CLK_SEL_06          (CLK_SEL_06),
  .CLK_SEL_07          (CLK_SEL_07),
  .CLK_SEL_08          (CLK_SEL_08),
  .CLK_SEL_09          (CLK_SEL_09),
  .CLK_SEL_10          (CLK_SEL_10),
  .CLK_SEL_11          (CLK_SEL_11),
  .CLK_SEL_12          (CLK_SEL_12),
  .CLK_SEL_13          (CLK_SEL_13),
  .CLK_SEL_14          (CLK_SEL_14),
  .CLK_SEL_15          (CLK_SEL_15),
  .CLK_SEL_16          (CLK_SEL_16),
  .CLK_SEL_17          (CLK_SEL_17),
  .CLK_SEL_18          (CLK_SEL_18),
  .CLK_SEL_19          (CLK_SEL_19),
  .CLK_SEL_20          (CLK_SEL_20),
  .CLK_SEL_21          (CLK_SEL_21),
  .CLK_SEL_22          (CLK_SEL_22),
  .CLK_SEL_23          (CLK_SEL_23),
  .CLK_SEL_24          (CLK_SEL_24),
  .CLK_SEL_25          (CLK_SEL_25),
  .CLK_SEL_26          (CLK_SEL_26),
  .CLK_SEL_27          (CLK_SEL_27),
  .CLK_SEL_28          (CLK_SEL_28),
  .CLK_SEL_29          (CLK_SEL_29),
  .CLK_SEL_30          (CLK_SEL_30),
  .CLK_SEL_31          (CLK_SEL_31),
  .MC_ENABLE_00        (MC_ENABLE_00),
  .MC_ENABLE_01        (MC_ENABLE_01),
  .MC_ENABLE_02        (MC_ENABLE_02),
  .MC_ENABLE_03        (MC_ENABLE_03),
  .MC_ENABLE_04        (MC_ENABLE_04),
  .MC_ENABLE_05        (MC_ENABLE_05),
  .MC_ENABLE_06        (MC_ENABLE_06),
  .MC_ENABLE_07        (MC_ENABLE_07),
  .MC_ENABLE_08        (MC_ENABLE_08),
  .MC_ENABLE_09        (MC_ENABLE_09),
  .MC_ENABLE_10        (MC_ENABLE_10),
  .MC_ENABLE_11        (MC_ENABLE_11),
  .MC_ENABLE_12        (MC_ENABLE_12),
  .MC_ENABLE_13        (MC_ENABLE_13),
  .MC_ENABLE_14        (MC_ENABLE_14),
  .MC_ENABLE_15        (MC_ENABLE_15),
  .MC_ENABLE_APB_00    (MC_ENABLE_APB_00),
  .MC_ENABLE_APB_01    (MC_ENABLE_APB_01),
  .PHY_ENABLE_00       (PHY_ENABLE_00),
  .PHY_ENABLE_01       (PHY_ENABLE_01),
  .PHY_ENABLE_02       (PHY_ENABLE_02),
  .PHY_ENABLE_03       (PHY_ENABLE_03),
  .PHY_ENABLE_04       (PHY_ENABLE_04),
  .PHY_ENABLE_05       (PHY_ENABLE_05),
  .PHY_ENABLE_06       (PHY_ENABLE_06),
  .PHY_ENABLE_07       (PHY_ENABLE_07),
  .PHY_ENABLE_08       (PHY_ENABLE_08),
  .PHY_ENABLE_09       (PHY_ENABLE_09),
  .PHY_ENABLE_10       (PHY_ENABLE_10),
  .PHY_ENABLE_11       (PHY_ENABLE_11),
  .PHY_ENABLE_12       (PHY_ENABLE_12),
  .PHY_ENABLE_13       (PHY_ENABLE_13),
  .PHY_ENABLE_14       (PHY_ENABLE_14),
  .PHY_ENABLE_15       (PHY_ENABLE_15),
  .PHY_ENABLE_16       (PHY_ENABLE_16),
  .PHY_ENABLE_17       (PHY_ENABLE_17),
  .PHY_ENABLE_18       (PHY_ENABLE_18),
  .PHY_ENABLE_19       (PHY_ENABLE_19),
  .PHY_ENABLE_20       (PHY_ENABLE_20),
  .PHY_ENABLE_21       (PHY_ENABLE_21),
  .PHY_ENABLE_22       (PHY_ENABLE_22),
  .PHY_ENABLE_23       (PHY_ENABLE_23),
  .PHY_ENABLE_24       (PHY_ENABLE_24),
  .PHY_ENABLE_25       (PHY_ENABLE_25),
  .PHY_ENABLE_26       (PHY_ENABLE_26),
  .PHY_ENABLE_27       (PHY_ENABLE_27),
  .PHY_ENABLE_28       (PHY_ENABLE_28),
  .PHY_ENABLE_29       (PHY_ENABLE_29),
  .PHY_ENABLE_30       (PHY_ENABLE_30),
  .PHY_ENABLE_31       (PHY_ENABLE_31),
  .PHY_ENABLE_APB_00   (PHY_ENABLE_APB_00),
  .PHY_ENABLE_APB_01   (PHY_ENABLE_APB_01),
  .DATARATE_00         (DATARATE_STACK_0),
  .DATARATE_01         (DATARATE_STACK_0),
  .DATARATE_02         (DATARATE_STACK_0),
  .DATARATE_03         (DATARATE_STACK_0),
  .DATARATE_04         (DATARATE_STACK_0),
  .DATARATE_05         (DATARATE_STACK_0),
  .DATARATE_06         (DATARATE_STACK_0),
  .DATARATE_07         (DATARATE_STACK_0),
  .DATARATE_08         (DATARATE_STACK_1),
  .DATARATE_09         (DATARATE_STACK_1),
  .DATARATE_10         (DATARATE_STACK_1),
  .DATARATE_11         (DATARATE_STACK_1),
  .DATARATE_12         (DATARATE_STACK_1),
  .DATARATE_13         (DATARATE_STACK_1),
  .DATARATE_14         (DATARATE_STACK_1),
  .DATARATE_15         (DATARATE_STACK_1),
  .READ_PERCENT_00     (READ_PERCENT_00),
  .READ_PERCENT_01     (READ_PERCENT_01),
  .READ_PERCENT_02     (READ_PERCENT_02),
  .READ_PERCENT_03     (READ_PERCENT_03),
  .READ_PERCENT_04     (READ_PERCENT_04),
  .READ_PERCENT_05     (READ_PERCENT_05),
  .READ_PERCENT_06     (READ_PERCENT_06),
  .READ_PERCENT_07     (READ_PERCENT_07),
  .READ_PERCENT_08     (READ_PERCENT_08),
  .READ_PERCENT_09     (READ_PERCENT_09),
  .READ_PERCENT_10     (READ_PERCENT_10),
  .READ_PERCENT_11     (READ_PERCENT_11),
  .READ_PERCENT_12     (READ_PERCENT_12),
  .READ_PERCENT_13     (READ_PERCENT_13),
  .READ_PERCENT_14     (READ_PERCENT_14),
  .READ_PERCENT_15     (READ_PERCENT_15),
  .READ_PERCENT_16     (READ_PERCENT_16),
  .READ_PERCENT_17     (READ_PERCENT_17),
  .READ_PERCENT_18     (READ_PERCENT_18),
  .READ_PERCENT_19     (READ_PERCENT_19),
  .READ_PERCENT_20     (READ_PERCENT_20),
  .READ_PERCENT_21     (READ_PERCENT_21),
  .READ_PERCENT_22     (READ_PERCENT_22),
  .READ_PERCENT_23     (READ_PERCENT_23),
  .READ_PERCENT_24     (READ_PERCENT_24),
  .READ_PERCENT_25     (READ_PERCENT_25),
  .READ_PERCENT_26     (READ_PERCENT_26),
  .READ_PERCENT_27     (READ_PERCENT_27),
  .READ_PERCENT_28     (READ_PERCENT_28),
  .READ_PERCENT_29     (READ_PERCENT_29),
  .READ_PERCENT_30     (READ_PERCENT_30),
  .READ_PERCENT_31     (READ_PERCENT_31),
  .WRITE_PERCENT_00    (WRITE_PERCENT_00),
  .WRITE_PERCENT_01    (WRITE_PERCENT_01),
  .WRITE_PERCENT_02    (WRITE_PERCENT_02),
  .WRITE_PERCENT_03    (WRITE_PERCENT_03),
  .WRITE_PERCENT_04    (WRITE_PERCENT_04),
  .WRITE_PERCENT_05    (WRITE_PERCENT_05),
  .WRITE_PERCENT_06    (WRITE_PERCENT_06),
  .WRITE_PERCENT_07    (WRITE_PERCENT_07),
  .WRITE_PERCENT_08    (WRITE_PERCENT_08),
  .WRITE_PERCENT_09    (WRITE_PERCENT_09),
  .WRITE_PERCENT_10    (WRITE_PERCENT_10),
  .WRITE_PERCENT_11    (WRITE_PERCENT_11),
  .WRITE_PERCENT_12    (WRITE_PERCENT_12),
  .WRITE_PERCENT_13    (WRITE_PERCENT_13),
  .WRITE_PERCENT_14    (WRITE_PERCENT_14),
  .WRITE_PERCENT_15    (WRITE_PERCENT_15),
  .WRITE_PERCENT_16    (WRITE_PERCENT_16),
  .WRITE_PERCENT_17    (WRITE_PERCENT_17),
  .WRITE_PERCENT_18    (WRITE_PERCENT_18),
  .WRITE_PERCENT_19    (WRITE_PERCENT_19),
  .WRITE_PERCENT_20    (WRITE_PERCENT_20),
  .WRITE_PERCENT_21    (WRITE_PERCENT_21),
  .WRITE_PERCENT_22    (WRITE_PERCENT_22),
  .WRITE_PERCENT_23    (WRITE_PERCENT_23),
  .WRITE_PERCENT_24    (WRITE_PERCENT_24),
  .WRITE_PERCENT_25    (WRITE_PERCENT_25),
  .WRITE_PERCENT_26    (WRITE_PERCENT_26),
  .WRITE_PERCENT_27    (WRITE_PERCENT_27),
  .WRITE_PERCENT_28    (WRITE_PERCENT_28),
  .WRITE_PERCENT_29    (WRITE_PERCENT_29),
  .WRITE_PERCENT_30    (WRITE_PERCENT_30),
  .WRITE_PERCENT_31    (WRITE_PERCENT_31),
  .PAGEHIT_PERCENT_00  (PAGEHIT_PERCENT_00),
  .PAGEHIT_PERCENT_01  (PAGEHIT_PERCENT_01),
  .SWITCH_ENABLE_00 (SWITCH_ENABLE_00),
  .SWITCH_ENABLE_01 (SWITCH_ENABLE_01)
) hbm_two_stack_intf (
  .HBM_REF_CLK_0(HBM_REF_CLK_0),
  .HBM_REF_CLK_1(HBM_REF_CLK_1),
  .AXI_00_ACLK(AXI_00_ACLK),
  .AXI_00_ARESET_N(AXI_00_ARESET_N),
  .AXI_00_ARADDR(AXI_00_ARADDR),
  .AXI_00_ARBURST(AXI_00_ARBURST),
  .AXI_00_ARID(AXI_00_ARID),
  .AXI_00_ARLEN(AXI_00_ARLEN[3:0]),
  .AXI_00_ARSIZE(AXI_00_ARSIZE),
  .AXI_00_ARVALID(AXI_00_ARVALID),
  .AXI_00_AWADDR(AXI_00_AWADDR),
  .AXI_00_AWBURST(AXI_00_AWBURST),
  .AXI_00_AWID(AXI_00_AWID),
  .AXI_00_AWLEN(AXI_00_AWLEN[3:0]),
  .AXI_00_AWSIZE(AXI_00_AWSIZE),
  .AXI_00_AWVALID(AXI_00_AWVALID),
  .AXI_00_RREADY(rready_00),
  .AXI_00_BREADY(bready_00),
  .AXI_00_WDATA(AXI_00_WDATA),
  .AXI_00_WLAST(AXI_00_WLAST),
  .AXI_00_WSTRB(AXI_00_WSTRB),
  .AXI_00_WDATA_PARITY(AXI_00_WDATA_PARITY),
  .AXI_00_WVALID(AXI_00_WVALID),
  //.AXI_00_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_00_DFI_LP_PWR_X_REQ(AXI_00_DFI_LP_PWR_X_REQ),
  .AXI_00_MC_STATUS(AXI_00_MC_STATUS),
  .AXI_00_PHY_STATUS(AXI_00_PHY_STATUS),
  .AXI_01_ACLK(AXI_01_ACLK),
  .AXI_01_ARESET_N(AXI_01_ARESET_N),
  .AXI_01_ARADDR(AXI_01_ARADDR),
  .AXI_01_ARBURST(AXI_01_ARBURST),
  .AXI_01_ARID(AXI_01_ARID),
  .AXI_01_ARLEN(AXI_01_ARLEN[3:0]),
  .AXI_01_ARSIZE(AXI_01_ARSIZE),
  .AXI_01_ARVALID(AXI_01_ARVALID),
  .AXI_01_AWADDR(AXI_01_AWADDR),
  .AXI_01_AWBURST(AXI_01_AWBURST),
  .AXI_01_AWID(AXI_01_AWID),
  .AXI_01_AWLEN(AXI_01_AWLEN[3:0]),
  .AXI_01_AWSIZE(AXI_01_AWSIZE),
  .AXI_01_AWVALID(AXI_01_AWVALID),
  .AXI_01_RREADY(rready_01),
  .AXI_01_BREADY(bready_01),
  .AXI_01_WDATA(AXI_01_WDATA),
  .AXI_01_WLAST(AXI_01_WLAST),
  .AXI_01_WSTRB(AXI_01_WSTRB),
  .AXI_01_WDATA_PARITY(AXI_01_WDATA_PARITY),
  .AXI_01_WVALID(AXI_01_WVALID),
  //.AXI_01_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_01_DFI_LP_PWR_X_REQ(AXI_01_DFI_LP_PWR_X_REQ),
  .AXI_02_ACLK(AXI_02_ACLK),
  .AXI_02_ARESET_N(AXI_02_ARESET_N),
  .AXI_02_ARADDR(AXI_02_ARADDR),
  .AXI_02_ARBURST(AXI_02_ARBURST),
  .AXI_02_ARID(AXI_02_ARID),
  .AXI_02_ARLEN(AXI_02_ARLEN[3:0]),
  .AXI_02_ARSIZE(AXI_02_ARSIZE),
  .AXI_02_ARVALID(AXI_02_ARVALID),
  .AXI_02_AWADDR(AXI_02_AWADDR),
  .AXI_02_AWBURST(AXI_02_AWBURST),
  .AXI_02_AWID(AXI_02_AWID),
  .AXI_02_AWLEN(AXI_02_AWLEN[3:0]),
  .AXI_02_AWSIZE(AXI_02_AWSIZE),
  .AXI_02_AWVALID(AXI_02_AWVALID),
  .AXI_02_RREADY(rready_02),
  .AXI_02_BREADY(bready_02),
  .AXI_02_WDATA(AXI_02_WDATA),
  .AXI_02_WLAST(AXI_02_WLAST),
  .AXI_02_WSTRB(AXI_02_WSTRB),
  .AXI_02_WDATA_PARITY(AXI_02_WDATA_PARITY),
  .AXI_02_WVALID(AXI_02_WVALID),
  //.AXI_02_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_02_DFI_LP_PWR_X_REQ(AXI_02_DFI_LP_PWR_X_REQ),
  .AXI_02_MC_STATUS(AXI_02_MC_STATUS),
  .AXI_02_PHY_STATUS(AXI_02_PHY_STATUS),
  .AXI_03_ACLK(AXI_03_ACLK),
  .AXI_03_ARESET_N(AXI_03_ARESET_N),
  .AXI_03_ARADDR(AXI_03_ARADDR),
  .AXI_03_ARBURST(AXI_03_ARBURST),
  .AXI_03_ARID(AXI_03_ARID),
  .AXI_03_ARLEN(AXI_03_ARLEN[3:0]),
  .AXI_03_ARSIZE(AXI_03_ARSIZE),
  .AXI_03_ARVALID(AXI_03_ARVALID),
  .AXI_03_AWADDR(AXI_03_AWADDR),
  .AXI_03_AWBURST(AXI_03_AWBURST),
  .AXI_03_AWID(AXI_03_AWID),
  .AXI_03_AWLEN(AXI_03_AWLEN[3:0]),
  .AXI_03_AWSIZE(AXI_03_AWSIZE),
  .AXI_03_AWVALID(AXI_03_AWVALID),
  .AXI_03_RREADY(rready_03),
  .AXI_03_BREADY(bready_03),
  .AXI_03_WDATA(AXI_03_WDATA),
  .AXI_03_WLAST(AXI_03_WLAST),
  .AXI_03_WSTRB(AXI_03_WSTRB),
  .AXI_03_WDATA_PARITY(AXI_03_WDATA_PARITY),
  .AXI_03_WVALID(AXI_03_WVALID),
  //.AXI_03_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_03_DFI_LP_PWR_X_REQ(AXI_03_DFI_LP_PWR_X_REQ),
  .AXI_04_ACLK(AXI_04_ACLK),
  .AXI_04_ARESET_N(AXI_04_ARESET_N),
  .AXI_04_ARADDR(AXI_04_ARADDR),
  .AXI_04_ARBURST(AXI_04_ARBURST),
  .AXI_04_ARID(AXI_04_ARID),
  .AXI_04_ARLEN(AXI_04_ARLEN[3:0]),
  .AXI_04_ARSIZE(AXI_04_ARSIZE),
  .AXI_04_ARVALID(AXI_04_ARVALID),
  .AXI_04_AWADDR(AXI_04_AWADDR),
  .AXI_04_AWBURST(AXI_04_AWBURST),
  .AXI_04_AWID(AXI_04_AWID),
  .AXI_04_AWLEN(AXI_04_AWLEN[3:0]),
  .AXI_04_AWSIZE(AXI_04_AWSIZE),
  .AXI_04_AWVALID(AXI_04_AWVALID),
  .AXI_04_RREADY(rready_04),
  .AXI_04_BREADY(bready_04),
  .AXI_04_WDATA(AXI_04_WDATA),
  .AXI_04_WLAST(AXI_04_WLAST),
  .AXI_04_WSTRB(AXI_04_WSTRB),
  .AXI_04_WDATA_PARITY(AXI_04_WDATA_PARITY),
  .AXI_04_WVALID(AXI_04_WVALID),
  //.AXI_04_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_04_DFI_LP_PWR_X_REQ(AXI_04_DFI_LP_PWR_X_REQ),
  .AXI_04_MC_STATUS(AXI_04_MC_STATUS),
  .AXI_04_PHY_STATUS(AXI_04_PHY_STATUS),
  .AXI_05_ACLK(AXI_05_ACLK),
  .AXI_05_ARESET_N(AXI_05_ARESET_N),
  .AXI_05_ARADDR(AXI_05_ARADDR),
  .AXI_05_ARBURST(AXI_05_ARBURST),
  .AXI_05_ARID(AXI_05_ARID),
  .AXI_05_ARLEN(AXI_05_ARLEN[3:0]),
  .AXI_05_ARSIZE(AXI_05_ARSIZE),
  .AXI_05_ARVALID(AXI_05_ARVALID),
  .AXI_05_AWADDR(AXI_05_AWADDR),
  .AXI_05_AWBURST(AXI_05_AWBURST),
  .AXI_05_AWID(AXI_05_AWID),
  .AXI_05_AWLEN(AXI_05_AWLEN[3:0]),
  .AXI_05_AWSIZE(AXI_05_AWSIZE),
  .AXI_05_AWVALID(AXI_05_AWVALID),
  .AXI_05_RREADY(rready_05),
  .AXI_05_BREADY(bready_05),
  .AXI_05_WDATA(AXI_05_WDATA),
  .AXI_05_WLAST(AXI_05_WLAST),
  .AXI_05_WSTRB(AXI_05_WSTRB),
  .AXI_05_WDATA_PARITY(AXI_05_WDATA_PARITY),
  .AXI_05_WVALID(AXI_05_WVALID),
  //.AXI_05_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_05_DFI_LP_PWR_X_REQ(AXI_05_DFI_LP_PWR_X_REQ),
  .AXI_06_ACLK(AXI_06_ACLK),
  .AXI_06_ARESET_N(AXI_06_ARESET_N),
  .AXI_06_ARADDR(AXI_06_ARADDR),
  .AXI_06_ARBURST(AXI_06_ARBURST),
  .AXI_06_ARID(AXI_06_ARID),
  .AXI_06_ARLEN(AXI_06_ARLEN[3:0]),
  .AXI_06_ARSIZE(AXI_06_ARSIZE),
  .AXI_06_ARVALID(AXI_06_ARVALID),
  .AXI_06_AWADDR(AXI_06_AWADDR),
  .AXI_06_AWBURST(AXI_06_AWBURST),
  .AXI_06_AWID(AXI_06_AWID),
  .AXI_06_AWLEN(AXI_06_AWLEN[3:0]),
  .AXI_06_AWSIZE(AXI_06_AWSIZE),
  .AXI_06_AWVALID(AXI_06_AWVALID),
  .AXI_06_RREADY(rready_06),
  .AXI_06_BREADY(bready_06),
  .AXI_06_WDATA(AXI_06_WDATA),
  .AXI_06_WLAST(AXI_06_WLAST),
  .AXI_06_WSTRB(AXI_06_WSTRB),
  .AXI_06_WDATA_PARITY(AXI_06_WDATA_PARITY),
  .AXI_06_WVALID(AXI_06_WVALID),
  //.AXI_06_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_06_DFI_LP_PWR_X_REQ(AXI_06_DFI_LP_PWR_X_REQ),
  .AXI_06_MC_STATUS(AXI_06_MC_STATUS),
  .AXI_06_PHY_STATUS(AXI_06_PHY_STATUS),
  .AXI_07_ACLK(AXI_07_ACLK),
  .AXI_07_ARESET_N(AXI_07_ARESET_N),
  .AXI_07_ARADDR(AXI_07_ARADDR),
  .AXI_07_ARBURST(AXI_07_ARBURST),
  .AXI_07_ARID(AXI_07_ARID),
  .AXI_07_ARLEN(AXI_07_ARLEN[3:0]),
  .AXI_07_ARSIZE(AXI_07_ARSIZE),
  .AXI_07_ARVALID(AXI_07_ARVALID),
  .AXI_07_AWADDR(AXI_07_AWADDR),
  .AXI_07_AWBURST(AXI_07_AWBURST),
  .AXI_07_AWID(AXI_07_AWID),
  .AXI_07_AWLEN(AXI_07_AWLEN[3:0]),
  .AXI_07_AWSIZE(AXI_07_AWSIZE),
  .AXI_07_AWVALID(AXI_07_AWVALID),
  .AXI_07_RREADY(rready_07),
  .AXI_07_BREADY(bready_07),
  .AXI_07_WDATA(AXI_07_WDATA),
  .AXI_07_WLAST(AXI_07_WLAST),
  .AXI_07_WSTRB(AXI_07_WSTRB),
  .AXI_07_WDATA_PARITY(AXI_07_WDATA_PARITY),
  .AXI_07_WVALID(AXI_07_WVALID),
  //.AXI_07_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_07_DFI_LP_PWR_X_REQ(AXI_07_DFI_LP_PWR_X_REQ),
  .AXI_08_ACLK(AXI_08_ACLK),
  .AXI_08_ARESET_N(AXI_08_ARESET_N),
  .AXI_08_ARADDR(AXI_08_ARADDR),
  .AXI_08_ARBURST(AXI_08_ARBURST),
  .AXI_08_ARID(AXI_08_ARID),
  .AXI_08_ARLEN(AXI_08_ARLEN[3:0]),
  .AXI_08_ARSIZE(AXI_08_ARSIZE),
  .AXI_08_ARVALID(AXI_08_ARVALID),
  .AXI_08_AWADDR(AXI_08_AWADDR),
  .AXI_08_AWBURST(AXI_08_AWBURST),
  .AXI_08_AWID(AXI_08_AWID),
  .AXI_08_AWLEN(AXI_08_AWLEN[3:0]),
  .AXI_08_AWSIZE(AXI_08_AWSIZE),
  .AXI_08_AWVALID(AXI_08_AWVALID),
  .AXI_08_RREADY(rready_08),
  .AXI_08_BREADY(bready_08),
  .AXI_08_WDATA(AXI_08_WDATA),
  .AXI_08_WLAST(AXI_08_WLAST),
  .AXI_08_WSTRB(AXI_08_WSTRB),
  .AXI_08_WDATA_PARITY(AXI_08_WDATA_PARITY),
  .AXI_08_WVALID(AXI_08_WVALID),
  //.AXI_08_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_08_DFI_LP_PWR_X_REQ(AXI_08_DFI_LP_PWR_X_REQ),
  .AXI_08_MC_STATUS(AXI_08_MC_STATUS),
  .AXI_08_PHY_STATUS(AXI_08_PHY_STATUS),
  .AXI_09_ACLK(AXI_09_ACLK),
  .AXI_09_ARESET_N(AXI_09_ARESET_N),
  .AXI_09_ARADDR(AXI_09_ARADDR),
  .AXI_09_ARBURST(AXI_09_ARBURST),
  .AXI_09_ARID(AXI_09_ARID),
  .AXI_09_ARLEN(AXI_09_ARLEN[3:0]),
  .AXI_09_ARSIZE(AXI_09_ARSIZE),
  .AXI_09_ARVALID(AXI_09_ARVALID),
  .AXI_09_AWADDR(AXI_09_AWADDR),
  .AXI_09_AWBURST(AXI_09_AWBURST),
  .AXI_09_AWID(AXI_09_AWID),
  .AXI_09_AWLEN(AXI_09_AWLEN[3:0]),
  .AXI_09_AWSIZE(AXI_09_AWSIZE),
  .AXI_09_AWVALID(AXI_09_AWVALID),
  .AXI_09_RREADY(rready_09),
  .AXI_09_BREADY(bready_09),
  .AXI_09_WDATA(AXI_09_WDATA),
  .AXI_09_WLAST(AXI_09_WLAST),
  .AXI_09_WSTRB(AXI_09_WSTRB),
  .AXI_09_WDATA_PARITY(AXI_09_WDATA_PARITY),
  .AXI_09_WVALID(AXI_09_WVALID),
  //.AXI_09_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_09_DFI_LP_PWR_X_REQ(AXI_09_DFI_LP_PWR_X_REQ),
  .AXI_10_ACLK(AXI_10_ACLK),
  .AXI_10_ARESET_N(AXI_10_ARESET_N),
  .AXI_10_ARADDR(AXI_10_ARADDR),
  .AXI_10_ARBURST(AXI_10_ARBURST),
  .AXI_10_ARID(AXI_10_ARID),
  .AXI_10_ARLEN(AXI_10_ARLEN[3:0]),
  .AXI_10_ARSIZE(AXI_10_ARSIZE),
  .AXI_10_ARVALID(AXI_10_ARVALID),
  .AXI_10_AWADDR(AXI_10_AWADDR),
  .AXI_10_AWBURST(AXI_10_AWBURST),
  .AXI_10_AWID(AXI_10_AWID),
  .AXI_10_AWLEN(AXI_10_AWLEN[3:0]),
  .AXI_10_AWSIZE(AXI_10_AWSIZE),
  .AXI_10_AWVALID(AXI_10_AWVALID),
  .AXI_10_RREADY(rready_10),
  .AXI_10_BREADY(bready_10),
  .AXI_10_WDATA(AXI_10_WDATA),
  .AXI_10_WLAST(AXI_10_WLAST),
  .AXI_10_WSTRB(AXI_10_WSTRB),
  .AXI_10_WDATA_PARITY(AXI_10_WDATA_PARITY),
  .AXI_10_WVALID(AXI_10_WVALID),
  //.AXI_10_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_10_DFI_LP_PWR_X_REQ(AXI_10_DFI_LP_PWR_X_REQ),
  .AXI_10_MC_STATUS(AXI_10_MC_STATUS),
  .AXI_10_PHY_STATUS(AXI_10_PHY_STATUS),
  .AXI_11_ACLK(AXI_11_ACLK),
  .AXI_11_ARESET_N(AXI_11_ARESET_N),
  .AXI_11_ARADDR(AXI_11_ARADDR),
  .AXI_11_ARBURST(AXI_11_ARBURST),
  .AXI_11_ARID(AXI_11_ARID),
  .AXI_11_ARLEN(AXI_11_ARLEN[3:0]),
  .AXI_11_ARSIZE(AXI_11_ARSIZE),
  .AXI_11_ARVALID(AXI_11_ARVALID),
  .AXI_11_AWADDR(AXI_11_AWADDR),
  .AXI_11_AWBURST(AXI_11_AWBURST),
  .AXI_11_AWID(AXI_11_AWID),
  .AXI_11_AWLEN(AXI_11_AWLEN[3:0]),
  .AXI_11_AWSIZE(AXI_11_AWSIZE),
  .AXI_11_AWVALID(AXI_11_AWVALID),
  .AXI_11_RREADY(rready_11),
  .AXI_11_BREADY(bready_11),
  .AXI_11_WDATA(AXI_11_WDATA),
  .AXI_11_WLAST(AXI_11_WLAST),
  .AXI_11_WSTRB(AXI_11_WSTRB),
  .AXI_11_WDATA_PARITY(AXI_11_WDATA_PARITY),
  .AXI_11_WVALID(AXI_11_WVALID),
  //.AXI_11_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_11_DFI_LP_PWR_X_REQ(AXI_11_DFI_LP_PWR_X_REQ),
  .AXI_12_ACLK(AXI_12_ACLK),
  .AXI_12_ARESET_N(AXI_12_ARESET_N),
  .AXI_12_ARADDR(AXI_12_ARADDR),
  .AXI_12_ARBURST(AXI_12_ARBURST),
  .AXI_12_ARID(AXI_12_ARID),
  .AXI_12_ARLEN(AXI_12_ARLEN[3:0]),
  .AXI_12_ARSIZE(AXI_12_ARSIZE),
  .AXI_12_ARVALID(AXI_12_ARVALID),
  .AXI_12_AWADDR(AXI_12_AWADDR),
  .AXI_12_AWBURST(AXI_12_AWBURST),
  .AXI_12_AWID(AXI_12_AWID),
  .AXI_12_AWLEN(AXI_12_AWLEN[3:0]),
  .AXI_12_AWSIZE(AXI_12_AWSIZE),
  .AXI_12_AWVALID(AXI_12_AWVALID),
  .AXI_12_RREADY(rready_12),
  .AXI_12_BREADY(bready_12),
  .AXI_12_WDATA(AXI_12_WDATA),
  .AXI_12_WLAST(AXI_12_WLAST),
  .AXI_12_WSTRB(AXI_12_WSTRB),
  .AXI_12_WDATA_PARITY(AXI_12_WDATA_PARITY),
  .AXI_12_WVALID(AXI_12_WVALID),
  //.AXI_12_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_12_DFI_LP_PWR_X_REQ(AXI_12_DFI_LP_PWR_X_REQ),
  .AXI_12_MC_STATUS(AXI_12_MC_STATUS),
  .AXI_12_PHY_STATUS(AXI_12_PHY_STATUS),
  .AXI_13_ACLK(AXI_13_ACLK),
  .AXI_13_ARESET_N(AXI_13_ARESET_N),
  .AXI_13_ARADDR(AXI_13_ARADDR),
  .AXI_13_ARBURST(AXI_13_ARBURST),
  .AXI_13_ARID(AXI_13_ARID),
  .AXI_13_ARLEN(AXI_13_ARLEN[3:0]),
  .AXI_13_ARSIZE(AXI_13_ARSIZE),
  .AXI_13_ARVALID(AXI_13_ARVALID),
  .AXI_13_AWADDR(AXI_13_AWADDR),
  .AXI_13_AWBURST(AXI_13_AWBURST),
  .AXI_13_AWID(AXI_13_AWID),
  .AXI_13_AWLEN(AXI_13_AWLEN[3:0]),
  .AXI_13_AWSIZE(AXI_13_AWSIZE),
  .AXI_13_AWVALID(AXI_13_AWVALID),
  .AXI_13_RREADY(rready_13),
  .AXI_13_BREADY(bready_13),
  .AXI_13_WDATA(AXI_13_WDATA),
  .AXI_13_WLAST(AXI_13_WLAST),
  .AXI_13_WSTRB(AXI_13_WSTRB),
  .AXI_13_WDATA_PARITY(AXI_13_WDATA_PARITY),
  .AXI_13_WVALID(AXI_13_WVALID),
  //.AXI_13_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_13_DFI_LP_PWR_X_REQ(AXI_13_DFI_LP_PWR_X_REQ),
  .AXI_14_ACLK(AXI_14_ACLK),
  .AXI_14_ARESET_N(AXI_14_ARESET_N),
  .AXI_14_ARADDR(AXI_14_ARADDR),
  .AXI_14_ARBURST(AXI_14_ARBURST),
  .AXI_14_ARID(AXI_14_ARID),
  .AXI_14_ARLEN(AXI_14_ARLEN[3:0]),
  .AXI_14_ARSIZE(AXI_14_ARSIZE),
  .AXI_14_ARVALID(AXI_14_ARVALID),
  .AXI_14_AWADDR(AXI_14_AWADDR),
  .AXI_14_AWBURST(AXI_14_AWBURST),
  .AXI_14_AWID(AXI_14_AWID),
  .AXI_14_AWLEN(AXI_14_AWLEN[3:0]),
  .AXI_14_AWSIZE(AXI_14_AWSIZE),
  .AXI_14_AWVALID(AXI_14_AWVALID),
  .AXI_14_RREADY(rready_14),
  .AXI_14_BREADY(bready_14),
  .AXI_14_WDATA(AXI_14_WDATA),
  .AXI_14_WLAST(AXI_14_WLAST),
  .AXI_14_WSTRB(AXI_14_WSTRB),
  .AXI_14_WDATA_PARITY(AXI_14_WDATA_PARITY),
  .AXI_14_WVALID(AXI_14_WVALID),
  //.AXI_14_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_14_DFI_LP_PWR_X_REQ(AXI_14_DFI_LP_PWR_X_REQ),
  .AXI_14_MC_STATUS(AXI_14_MC_STATUS),
  .AXI_14_PHY_STATUS(AXI_14_PHY_STATUS),
  .AXI_15_ACLK(AXI_15_ACLK),
  .AXI_15_ARESET_N(AXI_15_ARESET_N),
  .AXI_15_ARADDR(AXI_15_ARADDR),
  .AXI_15_ARBURST(AXI_15_ARBURST),
  .AXI_15_ARID(AXI_15_ARID),
  .AXI_15_ARLEN(AXI_15_ARLEN[3:0]),
  .AXI_15_ARSIZE(AXI_15_ARSIZE),
  .AXI_15_ARVALID(AXI_15_ARVALID),
  .AXI_15_AWADDR(AXI_15_AWADDR),
  .AXI_15_AWBURST(AXI_15_AWBURST),
  .AXI_15_AWID(AXI_15_AWID),
  .AXI_15_AWLEN(AXI_15_AWLEN[3:0]),
  .AXI_15_AWSIZE(AXI_15_AWSIZE),
  .AXI_15_AWVALID(AXI_15_AWVALID),
  .AXI_15_RREADY(rready_15),
  .AXI_15_BREADY(bready_15),
  .AXI_15_WDATA(AXI_15_WDATA),
  .AXI_15_WLAST(AXI_15_WLAST),
  .AXI_15_WSTRB(AXI_15_WSTRB),
  .AXI_15_WDATA_PARITY(AXI_15_WDATA_PARITY),
  .AXI_15_WVALID(AXI_15_WVALID),
  //.AXI_15_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_15_DFI_LP_PWR_X_REQ(AXI_15_DFI_LP_PWR_X_REQ),
  .AXI_16_ACLK(AXI_16_ACLK),
  .AXI_16_ARESET_N(AXI_16_ARESET_N),
  .AXI_16_ARADDR(AXI_16_ARADDR),
  .AXI_16_ARBURST(AXI_16_ARBURST),
  .AXI_16_ARID(AXI_16_ARID),
  .AXI_16_ARLEN(AXI_16_ARLEN[3:0]),
  .AXI_16_ARSIZE(AXI_16_ARSIZE),
  .AXI_16_ARVALID(AXI_16_ARVALID),
  .AXI_16_AWADDR(AXI_16_AWADDR),
  .AXI_16_AWBURST(AXI_16_AWBURST),
  .AXI_16_AWID(AXI_16_AWID),
  .AXI_16_AWLEN(AXI_16_AWLEN[3:0]),
  .AXI_16_AWSIZE(AXI_16_AWSIZE),
  .AXI_16_AWVALID(AXI_16_AWVALID),
  .AXI_16_RREADY(rready_16),
  .AXI_16_BREADY(bready_16),
  .AXI_16_WDATA(AXI_16_WDATA),
  .AXI_16_WLAST(AXI_16_WLAST),
  .AXI_16_WSTRB(AXI_16_WSTRB),
  .AXI_16_WDATA_PARITY(AXI_16_WDATA_PARITY),
  .AXI_16_WVALID(AXI_16_WVALID),
  //.AXI_16_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_16_DFI_LP_PWR_X_REQ(AXI_16_DFI_LP_PWR_X_REQ),
  .AXI_16_MC_STATUS(AXI_16_MC_STATUS),
  .AXI_16_PHY_STATUS(AXI_16_PHY_STATUS),
  .AXI_17_ACLK(AXI_17_ACLK),
  .AXI_17_ARESET_N(AXI_17_ARESET_N),
  .AXI_17_ARADDR(AXI_17_ARADDR),
  .AXI_17_ARBURST(AXI_17_ARBURST),
  .AXI_17_ARID(AXI_17_ARID),
  .AXI_17_ARLEN(AXI_17_ARLEN[3:0]),
  .AXI_17_ARSIZE(AXI_17_ARSIZE),
  .AXI_17_ARVALID(AXI_17_ARVALID),
  .AXI_17_AWADDR(AXI_17_AWADDR),
  .AXI_17_AWBURST(AXI_17_AWBURST),
  .AXI_17_AWID(AXI_17_AWID),
  .AXI_17_AWLEN(AXI_17_AWLEN[3:0]),
  .AXI_17_AWSIZE(AXI_17_AWSIZE),
  .AXI_17_AWVALID(AXI_17_AWVALID),
  .AXI_17_RREADY(rready_17),
  .AXI_17_BREADY(bready_17),
  .AXI_17_WDATA(AXI_17_WDATA),
  .AXI_17_WLAST(AXI_17_WLAST),
  .AXI_17_WSTRB(AXI_17_WSTRB),
  .AXI_17_WDATA_PARITY(AXI_17_WDATA_PARITY),
  .AXI_17_WVALID(AXI_17_WVALID),
  //.AXI_17_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_17_DFI_LP_PWR_X_REQ(AXI_17_DFI_LP_PWR_X_REQ),
  .AXI_18_ACLK(AXI_18_ACLK),
  .AXI_18_ARESET_N(AXI_18_ARESET_N),
  .AXI_18_ARADDR(AXI_18_ARADDR),
  .AXI_18_ARBURST(AXI_18_ARBURST),
  .AXI_18_ARID(AXI_18_ARID),
  .AXI_18_ARLEN(AXI_18_ARLEN[3:0]),
  .AXI_18_ARSIZE(AXI_18_ARSIZE),
  .AXI_18_ARVALID(AXI_18_ARVALID),
  .AXI_18_AWADDR(AXI_18_AWADDR),
  .AXI_18_AWBURST(AXI_18_AWBURST),
  .AXI_18_AWID(AXI_18_AWID),
  .AXI_18_AWLEN(AXI_18_AWLEN[3:0]),
  .AXI_18_AWSIZE(AXI_18_AWSIZE),
  .AXI_18_AWVALID(AXI_18_AWVALID),
  .AXI_18_RREADY(rready_18),
  .AXI_18_BREADY(bready_18),
  .AXI_18_WDATA(AXI_18_WDATA),
  .AXI_18_WLAST(AXI_18_WLAST),
  .AXI_18_WSTRB(AXI_18_WSTRB),
  .AXI_18_WDATA_PARITY(AXI_18_WDATA_PARITY),
  .AXI_18_WVALID(AXI_18_WVALID),
  //.AXI_18_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_18_DFI_LP_PWR_X_REQ(AXI_18_DFI_LP_PWR_X_REQ),
  .AXI_18_MC_STATUS(AXI_18_MC_STATUS),
  .AXI_18_PHY_STATUS(AXI_18_PHY_STATUS),
  .AXI_19_ACLK(AXI_19_ACLK),
  .AXI_19_ARESET_N(AXI_19_ARESET_N),
  .AXI_19_ARADDR(AXI_19_ARADDR),
  .AXI_19_ARBURST(AXI_19_ARBURST),
  .AXI_19_ARID(AXI_19_ARID),
  .AXI_19_ARLEN(AXI_19_ARLEN[3:0]),
  .AXI_19_ARSIZE(AXI_19_ARSIZE),
  .AXI_19_ARVALID(AXI_19_ARVALID),
  .AXI_19_AWADDR(AXI_19_AWADDR),
  .AXI_19_AWBURST(AXI_19_AWBURST),
  .AXI_19_AWID(AXI_19_AWID),
  .AXI_19_AWLEN(AXI_19_AWLEN[3:0]),
  .AXI_19_AWSIZE(AXI_19_AWSIZE),
  .AXI_19_AWVALID(AXI_19_AWVALID),
  .AXI_19_RREADY(rready_19),
  .AXI_19_BREADY(bready_19),
  .AXI_19_WDATA(AXI_19_WDATA),
  .AXI_19_WLAST(AXI_19_WLAST),
  .AXI_19_WSTRB(AXI_19_WSTRB),
  .AXI_19_WDATA_PARITY(AXI_19_WDATA_PARITY),
  .AXI_19_WVALID(AXI_19_WVALID),
  //.AXI_19_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_19_DFI_LP_PWR_X_REQ(AXI_19_DFI_LP_PWR_X_REQ),
  .AXI_20_ACLK(AXI_20_ACLK),
  .AXI_20_ARESET_N(AXI_20_ARESET_N),
  .AXI_20_ARADDR(AXI_20_ARADDR),
  .AXI_20_ARBURST(AXI_20_ARBURST),
  .AXI_20_ARID(AXI_20_ARID),
  .AXI_20_ARLEN(AXI_20_ARLEN[3:0]),
  .AXI_20_ARSIZE(AXI_20_ARSIZE),
  .AXI_20_ARVALID(AXI_20_ARVALID),
  .AXI_20_AWADDR(AXI_20_AWADDR),
  .AXI_20_AWBURST(AXI_20_AWBURST),
  .AXI_20_AWID(AXI_20_AWID),
  .AXI_20_AWLEN(AXI_20_AWLEN[3:0]),
  .AXI_20_AWSIZE(AXI_20_AWSIZE),
  .AXI_20_AWVALID(AXI_20_AWVALID),
  .AXI_20_RREADY(rready_20),
  .AXI_20_BREADY(bready_20),
  .AXI_20_WDATA(AXI_20_WDATA),
  .AXI_20_WLAST(AXI_20_WLAST),
  .AXI_20_WSTRB(AXI_20_WSTRB),
  .AXI_20_WDATA_PARITY(AXI_20_WDATA_PARITY),
  .AXI_20_WVALID(AXI_20_WVALID),
  //.AXI_20_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_20_DFI_LP_PWR_X_REQ(AXI_20_DFI_LP_PWR_X_REQ),
  .AXI_20_MC_STATUS(AXI_20_MC_STATUS),
  .AXI_20_PHY_STATUS(AXI_20_PHY_STATUS),
  .AXI_21_ACLK(AXI_21_ACLK),
  .AXI_21_ARESET_N(AXI_21_ARESET_N),
  .AXI_21_ARADDR(AXI_21_ARADDR),
  .AXI_21_ARBURST(AXI_21_ARBURST),
  .AXI_21_ARID(AXI_21_ARID),
  .AXI_21_ARLEN(AXI_21_ARLEN[3:0]),
  .AXI_21_ARSIZE(AXI_21_ARSIZE),
  .AXI_21_ARVALID(AXI_21_ARVALID),
  .AXI_21_AWADDR(AXI_21_AWADDR),
  .AXI_21_AWBURST(AXI_21_AWBURST),
  .AXI_21_AWID(AXI_21_AWID),
  .AXI_21_AWLEN(AXI_21_AWLEN[3:0]),
  .AXI_21_AWSIZE(AXI_21_AWSIZE),
  .AXI_21_AWVALID(AXI_21_AWVALID),
  .AXI_21_RREADY(rready_21),
  .AXI_21_BREADY(bready_21),
  .AXI_21_WDATA(AXI_21_WDATA),
  .AXI_21_WLAST(AXI_21_WLAST),
  .AXI_21_WSTRB(AXI_21_WSTRB),
  .AXI_21_WDATA_PARITY(AXI_21_WDATA_PARITY),
  .AXI_21_WVALID(AXI_21_WVALID),
  //.AXI_21_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_21_DFI_LP_PWR_X_REQ(AXI_21_DFI_LP_PWR_X_REQ),
  .AXI_22_ACLK(AXI_22_ACLK),
  .AXI_22_ARESET_N(AXI_22_ARESET_N),
  .AXI_22_ARADDR(AXI_22_ARADDR),
  .AXI_22_ARBURST(AXI_22_ARBURST),
  .AXI_22_ARID(AXI_22_ARID),
  .AXI_22_ARLEN(AXI_22_ARLEN[3:0]),
  .AXI_22_ARSIZE(AXI_22_ARSIZE),
  .AXI_22_ARVALID(AXI_22_ARVALID),
  .AXI_22_AWADDR(AXI_22_AWADDR),
  .AXI_22_AWBURST(AXI_22_AWBURST),
  .AXI_22_AWID(AXI_22_AWID),
  .AXI_22_AWLEN(AXI_22_AWLEN[3:0]),
  .AXI_22_AWSIZE(AXI_22_AWSIZE),
  .AXI_22_AWVALID(AXI_22_AWVALID),
  .AXI_22_RREADY(rready_22),
  .AXI_22_BREADY(bready_22),
  .AXI_22_WDATA(AXI_22_WDATA),
  .AXI_22_WLAST(AXI_22_WLAST),
  .AXI_22_WSTRB(AXI_22_WSTRB),
  .AXI_22_WDATA_PARITY(AXI_22_WDATA_PARITY),
  .AXI_22_WVALID(AXI_22_WVALID),
  //.AXI_22_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_22_DFI_LP_PWR_X_REQ(AXI_22_DFI_LP_PWR_X_REQ),
  .AXI_22_MC_STATUS(AXI_22_MC_STATUS),
  .AXI_22_PHY_STATUS(AXI_22_PHY_STATUS),
  .AXI_23_ACLK(AXI_23_ACLK),
  .AXI_23_ARESET_N(AXI_23_ARESET_N),
  .AXI_23_ARADDR(AXI_23_ARADDR),
  .AXI_23_ARBURST(AXI_23_ARBURST),
  .AXI_23_ARID(AXI_23_ARID),
  .AXI_23_ARLEN(AXI_23_ARLEN[3:0]),
  .AXI_23_ARSIZE(AXI_23_ARSIZE),
  .AXI_23_ARVALID(AXI_23_ARVALID),
  .AXI_23_AWADDR(AXI_23_AWADDR),
  .AXI_23_AWBURST(AXI_23_AWBURST),
  .AXI_23_AWID(AXI_23_AWID),
  .AXI_23_AWLEN(AXI_23_AWLEN[3:0]),
  .AXI_23_AWSIZE(AXI_23_AWSIZE),
  .AXI_23_AWVALID(AXI_23_AWVALID),
  .AXI_23_RREADY(rready_23),
  .AXI_23_BREADY(bready_23),
  .AXI_23_WDATA(AXI_23_WDATA),
  .AXI_23_WLAST(AXI_23_WLAST),
  .AXI_23_WSTRB(AXI_23_WSTRB),
  .AXI_23_WDATA_PARITY(AXI_23_WDATA_PARITY),
  .AXI_23_WVALID(AXI_23_WVALID),
  //.AXI_23_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_23_DFI_LP_PWR_X_REQ(AXI_23_DFI_LP_PWR_X_REQ),
  .AXI_24_ACLK(AXI_24_ACLK),
  .AXI_24_ARESET_N(AXI_24_ARESET_N),
  .AXI_24_ARADDR(AXI_24_ARADDR),
  .AXI_24_ARBURST(AXI_24_ARBURST),
  .AXI_24_ARID(AXI_24_ARID),
  .AXI_24_ARLEN(AXI_24_ARLEN[3:0]),
  .AXI_24_ARSIZE(AXI_24_ARSIZE),
  .AXI_24_ARVALID(AXI_24_ARVALID),
  .AXI_24_AWADDR(AXI_24_AWADDR),
  .AXI_24_AWBURST(AXI_24_AWBURST),
  .AXI_24_AWID(AXI_24_AWID),
  .AXI_24_AWLEN(AXI_24_AWLEN[3:0]),
  .AXI_24_AWSIZE(AXI_24_AWSIZE),
  .AXI_24_AWVALID(AXI_24_AWVALID),
  .AXI_24_RREADY(rready_24),
  .AXI_24_BREADY(bready_24),
  .AXI_24_WDATA(AXI_24_WDATA),
  .AXI_24_WLAST(AXI_24_WLAST),
  .AXI_24_WSTRB(AXI_24_WSTRB),
  .AXI_24_WDATA_PARITY(AXI_24_WDATA_PARITY),
  .AXI_24_WVALID(AXI_24_WVALID),
  //.AXI_24_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_24_DFI_LP_PWR_X_REQ(AXI_24_DFI_LP_PWR_X_REQ),
  .AXI_24_MC_STATUS(AXI_24_MC_STATUS),
  .AXI_24_PHY_STATUS(AXI_24_PHY_STATUS),
  .AXI_25_ACLK(AXI_25_ACLK),
  .AXI_25_ARESET_N(AXI_25_ARESET_N),
  .AXI_25_ARADDR(AXI_25_ARADDR),
  .AXI_25_ARBURST(AXI_25_ARBURST),
  .AXI_25_ARID(AXI_25_ARID),
  .AXI_25_ARLEN(AXI_25_ARLEN[3:0]),
  .AXI_25_ARSIZE(AXI_25_ARSIZE),
  .AXI_25_ARVALID(AXI_25_ARVALID),
  .AXI_25_AWADDR(AXI_25_AWADDR),
  .AXI_25_AWBURST(AXI_25_AWBURST),
  .AXI_25_AWID(AXI_25_AWID),
  .AXI_25_AWLEN(AXI_25_AWLEN[3:0]),
  .AXI_25_AWSIZE(AXI_25_AWSIZE),
  .AXI_25_AWVALID(AXI_25_AWVALID),
  .AXI_25_RREADY(rready_25),
  .AXI_25_BREADY(bready_25),
  .AXI_25_WDATA(AXI_25_WDATA),
  .AXI_25_WLAST(AXI_25_WLAST),
  .AXI_25_WSTRB(AXI_25_WSTRB),
  .AXI_25_WDATA_PARITY(AXI_25_WDATA_PARITY),
  .AXI_25_WVALID(AXI_25_WVALID),
  //.AXI_25_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_25_DFI_LP_PWR_X_REQ(AXI_25_DFI_LP_PWR_X_REQ),
  .AXI_26_ACLK(AXI_26_ACLK),
  .AXI_26_ARESET_N(AXI_26_ARESET_N),
  .AXI_26_ARADDR(AXI_26_ARADDR),
  .AXI_26_ARBURST(AXI_26_ARBURST),
  .AXI_26_ARID(AXI_26_ARID),
  .AXI_26_ARLEN(AXI_26_ARLEN[3:0]),
  .AXI_26_ARSIZE(AXI_26_ARSIZE),
  .AXI_26_ARVALID(AXI_26_ARVALID),
  .AXI_26_AWADDR(AXI_26_AWADDR),
  .AXI_26_AWBURST(AXI_26_AWBURST),
  .AXI_26_AWID(AXI_26_AWID),
  .AXI_26_AWLEN(AXI_26_AWLEN[3:0]),
  .AXI_26_AWSIZE(AXI_26_AWSIZE),
  .AXI_26_AWVALID(AXI_26_AWVALID),
  .AXI_26_RREADY(rready_26),
  .AXI_26_BREADY(bready_26),
  .AXI_26_WDATA(AXI_26_WDATA),
  .AXI_26_WLAST(AXI_26_WLAST),
  .AXI_26_WSTRB(AXI_26_WSTRB),
  .AXI_26_WDATA_PARITY(AXI_26_WDATA_PARITY),
  .AXI_26_WVALID(AXI_26_WVALID),
  //.AXI_26_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_26_DFI_LP_PWR_X_REQ(AXI_26_DFI_LP_PWR_X_REQ),
  .AXI_26_MC_STATUS(AXI_26_MC_STATUS),
  .AXI_26_PHY_STATUS(AXI_26_PHY_STATUS),
  .AXI_27_ACLK(AXI_27_ACLK),
  .AXI_27_ARESET_N(AXI_27_ARESET_N),
  .AXI_27_ARADDR(AXI_27_ARADDR),
  .AXI_27_ARBURST(AXI_27_ARBURST),
  .AXI_27_ARID(AXI_27_ARID),
  .AXI_27_ARLEN(AXI_27_ARLEN[3:0]),
  .AXI_27_ARSIZE(AXI_27_ARSIZE),
  .AXI_27_ARVALID(AXI_27_ARVALID),
  .AXI_27_AWADDR(AXI_27_AWADDR),
  .AXI_27_AWBURST(AXI_27_AWBURST),
  .AXI_27_AWID(AXI_27_AWID),
  .AXI_27_AWLEN(AXI_27_AWLEN[3:0]),
  .AXI_27_AWSIZE(AXI_27_AWSIZE),
  .AXI_27_AWVALID(AXI_27_AWVALID),
  .AXI_27_RREADY(rready_27),
  .AXI_27_BREADY(bready_27),
  .AXI_27_WDATA(AXI_27_WDATA),
  .AXI_27_WLAST(AXI_27_WLAST),
  .AXI_27_WSTRB(AXI_27_WSTRB),
  .AXI_27_WDATA_PARITY(AXI_27_WDATA_PARITY),
  .AXI_27_WVALID(AXI_27_WVALID),
  //.AXI_27_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_27_DFI_LP_PWR_X_REQ(AXI_27_DFI_LP_PWR_X_REQ),
  .AXI_28_ACLK(AXI_28_ACLK),
  .AXI_28_ARESET_N(AXI_28_ARESET_N),
  .AXI_28_ARADDR(AXI_28_ARADDR),
  .AXI_28_ARBURST(AXI_28_ARBURST),
  .AXI_28_ARID(AXI_28_ARID),
  .AXI_28_ARLEN(AXI_28_ARLEN[3:0]),
  .AXI_28_ARSIZE(AXI_28_ARSIZE),
  .AXI_28_ARVALID(AXI_28_ARVALID),
  .AXI_28_AWADDR(AXI_28_AWADDR),
  .AXI_28_AWBURST(AXI_28_AWBURST),
  .AXI_28_AWID(AXI_28_AWID),
  .AXI_28_AWLEN(AXI_28_AWLEN[3:0]),
  .AXI_28_AWSIZE(AXI_28_AWSIZE),
  .AXI_28_AWVALID(AXI_28_AWVALID),
  .AXI_28_RREADY(rready_28),
  .AXI_28_BREADY(bready_28),
  .AXI_28_WDATA(AXI_28_WDATA),
  .AXI_28_WLAST(AXI_28_WLAST),
  .AXI_28_WSTRB(AXI_28_WSTRB),
  .AXI_28_WDATA_PARITY(AXI_28_WDATA_PARITY),
  .AXI_28_WVALID(AXI_28_WVALID),
  //.AXI_28_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_28_DFI_LP_PWR_X_REQ(AXI_28_DFI_LP_PWR_X_REQ),
  .AXI_28_MC_STATUS(AXI_28_MC_STATUS),
  .AXI_28_PHY_STATUS(AXI_28_PHY_STATUS),
  .AXI_29_ACLK(AXI_29_ACLK),
  .AXI_29_ARESET_N(AXI_29_ARESET_N),
  .AXI_29_ARADDR(AXI_29_ARADDR),
  .AXI_29_ARBURST(AXI_29_ARBURST),
  .AXI_29_ARID(AXI_29_ARID),
  .AXI_29_ARLEN(AXI_29_ARLEN[3:0]),
  .AXI_29_ARSIZE(AXI_29_ARSIZE),
  .AXI_29_ARVALID(AXI_29_ARVALID),
  .AXI_29_AWADDR(AXI_29_AWADDR),
  .AXI_29_AWBURST(AXI_29_AWBURST),
  .AXI_29_AWID(AXI_29_AWID),
  .AXI_29_AWLEN(AXI_29_AWLEN[3:0]),
  .AXI_29_AWSIZE(AXI_29_AWSIZE),
  .AXI_29_AWVALID(AXI_29_AWVALID),
  .AXI_29_RREADY(rready_29),
  .AXI_29_BREADY(bready_29),
  .AXI_29_WDATA(AXI_29_WDATA),
  .AXI_29_WLAST(AXI_29_WLAST),
  .AXI_29_WSTRB(AXI_29_WSTRB),
  .AXI_29_WDATA_PARITY(AXI_29_WDATA_PARITY),
  .AXI_29_WVALID(AXI_29_WVALID),
  //.AXI_29_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_29_DFI_LP_PWR_X_REQ(AXI_29_DFI_LP_PWR_X_REQ),
  .AXI_30_ACLK(AXI_30_ACLK),
  .AXI_30_ARESET_N(AXI_30_ARESET_N),
  .AXI_30_ARADDR(AXI_30_ARADDR),
  .AXI_30_ARBURST(AXI_30_ARBURST),
  .AXI_30_ARID(AXI_30_ARID),
  .AXI_30_ARLEN(AXI_30_ARLEN[3:0]),
  .AXI_30_ARSIZE(AXI_30_ARSIZE),
  .AXI_30_ARVALID(AXI_30_ARVALID),
  .AXI_30_AWADDR(AXI_30_AWADDR),
  .AXI_30_AWBURST(AXI_30_AWBURST),
  .AXI_30_AWID(AXI_30_AWID),
  .AXI_30_AWLEN(AXI_30_AWLEN[3:0]),
  .AXI_30_AWSIZE(AXI_30_AWSIZE),
  .AXI_30_AWVALID(AXI_30_AWVALID),
  .AXI_30_RREADY(rready_30),
  .AXI_30_BREADY(bready_30),
  .AXI_30_WDATA(AXI_30_WDATA),
  .AXI_30_WLAST(AXI_30_WLAST),
  .AXI_30_WSTRB(AXI_30_WSTRB),
  .AXI_30_WDATA_PARITY(AXI_30_WDATA_PARITY),
  .AXI_30_WVALID(AXI_30_WVALID),
  //.AXI_30_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_30_DFI_LP_PWR_X_REQ(AXI_30_DFI_LP_PWR_X_REQ),
  .AXI_30_MC_STATUS(AXI_30_MC_STATUS),
  .AXI_30_PHY_STATUS(AXI_30_PHY_STATUS),
  .AXI_31_ACLK(AXI_31_ACLK),
  .AXI_31_ARESET_N(AXI_31_ARESET_N),
  .AXI_31_ARADDR(AXI_31_ARADDR),
  .AXI_31_ARBURST(AXI_31_ARBURST),
  .AXI_31_ARID(AXI_31_ARID),
  .AXI_31_ARLEN(AXI_31_ARLEN[3:0]),
  .AXI_31_ARSIZE(AXI_31_ARSIZE),
  .AXI_31_ARVALID(AXI_31_ARVALID),
  .AXI_31_AWADDR(AXI_31_AWADDR),
  .AXI_31_AWBURST(AXI_31_AWBURST),
  .AXI_31_AWID(AXI_31_AWID),
  .AXI_31_AWLEN(AXI_31_AWLEN[3:0]),
  .AXI_31_AWSIZE(AXI_31_AWSIZE),
  .AXI_31_AWVALID(AXI_31_AWVALID),
  .AXI_31_RREADY(rready_31),
  .AXI_31_BREADY(bready_31),
  .AXI_31_WDATA(AXI_31_WDATA),
  .AXI_31_WLAST(AXI_31_WLAST),
  .AXI_31_WSTRB(AXI_31_WSTRB),
  .AXI_31_WDATA_PARITY(AXI_31_WDATA_PARITY),
  .AXI_31_WVALID(AXI_31_WVALID),
  //.AXI_31_DFI_DW_RX_INDX_LD(1'b0),
  .AXI_31_DFI_LP_PWR_X_REQ(AXI_31_DFI_LP_PWR_X_REQ),
  .APB_0_PWDATA(pwdata_0),
  .APB_0_PADDR(paddr_0),
  .APB_0_PCLK(APB_0_PCLK),
  .APB_0_PENABLE(penable_0),
  .APB_0_PRESET_N(APB_0_PRESET_N),
  .APB_0_PSEL(psel_0),
  .APB_0_PWRITE(pwrite_0),
  .APB_1_PWDATA(pwdata_1),
  .APB_1_PADDR(paddr_1),
  .APB_1_PCLK(APB_1_PCLK),
  .APB_1_PENABLE(penable_1),
  .APB_1_PRESET_N(APB_1_PRESET_N),
  .APB_1_PSEL(psel_1),
  .APB_1_PWRITE(pwrite_1),
  .AXI_00_ARREADY(AXI_00_ARREADY),
  .AXI_00_AWREADY(AXI_00_AWREADY),
  .AXI_00_RDATA_PARITY(AXI_00_RDATA_PARITY),
  .AXI_00_RDATA(AXI_00_RDATA),
  .AXI_00_RID(AXI_00_RID),
  .AXI_00_RLAST(AXI_00_RLAST),
  .AXI_00_RRESP(AXI_00_RRESP),
  .AXI_00_RVALID(AXI_00_RVALID),
  .AXI_00_WREADY(AXI_00_WREADY),
  .AXI_00_BID(AXI_00_BID),
  .AXI_00_BRESP(AXI_00_BRESP),
  .AXI_00_BVALID(AXI_00_BVALID),
  .AXI_00_DFI_AW_AERR_N(AXI_00_DFI_AW_AERR_N),
  .AXI_00_DFI_DBI_BYTE_DISABLE(AXI_00_DFI_DBI_BYTE_DISABLE),
  .AXI_00_DFI_DW_RDDATA_DBI(AXI_00_DFI_DW_RDDATA_DBI),
  .AXI_00_DFI_DW_RDDATA_DERR(AXI_00_DFI_DW_RDDATA_DERR),
  .AXI_00_DFI_DW_RDDATA_VALID(AXI_00_DFI_DW_RDDATA_VALID),
  .AXI_00_DFI_INIT_COMPLETE(AXI_00_DFI_INIT_COMPLETE),
  .AXI_00_DFI_PHY_LP_STATE(AXI_00_DFI_PHY_LP_STATE),
  .AXI_00_DFI_PHYUPD_REQ(AXI_00_DFI_PHYUPD_REQ),
  .AXI_00_DFI_CLK_BUF(AXI_00_DFI_CLK_BUF),
  .AXI_00_DFI_RST_N_BUF(AXI_00_DFI_RST_N_BUF),
  .AXI_01_ARREADY(AXI_01_ARREADY),
  .AXI_01_AWREADY(AXI_01_AWREADY),
  .AXI_01_RDATA_PARITY(AXI_01_RDATA_PARITY),
  .AXI_01_RDATA(AXI_01_RDATA),
  .AXI_01_RID(AXI_01_RID),
  .AXI_01_RLAST(AXI_01_RLAST),
  .AXI_01_RRESP(AXI_01_RRESP),
  .AXI_01_RVALID(AXI_01_RVALID),
  .AXI_01_WREADY(AXI_01_WREADY),
  .AXI_01_BID(AXI_01_BID),
  .AXI_01_BRESP(AXI_01_BRESP),
  .AXI_01_BVALID(AXI_01_BVALID),
  .AXI_01_DFI_AW_AERR_N(AXI_01_DFI_AW_AERR_N),
  .AXI_01_DFI_DBI_BYTE_DISABLE(AXI_01_DFI_DBI_BYTE_DISABLE),
  .AXI_01_DFI_DW_RDDATA_DBI(AXI_01_DFI_DW_RDDATA_DBI),
  .AXI_01_DFI_DW_RDDATA_DERR(AXI_01_DFI_DW_RDDATA_DERR),
  .AXI_01_DFI_DW_RDDATA_VALID(AXI_01_DFI_DW_RDDATA_VALID),
  .AXI_01_DFI_INIT_COMPLETE(AXI_01_DFI_INIT_COMPLETE),
  .AXI_01_DFI_PHY_LP_STATE(AXI_01_DFI_PHY_LP_STATE),
  .AXI_01_DFI_PHYUPD_REQ(AXI_01_DFI_PHYUPD_REQ),
  .AXI_01_DFI_CLK_BUF(AXI_01_DFI_CLK_BUF),
  .AXI_01_DFI_RST_N_BUF(AXI_01_DFI_RST_N_BUF),
  .AXI_02_ARREADY(AXI_02_ARREADY),
  .AXI_02_AWREADY(AXI_02_AWREADY),
  .AXI_02_RDATA_PARITY(AXI_02_RDATA_PARITY),
  .AXI_02_RDATA(AXI_02_RDATA),
  .AXI_02_RID(AXI_02_RID),
  .AXI_02_RLAST(AXI_02_RLAST),
  .AXI_02_RRESP(AXI_02_RRESP),
  .AXI_02_RVALID(AXI_02_RVALID),
  .AXI_02_WREADY(AXI_02_WREADY),
  .AXI_02_BID(AXI_02_BID),
  .AXI_02_BRESP(AXI_02_BRESP),
  .AXI_02_BVALID(AXI_02_BVALID),
  .AXI_02_DFI_AW_AERR_N(AXI_02_DFI_AW_AERR_N),
  .AXI_02_DFI_DBI_BYTE_DISABLE(AXI_02_DFI_DBI_BYTE_DISABLE),
  .AXI_02_DFI_DW_RDDATA_DBI(AXI_02_DFI_DW_RDDATA_DBI),
  .AXI_02_DFI_DW_RDDATA_DERR(AXI_02_DFI_DW_RDDATA_DERR),
  .AXI_02_DFI_DW_RDDATA_VALID(AXI_02_DFI_DW_RDDATA_VALID),
  .AXI_02_DFI_INIT_COMPLETE(AXI_02_DFI_INIT_COMPLETE),
  .AXI_02_DFI_PHY_LP_STATE(AXI_02_DFI_PHY_LP_STATE),
  .AXI_02_DFI_PHYUPD_REQ(AXI_02_DFI_PHYUPD_REQ),
  .AXI_02_DFI_CLK_BUF(AXI_02_DFI_CLK_BUF),
  .AXI_02_DFI_RST_N_BUF(AXI_02_DFI_RST_N_BUF),
  .AXI_03_ARREADY(AXI_03_ARREADY),
  .AXI_03_AWREADY(AXI_03_AWREADY),
  .AXI_03_RDATA_PARITY(AXI_03_RDATA_PARITY),
  .AXI_03_RDATA(AXI_03_RDATA),
  .AXI_03_RID(AXI_03_RID),
  .AXI_03_RLAST(AXI_03_RLAST),
  .AXI_03_RRESP(AXI_03_RRESP),
  .AXI_03_RVALID(AXI_03_RVALID),
  .AXI_03_WREADY(AXI_03_WREADY),
  .AXI_03_BID(AXI_03_BID),
  .AXI_03_BRESP(AXI_03_BRESP),
  .AXI_03_BVALID(AXI_03_BVALID),
  .AXI_03_DFI_AW_AERR_N(AXI_03_DFI_AW_AERR_N),
  .AXI_03_DFI_DBI_BYTE_DISABLE(AXI_03_DFI_DBI_BYTE_DISABLE),
  .AXI_03_DFI_DW_RDDATA_DBI(AXI_03_DFI_DW_RDDATA_DBI),
  .AXI_03_DFI_DW_RDDATA_DERR(AXI_03_DFI_DW_RDDATA_DERR),
  .AXI_03_DFI_DW_RDDATA_VALID(AXI_03_DFI_DW_RDDATA_VALID),
  .AXI_03_DFI_INIT_COMPLETE(AXI_03_DFI_INIT_COMPLETE),
  .AXI_03_DFI_PHY_LP_STATE(AXI_03_DFI_PHY_LP_STATE),
  .AXI_03_DFI_PHYUPD_REQ(AXI_03_DFI_PHYUPD_REQ),
  .AXI_03_DFI_CLK_BUF(AXI_03_DFI_CLK_BUF),
  .AXI_03_DFI_RST_N_BUF(AXI_03_DFI_RST_N_BUF),
  .AXI_04_ARREADY(AXI_04_ARREADY),
  .AXI_04_AWREADY(AXI_04_AWREADY),
  .AXI_04_RDATA_PARITY(AXI_04_RDATA_PARITY),
  .AXI_04_RDATA(AXI_04_RDATA),
  .AXI_04_RID(AXI_04_RID),
  .AXI_04_RLAST(AXI_04_RLAST),
  .AXI_04_RRESP(AXI_04_RRESP),
  .AXI_04_RVALID(AXI_04_RVALID),
  .AXI_04_WREADY(AXI_04_WREADY),
  .AXI_04_BID(AXI_04_BID),
  .AXI_04_BRESP(AXI_04_BRESP),
  .AXI_04_BVALID(AXI_04_BVALID),
  .AXI_04_DFI_AW_AERR_N(AXI_04_DFI_AW_AERR_N),
  .AXI_04_DFI_DBI_BYTE_DISABLE(AXI_04_DFI_DBI_BYTE_DISABLE),
  .AXI_04_DFI_DW_RDDATA_DBI(AXI_04_DFI_DW_RDDATA_DBI),
  .AXI_04_DFI_DW_RDDATA_DERR(AXI_04_DFI_DW_RDDATA_DERR),
  .AXI_04_DFI_DW_RDDATA_VALID(AXI_04_DFI_DW_RDDATA_VALID),
  .AXI_04_DFI_INIT_COMPLETE(AXI_04_DFI_INIT_COMPLETE),
  .AXI_04_DFI_PHY_LP_STATE(AXI_04_DFI_PHY_LP_STATE),
  .AXI_04_DFI_PHYUPD_REQ(AXI_04_DFI_PHYUPD_REQ),
  .AXI_04_DFI_CLK_BUF(AXI_04_DFI_CLK_BUF),
  .AXI_04_DFI_RST_N_BUF(AXI_04_DFI_RST_N_BUF),
  .AXI_05_ARREADY(AXI_05_ARREADY),
  .AXI_05_AWREADY(AXI_05_AWREADY),
  .AXI_05_RDATA_PARITY(AXI_05_RDATA_PARITY),
  .AXI_05_RDATA(AXI_05_RDATA),
  .AXI_05_RID(AXI_05_RID),
  .AXI_05_RLAST(AXI_05_RLAST),
  .AXI_05_RRESP(AXI_05_RRESP),
  .AXI_05_RVALID(AXI_05_RVALID),
  .AXI_05_WREADY(AXI_05_WREADY),
  .AXI_05_BID(AXI_05_BID),
  .AXI_05_BRESP(AXI_05_BRESP),
  .AXI_05_BVALID(AXI_05_BVALID),
  .AXI_05_DFI_AW_AERR_N(AXI_05_DFI_AW_AERR_N),
  .AXI_05_DFI_DBI_BYTE_DISABLE(AXI_05_DFI_DBI_BYTE_DISABLE),
  .AXI_05_DFI_DW_RDDATA_DBI(AXI_05_DFI_DW_RDDATA_DBI),
  .AXI_05_DFI_DW_RDDATA_DERR(AXI_05_DFI_DW_RDDATA_DERR),
  .AXI_05_DFI_DW_RDDATA_VALID(AXI_05_DFI_DW_RDDATA_VALID),
  .AXI_05_DFI_INIT_COMPLETE(AXI_05_DFI_INIT_COMPLETE),
  .AXI_05_DFI_PHY_LP_STATE(AXI_05_DFI_PHY_LP_STATE),
  .AXI_05_DFI_PHYUPD_REQ(AXI_05_DFI_PHYUPD_REQ),
  .AXI_05_DFI_CLK_BUF(AXI_05_DFI_CLK_BUF),
  .AXI_05_DFI_RST_N_BUF(AXI_05_DFI_RST_N_BUF),
  .AXI_06_ARREADY(AXI_06_ARREADY),
  .AXI_06_AWREADY(AXI_06_AWREADY),
  .AXI_06_RDATA_PARITY(AXI_06_RDATA_PARITY),
  .AXI_06_RDATA(AXI_06_RDATA),
  .AXI_06_RID(AXI_06_RID),
  .AXI_06_RLAST(AXI_06_RLAST),
  .AXI_06_RRESP(AXI_06_RRESP),
  .AXI_06_RVALID(AXI_06_RVALID),
  .AXI_06_WREADY(AXI_06_WREADY),
  .AXI_06_BID(AXI_06_BID),
  .AXI_06_BRESP(AXI_06_BRESP),
  .AXI_06_BVALID(AXI_06_BVALID),
  .AXI_06_DFI_AW_AERR_N(AXI_06_DFI_AW_AERR_N),
  .AXI_06_DFI_DBI_BYTE_DISABLE(AXI_06_DFI_DBI_BYTE_DISABLE),
  .AXI_06_DFI_DW_RDDATA_DBI(AXI_06_DFI_DW_RDDATA_DBI),
  .AXI_06_DFI_DW_RDDATA_DERR(AXI_06_DFI_DW_RDDATA_DERR),
  .AXI_06_DFI_DW_RDDATA_VALID(AXI_06_DFI_DW_RDDATA_VALID),
  .AXI_06_DFI_INIT_COMPLETE(AXI_06_DFI_INIT_COMPLETE),
  .AXI_06_DFI_PHY_LP_STATE(AXI_06_DFI_PHY_LP_STATE),
  .AXI_06_DFI_PHYUPD_REQ(AXI_06_DFI_PHYUPD_REQ),
  .AXI_06_DFI_CLK_BUF(AXI_06_DFI_CLK_BUF),
  .AXI_06_DFI_RST_N_BUF(AXI_06_DFI_RST_N_BUF),
  .AXI_07_ARREADY(AXI_07_ARREADY),
  .AXI_07_AWREADY(AXI_07_AWREADY),
  .AXI_07_RDATA_PARITY(AXI_07_RDATA_PARITY),
  .AXI_07_RDATA(AXI_07_RDATA),
  .AXI_07_RID(AXI_07_RID),
  .AXI_07_RLAST(AXI_07_RLAST),
  .AXI_07_RRESP(AXI_07_RRESP),
  .AXI_07_RVALID(AXI_07_RVALID),
  .AXI_07_WREADY(AXI_07_WREADY),
  .AXI_07_BID(AXI_07_BID),
  .AXI_07_BRESP(AXI_07_BRESP),
  .AXI_07_BVALID(AXI_07_BVALID),
  .AXI_07_DFI_AW_AERR_N(AXI_07_DFI_AW_AERR_N),
  .AXI_07_DFI_DBI_BYTE_DISABLE(AXI_07_DFI_DBI_BYTE_DISABLE),
  .AXI_07_DFI_DW_RDDATA_DBI(AXI_07_DFI_DW_RDDATA_DBI),
  .AXI_07_DFI_DW_RDDATA_DERR(AXI_07_DFI_DW_RDDATA_DERR),
  .AXI_07_DFI_DW_RDDATA_VALID(AXI_07_DFI_DW_RDDATA_VALID),
  .AXI_07_DFI_INIT_COMPLETE(AXI_07_DFI_INIT_COMPLETE),
  .AXI_07_DFI_PHY_LP_STATE(AXI_07_DFI_PHY_LP_STATE),
  .AXI_07_DFI_PHYUPD_REQ(AXI_07_DFI_PHYUPD_REQ),
  .AXI_07_DFI_CLK_BUF(AXI_07_DFI_CLK_BUF),
  .AXI_07_DFI_RST_N_BUF(AXI_07_DFI_RST_N_BUF),
  .AXI_08_ARREADY(AXI_08_ARREADY),
  .AXI_08_AWREADY(AXI_08_AWREADY),
  .AXI_08_RDATA_PARITY(AXI_08_RDATA_PARITY),
  .AXI_08_RDATA(AXI_08_RDATA),
  .AXI_08_RID(AXI_08_RID),
  .AXI_08_RLAST(AXI_08_RLAST),
  .AXI_08_RRESP(AXI_08_RRESP),
  .AXI_08_RVALID(AXI_08_RVALID),
  .AXI_08_WREADY(AXI_08_WREADY),
  .AXI_08_BID(AXI_08_BID),
  .AXI_08_BRESP(AXI_08_BRESP),
  .AXI_08_BVALID(AXI_08_BVALID),
  .AXI_08_DFI_AW_AERR_N(AXI_08_DFI_AW_AERR_N),
  .AXI_08_DFI_DBI_BYTE_DISABLE(AXI_08_DFI_DBI_BYTE_DISABLE),
  .AXI_08_DFI_DW_RDDATA_DBI(AXI_08_DFI_DW_RDDATA_DBI),
  .AXI_08_DFI_DW_RDDATA_DERR(AXI_08_DFI_DW_RDDATA_DERR),
  .AXI_08_DFI_DW_RDDATA_VALID(AXI_08_DFI_DW_RDDATA_VALID),
  .AXI_08_DFI_INIT_COMPLETE(AXI_08_DFI_INIT_COMPLETE),
  .AXI_08_DFI_PHY_LP_STATE(AXI_08_DFI_PHY_LP_STATE),
  .AXI_08_DFI_PHYUPD_REQ(AXI_08_DFI_PHYUPD_REQ),
  .AXI_08_DFI_CLK_BUF(AXI_08_DFI_CLK_BUF),
  .AXI_08_DFI_RST_N_BUF(AXI_08_DFI_RST_N_BUF),
  .AXI_09_ARREADY(AXI_09_ARREADY),
  .AXI_09_AWREADY(AXI_09_AWREADY),
  .AXI_09_RDATA_PARITY(AXI_09_RDATA_PARITY),
  .AXI_09_RDATA(AXI_09_RDATA),
  .AXI_09_RID(AXI_09_RID),
  .AXI_09_RLAST(AXI_09_RLAST),
  .AXI_09_RRESP(AXI_09_RRESP),
  .AXI_09_RVALID(AXI_09_RVALID),
  .AXI_09_WREADY(AXI_09_WREADY),
  .AXI_09_BID(AXI_09_BID),
  .AXI_09_BRESP(AXI_09_BRESP),
  .AXI_09_BVALID(AXI_09_BVALID),
  .AXI_09_DFI_AW_AERR_N(AXI_09_DFI_AW_AERR_N),
  .AXI_09_DFI_DBI_BYTE_DISABLE(AXI_09_DFI_DBI_BYTE_DISABLE),
  .AXI_09_DFI_DW_RDDATA_DBI(AXI_09_DFI_DW_RDDATA_DBI),
  .AXI_09_DFI_DW_RDDATA_DERR(AXI_09_DFI_DW_RDDATA_DERR),
  .AXI_09_DFI_DW_RDDATA_VALID(AXI_09_DFI_DW_RDDATA_VALID),
  .AXI_09_DFI_INIT_COMPLETE(AXI_09_DFI_INIT_COMPLETE),
  .AXI_09_DFI_PHY_LP_STATE(AXI_09_DFI_PHY_LP_STATE),
  .AXI_09_DFI_PHYUPD_REQ(AXI_09_DFI_PHYUPD_REQ),
  .AXI_09_DFI_CLK_BUF(AXI_09_DFI_CLK_BUF),
  .AXI_09_DFI_RST_N_BUF(AXI_09_DFI_RST_N_BUF),
  .AXI_10_ARREADY(AXI_10_ARREADY),
  .AXI_10_AWREADY(AXI_10_AWREADY),
  .AXI_10_RDATA_PARITY(AXI_10_RDATA_PARITY),
  .AXI_10_RDATA(AXI_10_RDATA),
  .AXI_10_RID(AXI_10_RID),
  .AXI_10_RLAST(AXI_10_RLAST),
  .AXI_10_RRESP(AXI_10_RRESP),
  .AXI_10_RVALID(AXI_10_RVALID),
  .AXI_10_WREADY(AXI_10_WREADY),
  .AXI_10_BID(AXI_10_BID),
  .AXI_10_BRESP(AXI_10_BRESP),
  .AXI_10_BVALID(AXI_10_BVALID),
  .AXI_10_DFI_AW_AERR_N(AXI_10_DFI_AW_AERR_N),
  .AXI_10_DFI_DBI_BYTE_DISABLE(AXI_10_DFI_DBI_BYTE_DISABLE),
  .AXI_10_DFI_DW_RDDATA_DBI(AXI_10_DFI_DW_RDDATA_DBI),
  .AXI_10_DFI_DW_RDDATA_DERR(AXI_10_DFI_DW_RDDATA_DERR),
  .AXI_10_DFI_DW_RDDATA_VALID(AXI_10_DFI_DW_RDDATA_VALID),
  .AXI_10_DFI_INIT_COMPLETE(AXI_10_DFI_INIT_COMPLETE),
  .AXI_10_DFI_PHY_LP_STATE(AXI_10_DFI_PHY_LP_STATE),
  .AXI_10_DFI_PHYUPD_REQ(AXI_10_DFI_PHYUPD_REQ),
  .AXI_10_DFI_CLK_BUF(AXI_10_DFI_CLK_BUF),
  .AXI_10_DFI_RST_N_BUF(AXI_10_DFI_RST_N_BUF),
  .AXI_11_ARREADY(AXI_11_ARREADY),
  .AXI_11_AWREADY(AXI_11_AWREADY),
  .AXI_11_RDATA_PARITY(AXI_11_RDATA_PARITY),
  .AXI_11_RDATA(AXI_11_RDATA),
  .AXI_11_RID(AXI_11_RID),
  .AXI_11_RLAST(AXI_11_RLAST),
  .AXI_11_RRESP(AXI_11_RRESP),
  .AXI_11_RVALID(AXI_11_RVALID),
  .AXI_11_WREADY(AXI_11_WREADY),
  .AXI_11_BID(AXI_11_BID),
  .AXI_11_BRESP(AXI_11_BRESP),
  .AXI_11_BVALID(AXI_11_BVALID),
  .AXI_11_DFI_AW_AERR_N(AXI_11_DFI_AW_AERR_N),
  .AXI_11_DFI_DBI_BYTE_DISABLE(AXI_11_DFI_DBI_BYTE_DISABLE),
  .AXI_11_DFI_DW_RDDATA_DBI(AXI_11_DFI_DW_RDDATA_DBI),
  .AXI_11_DFI_DW_RDDATA_DERR(AXI_11_DFI_DW_RDDATA_DERR),
  .AXI_11_DFI_DW_RDDATA_VALID(AXI_11_DFI_DW_RDDATA_VALID),
  .AXI_11_DFI_INIT_COMPLETE(AXI_11_DFI_INIT_COMPLETE),
  .AXI_11_DFI_PHY_LP_STATE(AXI_11_DFI_PHY_LP_STATE),
  .AXI_11_DFI_PHYUPD_REQ(AXI_11_DFI_PHYUPD_REQ),
  .AXI_11_DFI_CLK_BUF(AXI_11_DFI_CLK_BUF),
  .AXI_11_DFI_RST_N_BUF(AXI_11_DFI_RST_N_BUF),
  .AXI_12_ARREADY(AXI_12_ARREADY),
  .AXI_12_AWREADY(AXI_12_AWREADY),
  .AXI_12_RDATA_PARITY(AXI_12_RDATA_PARITY),
  .AXI_12_RDATA(AXI_12_RDATA),
  .AXI_12_RID(AXI_12_RID),
  .AXI_12_RLAST(AXI_12_RLAST),
  .AXI_12_RRESP(AXI_12_RRESP),
  .AXI_12_RVALID(AXI_12_RVALID),
  .AXI_12_WREADY(AXI_12_WREADY),
  .AXI_12_BID(AXI_12_BID),
  .AXI_12_BRESP(AXI_12_BRESP),
  .AXI_12_BVALID(AXI_12_BVALID),
  .AXI_12_DFI_AW_AERR_N(AXI_12_DFI_AW_AERR_N),
  .AXI_12_DFI_DBI_BYTE_DISABLE(AXI_12_DFI_DBI_BYTE_DISABLE),
  .AXI_12_DFI_DW_RDDATA_DBI(AXI_12_DFI_DW_RDDATA_DBI),
  .AXI_12_DFI_DW_RDDATA_DERR(AXI_12_DFI_DW_RDDATA_DERR),
  .AXI_12_DFI_DW_RDDATA_VALID(AXI_12_DFI_DW_RDDATA_VALID),
  .AXI_12_DFI_INIT_COMPLETE(AXI_12_DFI_INIT_COMPLETE),
  .AXI_12_DFI_PHY_LP_STATE(AXI_12_DFI_PHY_LP_STATE),
  .AXI_12_DFI_PHYUPD_REQ(AXI_12_DFI_PHYUPD_REQ),
  .AXI_12_DFI_CLK_BUF(AXI_12_DFI_CLK_BUF),
  .AXI_12_DFI_RST_N_BUF(AXI_12_DFI_RST_N_BUF),
  .AXI_13_ARREADY(AXI_13_ARREADY),
  .AXI_13_AWREADY(AXI_13_AWREADY),
  .AXI_13_RDATA_PARITY(AXI_13_RDATA_PARITY),
  .AXI_13_RDATA(AXI_13_RDATA),
  .AXI_13_RID(AXI_13_RID),
  .AXI_13_RLAST(AXI_13_RLAST),
  .AXI_13_RRESP(AXI_13_RRESP),
  .AXI_13_RVALID(AXI_13_RVALID),
  .AXI_13_WREADY(AXI_13_WREADY),
  .AXI_13_BID(AXI_13_BID),
  .AXI_13_BRESP(AXI_13_BRESP),
  .AXI_13_BVALID(AXI_13_BVALID),
  .AXI_13_DFI_AW_AERR_N(AXI_13_DFI_AW_AERR_N),
  .AXI_13_DFI_DBI_BYTE_DISABLE(AXI_13_DFI_DBI_BYTE_DISABLE),
  .AXI_13_DFI_DW_RDDATA_DBI(AXI_13_DFI_DW_RDDATA_DBI),
  .AXI_13_DFI_DW_RDDATA_DERR(AXI_13_DFI_DW_RDDATA_DERR),
  .AXI_13_DFI_DW_RDDATA_VALID(AXI_13_DFI_DW_RDDATA_VALID),
  .AXI_13_DFI_INIT_COMPLETE(AXI_13_DFI_INIT_COMPLETE),
  .AXI_13_DFI_PHY_LP_STATE(AXI_13_DFI_PHY_LP_STATE),
  .AXI_13_DFI_PHYUPD_REQ(AXI_13_DFI_PHYUPD_REQ),
  .AXI_13_DFI_CLK_BUF(AXI_13_DFI_CLK_BUF),
  .AXI_13_DFI_RST_N_BUF(AXI_13_DFI_RST_N_BUF),
  .AXI_14_ARREADY(AXI_14_ARREADY),
  .AXI_14_AWREADY(AXI_14_AWREADY),
  .AXI_14_RDATA_PARITY(AXI_14_RDATA_PARITY),
  .AXI_14_RDATA(AXI_14_RDATA),
  .AXI_14_RID(AXI_14_RID),
  .AXI_14_RLAST(AXI_14_RLAST),
  .AXI_14_RRESP(AXI_14_RRESP),
  .AXI_14_RVALID(AXI_14_RVALID),
  .AXI_14_WREADY(AXI_14_WREADY),
  .AXI_14_BID(AXI_14_BID),
  .AXI_14_BRESP(AXI_14_BRESP),
  .AXI_14_BVALID(AXI_14_BVALID),
  .AXI_14_DFI_AW_AERR_N(AXI_14_DFI_AW_AERR_N),
  .AXI_14_DFI_DBI_BYTE_DISABLE(AXI_14_DFI_DBI_BYTE_DISABLE),
  .AXI_14_DFI_DW_RDDATA_DBI(AXI_14_DFI_DW_RDDATA_DBI),
  .AXI_14_DFI_DW_RDDATA_DERR(AXI_14_DFI_DW_RDDATA_DERR),
  .AXI_14_DFI_DW_RDDATA_VALID(AXI_14_DFI_DW_RDDATA_VALID),
  .AXI_14_DFI_INIT_COMPLETE(AXI_14_DFI_INIT_COMPLETE),
  .AXI_14_DFI_PHY_LP_STATE(AXI_14_DFI_PHY_LP_STATE),
  .AXI_14_DFI_PHYUPD_REQ(AXI_14_DFI_PHYUPD_REQ),
  .AXI_14_DFI_CLK_BUF(AXI_14_DFI_CLK_BUF),
  .AXI_14_DFI_RST_N_BUF(AXI_14_DFI_RST_N_BUF),
  .AXI_15_ARREADY(AXI_15_ARREADY),
  .AXI_15_AWREADY(AXI_15_AWREADY),
  .AXI_15_RDATA_PARITY(AXI_15_RDATA_PARITY),
  .AXI_15_RDATA(AXI_15_RDATA),
  .AXI_15_RID(AXI_15_RID),
  .AXI_15_RLAST(AXI_15_RLAST),
  .AXI_15_RRESP(AXI_15_RRESP),
  .AXI_15_RVALID(AXI_15_RVALID),
  .AXI_15_WREADY(AXI_15_WREADY),
  .AXI_15_BID(AXI_15_BID),
  .AXI_15_BRESP(AXI_15_BRESP),
  .AXI_15_BVALID(AXI_15_BVALID),
  .AXI_15_DFI_AW_AERR_N(AXI_15_DFI_AW_AERR_N),
  .AXI_15_DFI_DBI_BYTE_DISABLE(AXI_15_DFI_DBI_BYTE_DISABLE),
  .AXI_15_DFI_DW_RDDATA_DBI(AXI_15_DFI_DW_RDDATA_DBI),
  .AXI_15_DFI_DW_RDDATA_DERR(AXI_15_DFI_DW_RDDATA_DERR),
  .AXI_15_DFI_DW_RDDATA_VALID(AXI_15_DFI_DW_RDDATA_VALID),
  .AXI_15_DFI_INIT_COMPLETE(AXI_15_DFI_INIT_COMPLETE),
  .AXI_15_DFI_PHY_LP_STATE(AXI_15_DFI_PHY_LP_STATE),
  .AXI_15_DFI_PHYUPD_REQ(AXI_15_DFI_PHYUPD_REQ),
  .AXI_15_DFI_CLK_BUF(AXI_15_DFI_CLK_BUF),
  .AXI_15_DFI_RST_N_BUF(AXI_15_DFI_RST_N_BUF),
  .AXI_16_ARREADY(AXI_16_ARREADY),
  .AXI_16_AWREADY(AXI_16_AWREADY),
  .AXI_16_RDATA_PARITY(AXI_16_RDATA_PARITY),
  .AXI_16_RDATA(AXI_16_RDATA),
  .AXI_16_RID(AXI_16_RID),
  .AXI_16_RLAST(AXI_16_RLAST),
  .AXI_16_RRESP(AXI_16_RRESP),
  .AXI_16_RVALID(AXI_16_RVALID),
  .AXI_16_WREADY(AXI_16_WREADY),
  .AXI_16_BID(AXI_16_BID),
  .AXI_16_BRESP(AXI_16_BRESP),
  .AXI_16_BVALID(AXI_16_BVALID),
  .AXI_16_DFI_AW_AERR_N(AXI_16_DFI_AW_AERR_N),
  .AXI_16_DFI_DBI_BYTE_DISABLE(AXI_16_DFI_DBI_BYTE_DISABLE),
  .AXI_16_DFI_DW_RDDATA_DBI(AXI_16_DFI_DW_RDDATA_DBI),
  .AXI_16_DFI_DW_RDDATA_DERR(AXI_16_DFI_DW_RDDATA_DERR),
  .AXI_16_DFI_DW_RDDATA_VALID(AXI_16_DFI_DW_RDDATA_VALID),
  .AXI_16_DFI_INIT_COMPLETE(AXI_16_DFI_INIT_COMPLETE),
  .AXI_16_DFI_PHY_LP_STATE(AXI_16_DFI_PHY_LP_STATE),
  .AXI_16_DFI_PHYUPD_REQ(AXI_16_DFI_PHYUPD_REQ),
  .AXI_16_DFI_CLK_BUF(AXI_16_DFI_CLK_BUF),
  .AXI_16_DFI_RST_N_BUF(AXI_16_DFI_RST_N_BUF),
  .AXI_17_ARREADY(AXI_17_ARREADY),
  .AXI_17_AWREADY(AXI_17_AWREADY),
  .AXI_17_RDATA_PARITY(AXI_17_RDATA_PARITY),
  .AXI_17_RDATA(AXI_17_RDATA),
  .AXI_17_RID(AXI_17_RID),
  .AXI_17_RLAST(AXI_17_RLAST),
  .AXI_17_RRESP(AXI_17_RRESP),
  .AXI_17_RVALID(AXI_17_RVALID),
  .AXI_17_WREADY(AXI_17_WREADY),
  .AXI_17_BID(AXI_17_BID),
  .AXI_17_BRESP(AXI_17_BRESP),
  .AXI_17_BVALID(AXI_17_BVALID),
  .AXI_17_DFI_AW_AERR_N(AXI_17_DFI_AW_AERR_N),
  .AXI_17_DFI_DBI_BYTE_DISABLE(AXI_17_DFI_DBI_BYTE_DISABLE),
  .AXI_17_DFI_DW_RDDATA_DBI(AXI_17_DFI_DW_RDDATA_DBI),
  .AXI_17_DFI_DW_RDDATA_DERR(AXI_17_DFI_DW_RDDATA_DERR),
  .AXI_17_DFI_DW_RDDATA_VALID(AXI_17_DFI_DW_RDDATA_VALID),
  .AXI_17_DFI_INIT_COMPLETE(AXI_17_DFI_INIT_COMPLETE),
  .AXI_17_DFI_PHY_LP_STATE(AXI_17_DFI_PHY_LP_STATE),
  .AXI_17_DFI_PHYUPD_REQ(AXI_17_DFI_PHYUPD_REQ),
  .AXI_17_DFI_CLK_BUF(AXI_17_DFI_CLK_BUF),
  .AXI_17_DFI_RST_N_BUF(AXI_17_DFI_RST_N_BUF),
  .AXI_18_ARREADY(AXI_18_ARREADY),
  .AXI_18_AWREADY(AXI_18_AWREADY),
  .AXI_18_RDATA_PARITY(AXI_18_RDATA_PARITY),
  .AXI_18_RDATA(AXI_18_RDATA),
  .AXI_18_RID(AXI_18_RID),
  .AXI_18_RLAST(AXI_18_RLAST),
  .AXI_18_RRESP(AXI_18_RRESP),
  .AXI_18_RVALID(AXI_18_RVALID),
  .AXI_18_WREADY(AXI_18_WREADY),
  .AXI_18_BID(AXI_18_BID),
  .AXI_18_BRESP(AXI_18_BRESP),
  .AXI_18_BVALID(AXI_18_BVALID),
  .AXI_18_DFI_AW_AERR_N(AXI_18_DFI_AW_AERR_N),
  .AXI_18_DFI_DBI_BYTE_DISABLE(AXI_18_DFI_DBI_BYTE_DISABLE),
  .AXI_18_DFI_DW_RDDATA_DBI(AXI_18_DFI_DW_RDDATA_DBI),
  .AXI_18_DFI_DW_RDDATA_DERR(AXI_18_DFI_DW_RDDATA_DERR),
  .AXI_18_DFI_DW_RDDATA_VALID(AXI_18_DFI_DW_RDDATA_VALID),
  .AXI_18_DFI_INIT_COMPLETE(AXI_18_DFI_INIT_COMPLETE),
  .AXI_18_DFI_PHY_LP_STATE(AXI_18_DFI_PHY_LP_STATE),
  .AXI_18_DFI_PHYUPD_REQ(AXI_18_DFI_PHYUPD_REQ),
  .AXI_18_DFI_CLK_BUF(AXI_18_DFI_CLK_BUF),
  .AXI_18_DFI_RST_N_BUF(AXI_18_DFI_RST_N_BUF),
  .AXI_19_ARREADY(AXI_19_ARREADY),
  .AXI_19_AWREADY(AXI_19_AWREADY),
  .AXI_19_RDATA_PARITY(AXI_19_RDATA_PARITY),
  .AXI_19_RDATA(AXI_19_RDATA),
  .AXI_19_RID(AXI_19_RID),
  .AXI_19_RLAST(AXI_19_RLAST),
  .AXI_19_RRESP(AXI_19_RRESP),
  .AXI_19_RVALID(AXI_19_RVALID),
  .AXI_19_WREADY(AXI_19_WREADY),
  .AXI_19_BID(AXI_19_BID),
  .AXI_19_BRESP(AXI_19_BRESP),
  .AXI_19_BVALID(AXI_19_BVALID),
  .AXI_19_DFI_AW_AERR_N(AXI_19_DFI_AW_AERR_N),
  .AXI_19_DFI_DBI_BYTE_DISABLE(AXI_19_DFI_DBI_BYTE_DISABLE),
  .AXI_19_DFI_DW_RDDATA_DBI(AXI_19_DFI_DW_RDDATA_DBI),
  .AXI_19_DFI_DW_RDDATA_DERR(AXI_19_DFI_DW_RDDATA_DERR),
  .AXI_19_DFI_DW_RDDATA_VALID(AXI_19_DFI_DW_RDDATA_VALID),
  .AXI_19_DFI_INIT_COMPLETE(AXI_19_DFI_INIT_COMPLETE),
  .AXI_19_DFI_PHY_LP_STATE(AXI_19_DFI_PHY_LP_STATE),
  .AXI_19_DFI_PHYUPD_REQ(AXI_19_DFI_PHYUPD_REQ),
  .AXI_19_DFI_CLK_BUF(AXI_19_DFI_CLK_BUF),
  .AXI_19_DFI_RST_N_BUF(AXI_19_DFI_RST_N_BUF),
  .AXI_20_ARREADY(AXI_20_ARREADY),
  .AXI_20_AWREADY(AXI_20_AWREADY),
  .AXI_20_RDATA_PARITY(AXI_20_RDATA_PARITY),
  .AXI_20_RDATA(AXI_20_RDATA),
  .AXI_20_RID(AXI_20_RID),
  .AXI_20_RLAST(AXI_20_RLAST),
  .AXI_20_RRESP(AXI_20_RRESP),
  .AXI_20_RVALID(AXI_20_RVALID),
  .AXI_20_WREADY(AXI_20_WREADY),
  .AXI_20_BID(AXI_20_BID),
  .AXI_20_BRESP(AXI_20_BRESP),
  .AXI_20_BVALID(AXI_20_BVALID),
  .AXI_20_DFI_AW_AERR_N(AXI_20_DFI_AW_AERR_N),
  .AXI_20_DFI_DBI_BYTE_DISABLE(AXI_20_DFI_DBI_BYTE_DISABLE),
  .AXI_20_DFI_DW_RDDATA_DBI(AXI_20_DFI_DW_RDDATA_DBI),
  .AXI_20_DFI_DW_RDDATA_DERR(AXI_20_DFI_DW_RDDATA_DERR),
  .AXI_20_DFI_DW_RDDATA_VALID(AXI_20_DFI_DW_RDDATA_VALID),
  .AXI_20_DFI_INIT_COMPLETE(AXI_20_DFI_INIT_COMPLETE),
  .AXI_20_DFI_PHY_LP_STATE(AXI_20_DFI_PHY_LP_STATE),
  .AXI_20_DFI_PHYUPD_REQ(AXI_20_DFI_PHYUPD_REQ),
  .AXI_20_DFI_CLK_BUF(AXI_20_DFI_CLK_BUF),
  .AXI_20_DFI_RST_N_BUF(AXI_20_DFI_RST_N_BUF),
  .AXI_21_ARREADY(AXI_21_ARREADY),
  .AXI_21_AWREADY(AXI_21_AWREADY),
  .AXI_21_RDATA_PARITY(AXI_21_RDATA_PARITY),
  .AXI_21_RDATA(AXI_21_RDATA),
  .AXI_21_RID(AXI_21_RID),
  .AXI_21_RLAST(AXI_21_RLAST),
  .AXI_21_RRESP(AXI_21_RRESP),
  .AXI_21_RVALID(AXI_21_RVALID),
  .AXI_21_WREADY(AXI_21_WREADY),
  .AXI_21_BID(AXI_21_BID),
  .AXI_21_BRESP(AXI_21_BRESP),
  .AXI_21_BVALID(AXI_21_BVALID),
  .AXI_21_DFI_AW_AERR_N(AXI_21_DFI_AW_AERR_N),
  .AXI_21_DFI_DBI_BYTE_DISABLE(AXI_21_DFI_DBI_BYTE_DISABLE),
  .AXI_21_DFI_DW_RDDATA_DBI(AXI_21_DFI_DW_RDDATA_DBI),
  .AXI_21_DFI_DW_RDDATA_DERR(AXI_21_DFI_DW_RDDATA_DERR),
  .AXI_21_DFI_DW_RDDATA_VALID(AXI_21_DFI_DW_RDDATA_VALID),
  .AXI_21_DFI_INIT_COMPLETE(AXI_21_DFI_INIT_COMPLETE),
  .AXI_21_DFI_PHY_LP_STATE(AXI_21_DFI_PHY_LP_STATE),
  .AXI_21_DFI_PHYUPD_REQ(AXI_21_DFI_PHYUPD_REQ),
  .AXI_21_DFI_CLK_BUF(AXI_21_DFI_CLK_BUF),
  .AXI_21_DFI_RST_N_BUF(AXI_21_DFI_RST_N_BUF),
  .AXI_22_ARREADY(AXI_22_ARREADY),
  .AXI_22_AWREADY(AXI_22_AWREADY),
  .AXI_22_RDATA_PARITY(AXI_22_RDATA_PARITY),
  .AXI_22_RDATA(AXI_22_RDATA),
  .AXI_22_RID(AXI_22_RID),
  .AXI_22_RLAST(AXI_22_RLAST),
  .AXI_22_RRESP(AXI_22_RRESP),
  .AXI_22_RVALID(AXI_22_RVALID),
  .AXI_22_WREADY(AXI_22_WREADY),
  .AXI_22_BID(AXI_22_BID),
  .AXI_22_BRESP(AXI_22_BRESP),
  .AXI_22_BVALID(AXI_22_BVALID),
  .AXI_22_DFI_AW_AERR_N(AXI_22_DFI_AW_AERR_N),
  .AXI_22_DFI_DBI_BYTE_DISABLE(AXI_22_DFI_DBI_BYTE_DISABLE),
  .AXI_22_DFI_DW_RDDATA_DBI(AXI_22_DFI_DW_RDDATA_DBI),
  .AXI_22_DFI_DW_RDDATA_DERR(AXI_22_DFI_DW_RDDATA_DERR),
  .AXI_22_DFI_DW_RDDATA_VALID(AXI_22_DFI_DW_RDDATA_VALID),
  .AXI_22_DFI_INIT_COMPLETE(AXI_22_DFI_INIT_COMPLETE),
  .AXI_22_DFI_PHY_LP_STATE(AXI_22_DFI_PHY_LP_STATE),
  .AXI_22_DFI_PHYUPD_REQ(AXI_22_DFI_PHYUPD_REQ),
  .AXI_22_DFI_CLK_BUF(AXI_22_DFI_CLK_BUF),
  .AXI_22_DFI_RST_N_BUF(AXI_22_DFI_RST_N_BUF),
  .AXI_23_ARREADY(AXI_23_ARREADY),
  .AXI_23_AWREADY(AXI_23_AWREADY),
  .AXI_23_RDATA_PARITY(AXI_23_RDATA_PARITY),
  .AXI_23_RDATA(AXI_23_RDATA),
  .AXI_23_RID(AXI_23_RID),
  .AXI_23_RLAST(AXI_23_RLAST),
  .AXI_23_RRESP(AXI_23_RRESP),
  .AXI_23_RVALID(AXI_23_RVALID),
  .AXI_23_WREADY(AXI_23_WREADY),
  .AXI_23_BID(AXI_23_BID),
  .AXI_23_BRESP(AXI_23_BRESP),
  .AXI_23_BVALID(AXI_23_BVALID),
  .AXI_23_DFI_AW_AERR_N(AXI_23_DFI_AW_AERR_N),
  .AXI_23_DFI_DBI_BYTE_DISABLE(AXI_23_DFI_DBI_BYTE_DISABLE),
  .AXI_23_DFI_DW_RDDATA_DBI(AXI_23_DFI_DW_RDDATA_DBI),
  .AXI_23_DFI_DW_RDDATA_DERR(AXI_23_DFI_DW_RDDATA_DERR),
  .AXI_23_DFI_DW_RDDATA_VALID(AXI_23_DFI_DW_RDDATA_VALID),
  .AXI_23_DFI_INIT_COMPLETE(AXI_23_DFI_INIT_COMPLETE),
  .AXI_23_DFI_PHY_LP_STATE(AXI_23_DFI_PHY_LP_STATE),
  .AXI_23_DFI_PHYUPD_REQ(AXI_23_DFI_PHYUPD_REQ),
  .AXI_23_DFI_CLK_BUF(AXI_23_DFI_CLK_BUF),
  .AXI_23_DFI_RST_N_BUF(AXI_23_DFI_RST_N_BUF),
  .AXI_24_ARREADY(AXI_24_ARREADY),
  .AXI_24_AWREADY(AXI_24_AWREADY),
  .AXI_24_RDATA_PARITY(AXI_24_RDATA_PARITY),
  .AXI_24_RDATA(AXI_24_RDATA),
  .AXI_24_RID(AXI_24_RID),
  .AXI_24_RLAST(AXI_24_RLAST),
  .AXI_24_RRESP(AXI_24_RRESP),
  .AXI_24_RVALID(AXI_24_RVALID),
  .AXI_24_WREADY(AXI_24_WREADY),
  .AXI_24_BID(AXI_24_BID),
  .AXI_24_BRESP(AXI_24_BRESP),
  .AXI_24_BVALID(AXI_24_BVALID),
  .AXI_24_DFI_AW_AERR_N(AXI_24_DFI_AW_AERR_N),
  .AXI_24_DFI_DBI_BYTE_DISABLE(AXI_24_DFI_DBI_BYTE_DISABLE),
  .AXI_24_DFI_DW_RDDATA_DBI(AXI_24_DFI_DW_RDDATA_DBI),
  .AXI_24_DFI_DW_RDDATA_DERR(AXI_24_DFI_DW_RDDATA_DERR),
  .AXI_24_DFI_DW_RDDATA_VALID(AXI_24_DFI_DW_RDDATA_VALID),
  .AXI_24_DFI_INIT_COMPLETE(AXI_24_DFI_INIT_COMPLETE),
  .AXI_24_DFI_PHY_LP_STATE(AXI_24_DFI_PHY_LP_STATE),
  .AXI_24_DFI_PHYUPD_REQ(AXI_24_DFI_PHYUPD_REQ),
  .AXI_24_DFI_CLK_BUF(AXI_24_DFI_CLK_BUF),
  .AXI_24_DFI_RST_N_BUF(AXI_24_DFI_RST_N_BUF),
  .AXI_25_ARREADY(AXI_25_ARREADY),
  .AXI_25_AWREADY(AXI_25_AWREADY),
  .AXI_25_RDATA_PARITY(AXI_25_RDATA_PARITY),
  .AXI_25_RDATA(AXI_25_RDATA),
  .AXI_25_RID(AXI_25_RID),
  .AXI_25_RLAST(AXI_25_RLAST),
  .AXI_25_RRESP(AXI_25_RRESP),
  .AXI_25_RVALID(AXI_25_RVALID),
  .AXI_25_WREADY(AXI_25_WREADY),
  .AXI_25_BID(AXI_25_BID),
  .AXI_25_BRESP(AXI_25_BRESP),
  .AXI_25_BVALID(AXI_25_BVALID),
  .AXI_25_DFI_AW_AERR_N(AXI_25_DFI_AW_AERR_N),
  .AXI_25_DFI_DBI_BYTE_DISABLE(AXI_25_DFI_DBI_BYTE_DISABLE),
  .AXI_25_DFI_DW_RDDATA_DBI(AXI_25_DFI_DW_RDDATA_DBI),
  .AXI_25_DFI_DW_RDDATA_DERR(AXI_25_DFI_DW_RDDATA_DERR),
  .AXI_25_DFI_DW_RDDATA_VALID(AXI_25_DFI_DW_RDDATA_VALID),
  .AXI_25_DFI_INIT_COMPLETE(AXI_25_DFI_INIT_COMPLETE),
  .AXI_25_DFI_PHY_LP_STATE(AXI_25_DFI_PHY_LP_STATE),
  .AXI_25_DFI_PHYUPD_REQ(AXI_25_DFI_PHYUPD_REQ),
  .AXI_25_DFI_CLK_BUF(AXI_25_DFI_CLK_BUF),
  .AXI_25_DFI_RST_N_BUF(AXI_25_DFI_RST_N_BUF),
  .AXI_26_ARREADY(AXI_26_ARREADY),
  .AXI_26_AWREADY(AXI_26_AWREADY),
  .AXI_26_RDATA_PARITY(AXI_26_RDATA_PARITY),
  .AXI_26_RDATA(AXI_26_RDATA),
  .AXI_26_RID(AXI_26_RID),
  .AXI_26_RLAST(AXI_26_RLAST),
  .AXI_26_RRESP(AXI_26_RRESP),
  .AXI_26_RVALID(AXI_26_RVALID),
  .AXI_26_WREADY(AXI_26_WREADY),
  .AXI_26_BID(AXI_26_BID),
  .AXI_26_BRESP(AXI_26_BRESP),
  .AXI_26_BVALID(AXI_26_BVALID),
  .AXI_26_DFI_AW_AERR_N(AXI_26_DFI_AW_AERR_N),
  .AXI_26_DFI_DBI_BYTE_DISABLE(AXI_26_DFI_DBI_BYTE_DISABLE),
  .AXI_26_DFI_DW_RDDATA_DBI(AXI_26_DFI_DW_RDDATA_DBI),
  .AXI_26_DFI_DW_RDDATA_DERR(AXI_26_DFI_DW_RDDATA_DERR),
  .AXI_26_DFI_DW_RDDATA_VALID(AXI_26_DFI_DW_RDDATA_VALID),
  .AXI_26_DFI_INIT_COMPLETE(AXI_26_DFI_INIT_COMPLETE),
  .AXI_26_DFI_PHY_LP_STATE(AXI_26_DFI_PHY_LP_STATE),
  .AXI_26_DFI_PHYUPD_REQ(AXI_26_DFI_PHYUPD_REQ),
  .AXI_26_DFI_CLK_BUF(AXI_26_DFI_CLK_BUF),
  .AXI_26_DFI_RST_N_BUF(AXI_26_DFI_RST_N_BUF),
  .AXI_27_ARREADY(AXI_27_ARREADY),
  .AXI_27_AWREADY(AXI_27_AWREADY),
  .AXI_27_RDATA_PARITY(AXI_27_RDATA_PARITY),
  .AXI_27_RDATA(AXI_27_RDATA),
  .AXI_27_RID(AXI_27_RID),
  .AXI_27_RLAST(AXI_27_RLAST),
  .AXI_27_RRESP(AXI_27_RRESP),
  .AXI_27_RVALID(AXI_27_RVALID),
  .AXI_27_WREADY(AXI_27_WREADY),
  .AXI_27_BID(AXI_27_BID),
  .AXI_27_BRESP(AXI_27_BRESP),
  .AXI_27_BVALID(AXI_27_BVALID),
  .AXI_27_DFI_AW_AERR_N(AXI_27_DFI_AW_AERR_N),
  .AXI_27_DFI_DBI_BYTE_DISABLE(AXI_27_DFI_DBI_BYTE_DISABLE),
  .AXI_27_DFI_DW_RDDATA_DBI(AXI_27_DFI_DW_RDDATA_DBI),
  .AXI_27_DFI_DW_RDDATA_DERR(AXI_27_DFI_DW_RDDATA_DERR),
  .AXI_27_DFI_DW_RDDATA_VALID(AXI_27_DFI_DW_RDDATA_VALID),
  .AXI_27_DFI_INIT_COMPLETE(AXI_27_DFI_INIT_COMPLETE),
  .AXI_27_DFI_PHY_LP_STATE(AXI_27_DFI_PHY_LP_STATE),
  .AXI_27_DFI_PHYUPD_REQ(AXI_27_DFI_PHYUPD_REQ),
  .AXI_27_DFI_CLK_BUF(AXI_27_DFI_CLK_BUF),
  .AXI_27_DFI_RST_N_BUF(AXI_27_DFI_RST_N_BUF),
  .AXI_28_ARREADY(AXI_28_ARREADY),
  .AXI_28_AWREADY(AXI_28_AWREADY),
  .AXI_28_RDATA_PARITY(AXI_28_RDATA_PARITY),
  .AXI_28_RDATA(AXI_28_RDATA),
  .AXI_28_RID(AXI_28_RID),
  .AXI_28_RLAST(AXI_28_RLAST),
  .AXI_28_RRESP(AXI_28_RRESP),
  .AXI_28_RVALID(AXI_28_RVALID),
  .AXI_28_WREADY(AXI_28_WREADY),
  .AXI_28_BID(AXI_28_BID),
  .AXI_28_BRESP(AXI_28_BRESP),
  .AXI_28_BVALID(AXI_28_BVALID),
  .AXI_28_DFI_AW_AERR_N(AXI_28_DFI_AW_AERR_N),
  .AXI_28_DFI_DBI_BYTE_DISABLE(AXI_28_DFI_DBI_BYTE_DISABLE),
  .AXI_28_DFI_DW_RDDATA_DBI(AXI_28_DFI_DW_RDDATA_DBI),
  .AXI_28_DFI_DW_RDDATA_DERR(AXI_28_DFI_DW_RDDATA_DERR),
  .AXI_28_DFI_DW_RDDATA_VALID(AXI_28_DFI_DW_RDDATA_VALID),
  .AXI_28_DFI_INIT_COMPLETE(AXI_28_DFI_INIT_COMPLETE),
  .AXI_28_DFI_PHY_LP_STATE(AXI_28_DFI_PHY_LP_STATE),
  .AXI_28_DFI_PHYUPD_REQ(AXI_28_DFI_PHYUPD_REQ),
  .AXI_28_DFI_CLK_BUF(AXI_28_DFI_CLK_BUF),
  .AXI_28_DFI_RST_N_BUF(AXI_28_DFI_RST_N_BUF),
  .AXI_29_ARREADY(AXI_29_ARREADY),
  .AXI_29_AWREADY(AXI_29_AWREADY),
  .AXI_29_RDATA_PARITY(AXI_29_RDATA_PARITY),
  .AXI_29_RDATA(AXI_29_RDATA),
  .AXI_29_RID(AXI_29_RID),
  .AXI_29_RLAST(AXI_29_RLAST),
  .AXI_29_RRESP(AXI_29_RRESP),
  .AXI_29_RVALID(AXI_29_RVALID),
  .AXI_29_WREADY(AXI_29_WREADY),
  .AXI_29_BID(AXI_29_BID),
  .AXI_29_BRESP(AXI_29_BRESP),
  .AXI_29_BVALID(AXI_29_BVALID),
  .AXI_29_DFI_AW_AERR_N(AXI_29_DFI_AW_AERR_N),
  .AXI_29_DFI_DBI_BYTE_DISABLE(AXI_29_DFI_DBI_BYTE_DISABLE),
  .AXI_29_DFI_DW_RDDATA_DBI(AXI_29_DFI_DW_RDDATA_DBI),
  .AXI_29_DFI_DW_RDDATA_DERR(AXI_29_DFI_DW_RDDATA_DERR),
  .AXI_29_DFI_DW_RDDATA_VALID(AXI_29_DFI_DW_RDDATA_VALID),
  .AXI_29_DFI_INIT_COMPLETE(AXI_29_DFI_INIT_COMPLETE),
  .AXI_29_DFI_PHY_LP_STATE(AXI_29_DFI_PHY_LP_STATE),
  .AXI_29_DFI_PHYUPD_REQ(AXI_29_DFI_PHYUPD_REQ),
  .AXI_29_DFI_CLK_BUF(AXI_29_DFI_CLK_BUF),
  .AXI_29_DFI_RST_N_BUF(AXI_29_DFI_RST_N_BUF),
  .AXI_30_ARREADY(AXI_30_ARREADY),
  .AXI_30_AWREADY(AXI_30_AWREADY),
  .AXI_30_RDATA_PARITY(AXI_30_RDATA_PARITY),
  .AXI_30_RDATA(AXI_30_RDATA),
  .AXI_30_RID(AXI_30_RID),
  .AXI_30_RLAST(AXI_30_RLAST),
  .AXI_30_RRESP(AXI_30_RRESP),
  .AXI_30_RVALID(AXI_30_RVALID),
  .AXI_30_WREADY(AXI_30_WREADY),
  .AXI_30_BID(AXI_30_BID),
  .AXI_30_BRESP(AXI_30_BRESP),
  .AXI_30_BVALID(AXI_30_BVALID),
  .AXI_30_DFI_AW_AERR_N(AXI_30_DFI_AW_AERR_N),
  .AXI_30_DFI_DBI_BYTE_DISABLE(AXI_30_DFI_DBI_BYTE_DISABLE),
  .AXI_30_DFI_DW_RDDATA_DBI(AXI_30_DFI_DW_RDDATA_DBI),
  .AXI_30_DFI_DW_RDDATA_DERR(AXI_30_DFI_DW_RDDATA_DERR),
  .AXI_30_DFI_DW_RDDATA_VALID(AXI_30_DFI_DW_RDDATA_VALID),
  .AXI_30_DFI_INIT_COMPLETE(AXI_30_DFI_INIT_COMPLETE),
  .AXI_30_DFI_PHY_LP_STATE(AXI_30_DFI_PHY_LP_STATE),
  .AXI_30_DFI_PHYUPD_REQ(AXI_30_DFI_PHYUPD_REQ),
  .AXI_30_DFI_CLK_BUF(AXI_30_DFI_CLK_BUF),
  .AXI_30_DFI_RST_N_BUF(AXI_30_DFI_RST_N_BUF),
  .AXI_31_ARREADY(AXI_31_ARREADY),
  .AXI_31_AWREADY(AXI_31_AWREADY),
  .AXI_31_RDATA_PARITY(AXI_31_RDATA_PARITY),
  .AXI_31_RDATA(AXI_31_RDATA),
  .AXI_31_RID(AXI_31_RID),
  .AXI_31_RLAST(AXI_31_RLAST),
  .AXI_31_RRESP(AXI_31_RRESP),
  .AXI_31_RVALID(AXI_31_RVALID),
  .AXI_31_WREADY(AXI_31_WREADY),
  .AXI_31_BID(AXI_31_BID),
  .AXI_31_BRESP(AXI_31_BRESP),
  .AXI_31_BVALID(AXI_31_BVALID),
  .AXI_31_DFI_AW_AERR_N(AXI_31_DFI_AW_AERR_N),
  .AXI_31_DFI_DBI_BYTE_DISABLE(AXI_31_DFI_DBI_BYTE_DISABLE),
  .AXI_31_DFI_DW_RDDATA_DBI(AXI_31_DFI_DW_RDDATA_DBI),
  .AXI_31_DFI_DW_RDDATA_DERR(AXI_31_DFI_DW_RDDATA_DERR),
  .AXI_31_DFI_DW_RDDATA_VALID(AXI_31_DFI_DW_RDDATA_VALID),
  .AXI_31_DFI_INIT_COMPLETE(AXI_31_DFI_INIT_COMPLETE),
  .AXI_31_DFI_PHY_LP_STATE(AXI_31_DFI_PHY_LP_STATE),
  .AXI_31_DFI_PHYUPD_REQ(AXI_31_DFI_PHYUPD_REQ),
  .AXI_31_DFI_CLK_BUF(AXI_31_DFI_CLK_BUF),
  .AXI_31_DFI_RST_N_BUF(AXI_31_DFI_RST_N_BUF),
  .APB_0_PRDATA(prdata_0),
  .APB_0_PREADY(pready_0),
  .APB_0_PSLVERR(pslverr_0),
  .APB_1_PRDATA(prdata_1),
  .APB_1_PREADY(pready_1),
  .APB_1_PSLVERR(pslverr_1),
  .DRAM_0_STAT_CATTRIP(DRAM_0_STAT_CATTRIP),
  .DRAM_0_STAT_TEMP(DRAM_0_STAT_TEMP),
  .DRAM_1_STAT_CATTRIP(DRAM_1_STAT_CATTRIP),
  .DRAM_1_STAT_TEMP(DRAM_1_STAT_TEMP),
  .BSCAN_DRCK_0 (1'b0),
  .BSCAN_DRCK_1 (1'b0),
  .BSCAN_TCK_0 (1'b0),
  .BSCAN_TCK_1 (1'b0),
  .MBIST_EN_00 (1'b1),
  .MBIST_EN_01 (1'b1),
  .MBIST_EN_02 (1'b1),
  .MBIST_EN_03 (1'b1),
  .MBIST_EN_04 (1'b1),
  .MBIST_EN_05 (1'b1),
  .MBIST_EN_06 (1'b1),
  .MBIST_EN_07 (1'b1),
  .MBIST_EN_08 (1'b1),
  .MBIST_EN_09 (1'b1),
  .MBIST_EN_10 (1'b1),
  .MBIST_EN_11 (1'b1),
  .MBIST_EN_12 (1'b1),
  .MBIST_EN_13 (1'b1),
  .MBIST_EN_14 (1'b1),
  .MBIST_EN_15 (1'b1)

);

end
endgenerate

// // synthesis translate off
// ////////////////////////////////////////////////////////////////////////////////
// // Checker to check if the upper 4-bits of AWLEN are '0'.
// ////////////////////////////////////////////////////////////////////////////////
// always @ (AXI_00_AWLEN) begin
//   if (AXI_00_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_00_AWLEN is %0h resulting in burst length more than 16", AXI_00_AWLEN);
//   end
// end
// 
// always @ (AXI_01_AWLEN) begin
//   if (AXI_01_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_01_AWLEN is %0h resulting in burst length more than 16", AXI_01_AWLEN);
//   end
// end
// 
// always @ (AXI_02_AWLEN) begin
//   if (AXI_02_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_02_AWLEN is %0h resulting in burst length more than 16", AXI_02_AWLEN);
//   end
// end
// 
// always @ (AXI_03_AWLEN) begin
//   if (AXI_03_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_03_AWLEN is %0h resulting in burst length more than 16", AXI_03_AWLEN);
//   end
// end
// 
// always @ (AXI_04_AWLEN) begin
//   if (AXI_04_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_04_AWLEN is %0h resulting in burst length more than 16", AXI_04_AWLEN);
//   end
// end
// 
// always @ (AXI_05_AWLEN) begin
//   if (AXI_05_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_05_AWLEN is %0h resulting in burst length more than 16", AXI_05_AWLEN);
//   end
// end
// 
// always @ (AXI_06_AWLEN) begin
//   if (AXI_06_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_06_AWLEN is %0h resulting in burst length more than 16", AXI_06_AWLEN);
//   end
// end
// 
// always @ (AXI_07_AWLEN) begin
//   if (AXI_07_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_07_AWLEN is %0h resulting in burst length more than 16", AXI_07_AWLEN);
//   end
// end
// 
// always @ (AXI_08_AWLEN) begin
//   if (AXI_08_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_08_AWLEN is %0h resulting in burst length more than 16", AXI_08_AWLEN);
//   end
// end
// 
// always @ (AXI_09_AWLEN) begin
//   if (AXI_09_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_09_AWLEN is %0h resulting in burst length more than 16", AXI_09_AWLEN);
//   end
// end
// 
// always @ (AXI_10_AWLEN) begin
//   if (AXI_10_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_10_AWLEN is %0h resulting in burst length more than 16", AXI_10_AWLEN);
//   end
// end
// 
// always @ (AXI_11_AWLEN) begin
//   if (AXI_11_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_11_AWLEN is %0h resulting in burst length more than 16", AXI_11_AWLEN);
//   end
// end
// 
// always @ (AXI_12_AWLEN) begin
//   if (AXI_12_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_12_AWLEN is %0h resulting in burst length more than 16", AXI_12_AWLEN);
//   end
// end
// 
// always @ (AXI_13_AWLEN) begin
//   if (AXI_13_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_13_AWLEN is %0h resulting in burst length more than 16", AXI_13_AWLEN);
//   end
// end
// 
// always @ (AXI_14_AWLEN) begin
//   if (AXI_14_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_14_AWLEN is %0h resulting in burst length more than 16", AXI_14_AWLEN);
//   end
// end
// 
// always @ (AXI_15_AWLEN) begin
//   if (AXI_15_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_15_AWLEN is %0h resulting in burst length more than 16", AXI_15_AWLEN);
//   end
// end
// 
// always @ (AXI_16_AWLEN) begin
//   if (AXI_16_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_16_AWLEN is %0h resulting in burst length more than 16", AXI_16_AWLEN);
//   end
// end
// 
// always @ (AXI_17_AWLEN) begin
//   if (AXI_17_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_17_AWLEN is %0h resulting in burst length more than 16", AXI_17_AWLEN);
//   end
// end
// 
// always @ (AXI_18_AWLEN) begin
//   if (AXI_18_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_18_AWLEN is %0h resulting in burst length more than 16", AXI_18_AWLEN);
//   end
// end
// 
// always @ (AXI_19_AWLEN) begin
//   if (AXI_19_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_19_AWLEN is %0h resulting in burst length more than 16", AXI_19_AWLEN);
//   end
// end
// 
// always @ (AXI_20_AWLEN) begin
//   if (AXI_20_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_20_AWLEN is %0h resulting in burst length more than 16", AXI_20_AWLEN);
//   end
// end
// 
// always @ (AXI_21_AWLEN) begin
//   if (AXI_21_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_21_AWLEN is %0h resulting in burst length more than 16", AXI_21_AWLEN);
//   end
// end
// 
// always @ (AXI_22_AWLEN) begin
//   if (AXI_22_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_22_AWLEN is %0h resulting in burst length more than 16", AXI_22_AWLEN);
//   end
// end
// 
// always @ (AXI_23_AWLEN) begin
//   if (AXI_23_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_23_AWLEN is %0h resulting in burst length more than 16", AXI_23_AWLEN);
//   end
// end
// 
// always @ (AXI_24_AWLEN) begin
//   if (AXI_24_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_24_AWLEN is %0h resulting in burst length more than 16", AXI_24_AWLEN);
//   end
// end
// 
// always @ (AXI_25_AWLEN) begin
//   if (AXI_25_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_25_AWLEN is %0h resulting in burst length more than 16", AXI_25_AWLEN);
//   end
// end
// 
// always @ (AXI_26_AWLEN) begin
//   if (AXI_26_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_26_AWLEN is %0h resulting in burst length more than 16", AXI_26_AWLEN);
//   end
// end
// 
// always @ (AXI_27_AWLEN) begin
//   if (AXI_27_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_27_AWLEN is %0h resulting in burst length more than 16", AXI_27_AWLEN);
//   end
// end
// 
// always @ (AXI_28_AWLEN) begin
//   if (AXI_28_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_28_AWLEN is %0h resulting in burst length more than 16", AXI_28_AWLEN);
//   end
// end
// 
// always @ (AXI_29_AWLEN) begin
//   if (AXI_29_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_29_AWLEN is %0h resulting in burst length more than 16", AXI_29_AWLEN);
//   end
// end
// 
// always @ (AXI_30_AWLEN) begin
//   if (AXI_30_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_30_AWLEN is %0h resulting in burst length more than 16", AXI_30_AWLEN);
//   end
// end
// 
// always @ (AXI_31_AWLEN) begin
//   if (AXI_31_AWLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_31_AWLEN is %0h resulting in burst length more than 16", AXI_31_AWLEN);
//   end
// end
// 
// ////////////////////////////////////////////////////////////////////////////////
// // Checker to check if the upper 4-bits of ARLEN are '0'.
// ////////////////////////////////////////////////////////////////////////////////
// always @ (AXI_00_ARLEN) begin
//   if (AXI_00_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_00_ARLEN is %0h resulting in burst length more than 16", AXI_00_ARLEN);
//   end
// end
// 
// always @ (AXI_01_ARLEN) begin
//   if (AXI_01_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_01_ARLEN is %0h resulting in burst length more than 16", AXI_01_ARLEN);
//   end
// end
// 
// always @ (AXI_02_ARLEN) begin
//   if (AXI_02_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_02_ARLEN is %0h resulting in burst length more than 16", AXI_02_ARLEN);
//   end
// end
// 
// always @ (AXI_03_ARLEN) begin
//   if (AXI_03_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_03_ARLEN is %0h resulting in burst length more than 16", AXI_03_ARLEN);
//   end
// end
// 
// always @ (AXI_04_ARLEN) begin
//   if (AXI_04_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_04_ARLEN is %0h resulting in burst length more than 16", AXI_04_ARLEN);
//   end
// end
// 
// always @ (AXI_05_ARLEN) begin
//   if (AXI_05_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_05_ARLEN is %0h resulting in burst length more than 16", AXI_05_ARLEN);
//   end
// end
// 
// always @ (AXI_06_ARLEN) begin
//   if (AXI_06_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_06_ARLEN is %0h resulting in burst length more than 16", AXI_06_ARLEN);
//   end
// end
// 
// always @ (AXI_07_ARLEN) begin
//   if (AXI_07_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_07_ARLEN is %0h resulting in burst length more than 16", AXI_07_ARLEN);
//   end
// end
// 
// always @ (AXI_08_ARLEN) begin
//   if (AXI_08_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_08_ARLEN is %0h resulting in burst length more than 16", AXI_08_ARLEN);
//   end
// end
// 
// always @ (AXI_09_ARLEN) begin
//   if (AXI_09_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_09_ARLEN is %0h resulting in burst length more than 16", AXI_09_ARLEN);
//   end
// end
// 
// always @ (AXI_10_ARLEN) begin
//   if (AXI_10_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_10_ARLEN is %0h resulting in burst length more than 16", AXI_10_ARLEN);
//   end
// end
// 
// always @ (AXI_11_ARLEN) begin
//   if (AXI_11_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_11_ARLEN is %0h resulting in burst length more than 16", AXI_11_ARLEN);
//   end
// end
// 
// always @ (AXI_12_ARLEN) begin
//   if (AXI_12_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_12_ARLEN is %0h resulting in burst length more than 16", AXI_12_ARLEN);
//   end
// end
// 
// always @ (AXI_13_ARLEN) begin
//   if (AXI_13_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_13_ARLEN is %0h resulting in burst length more than 16", AXI_13_ARLEN);
//   end
// end
// 
// always @ (AXI_14_ARLEN) begin
//   if (AXI_14_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_14_ARLEN is %0h resulting in burst length more than 16", AXI_14_ARLEN);
//   end
// end
// 
// always @ (AXI_15_ARLEN) begin
//   if (AXI_15_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_15_ARLEN is %0h resulting in burst length more than 16", AXI_15_ARLEN);
//   end
// end
// 
// always @ (AXI_16_ARLEN) begin
//   if (AXI_16_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_16_ARLEN is %0h resulting in burst length more than 16", AXI_16_ARLEN);
//   end
// end
// 
// always @ (AXI_17_ARLEN) begin
//   if (AXI_17_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_17_ARLEN is %0h resulting in burst length more than 16", AXI_17_ARLEN);
//   end
// end
// 
// always @ (AXI_18_ARLEN) begin
//   if (AXI_18_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_18_ARLEN is %0h resulting in burst length more than 16", AXI_18_ARLEN);
//   end
// end
// 
// always @ (AXI_19_ARLEN) begin
//   if (AXI_19_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_19_ARLEN is %0h resulting in burst length more than 16", AXI_19_ARLEN);
//   end
// end
// 
// always @ (AXI_20_ARLEN) begin
//   if (AXI_20_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_20_ARLEN is %0h resulting in burst length more than 16", AXI_20_ARLEN);
//   end
// end
// 
// always @ (AXI_21_ARLEN) begin
//   if (AXI_21_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_21_ARLEN is %0h resulting in burst length more than 16", AXI_21_ARLEN);
//   end
// end
// 
// always @ (AXI_22_ARLEN) begin
//   if (AXI_22_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_22_ARLEN is %0h resulting in burst length more than 16", AXI_22_ARLEN);
//   end
// end
// 
// always @ (AXI_23_ARLEN) begin
//   if (AXI_23_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_23_ARLEN is %0h resulting in burst length more than 16", AXI_23_ARLEN);
//   end
// end
// 
// always @ (AXI_24_ARLEN) begin
//   if (AXI_24_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_24_ARLEN is %0h resulting in burst length more than 16", AXI_24_ARLEN);
//   end
// end
// 
// always @ (AXI_25_ARLEN) begin
//   if (AXI_25_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_25_ARLEN is %0h resulting in burst length more than 16", AXI_25_ARLEN);
//   end
// end
// 
// always @ (AXI_26_ARLEN) begin
//   if (AXI_26_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_26_ARLEN is %0h resulting in burst length more than 16", AXI_26_ARLEN);
//   end
// end
// 
// always @ (AXI_27_ARLEN) begin
//   if (AXI_27_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_27_ARLEN is %0h resulting in burst length more than 16", AXI_27_ARLEN);
//   end
// end
// 
// always @ (AXI_28_ARLEN) begin
//   if (AXI_28_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_28_ARLEN is %0h resulting in burst length more than 16", AXI_28_ARLEN);
//   end
// end
// 
// always @ (AXI_29_ARLEN) begin
//   if (AXI_29_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_29_ARLEN is %0h resulting in burst length more than 16", AXI_29_ARLEN);
//   end
// end
// 
// always @ (AXI_30_ARLEN) begin
//   if (AXI_30_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_30_ARLEN is %0h resulting in burst length more than 16", AXI_30_ARLEN);
//   end
// end
// 
// always @ (AXI_31_ARLEN) begin
//   if (AXI_31_ARLEN[7:4] != 4'h0) begin
//     $error("ERROR :: Maximum supported Burst Length for HBM is 16. Value of AXI_31_ARLEN is %0h resulting in burst length more than 16", AXI_31_ARLEN);
//   end
// end
// // synthesis translate on

endmodule


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
/******************************************************************************
******************************************************************************/
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor             : AMD
// \   \   \/     Version            : 1.0
//  \   \         Application        : MIG
//  /   /         Filename           : hbm_apb_mst.sv
// /___/   /\     Date Last Modified : $Date$
// \   \  /  \    Date Created       : Tue Jan 3 2017
//  \___\/\___\
//
//Device: UltraScale+ HBM
//Design Name: HBM
//*****************************************************************************

`timescale 1ps / 1ps
////////////////////////////////////////////////////////////////////////////////
// Module Declaration
////////////////////////////////////////////////////////////////////////////////
module hbm_apb_mst #(
  parameter        INIT_BYPASS      = "FALSE",
  parameter [23:0] INIT_SEQ_TIMEOUT = 10000000,
  parameter        APB_ADDR_WIDTH   = 21,
  parameter        APB_DATA_WIDTH   = 32
) (
   input                       apb_clk
  ,input                       apb_rst_n

  ,output                      apb_back_press
  ,input                       init_seq_complete
  ,input                       gen_apb_tran
  ,input                       gen_apb_wr_rd
  ,input                       gen_poll
  ,input [APB_ADDR_WIDTH-1:0]  gen_apb_addr
  ,input [APB_DATA_WIDTH-1:0]  gen_apb_data
  ,output                      apb_switch
  ,output                      apb_poll_complete
  ,output                      valid_window_fail

  ,output                      psel
  ,output                      pwrite
  ,output                      penable
  ,output [APB_ADDR_WIDTH-1:0] paddr
  ,output [APB_DATA_WIDTH-1:0] pwdata
  ,input  [APB_DATA_WIDTH-1:0] prdata
  ,input                       pready
  ,input                       pslverr

);

////////////////////////////////////////////////////////////////////////////////
// Internal Parameter declaration
////////////////////////////////////////////////////////////////////////////////
localparam C_IDLE    = 3'b001;
localparam C_SETUP   = 3'b010;
localparam C_ACCESS  = 3'b100;

////////////////////////////////////////////////////////////////////////////////
// Internal Wire / Reg Declaration
////////////////////////////////////////////////////////////////////////////////
wire                      apb_switch_s;

reg  [2:0]                curr_state;
reg  [2:0]                nxt_state;
reg  [1:0]                data_cnt_r;
reg                       wr_rd_store_0;
reg                       wr_rd_store_1;
reg  [APB_ADDR_WIDTH-1:0] addr_store_0;
reg  [APB_ADDR_WIDTH-1:0] addr_store_1;
reg  [APB_DATA_WIDTH-1:0] data_store_0;
reg  [APB_DATA_WIDTH-1:0] data_store_1;
reg                       apb_psel_r;
reg                       apb_pwrite_r;
reg                       apb_penable_r;
reg  [APB_ADDR_WIDTH-1:0] apb_paddr_r;
reg  [APB_DATA_WIDTH-1:0] apb_pwdata_r;
reg                       apb_back_press_r;
reg                       apb_poll_complete_r;
reg                       gen_poll_r;
reg                       polling_r;
reg  [APB_ADDR_WIDTH-1:0] gen_apb_addr_r;
reg  [APB_DATA_WIDTH-1:0] gen_apb_data_r;
reg                       apb_switch_r;
reg                       gen_apb_wr_rd_r;
reg                       reading_r;
reg                       apb_read_complete_r;
reg                       valid_window_fail_r;
reg                       valid_window_fail_latch_r;
reg  [23:0]               timeout_cnt_r;
reg                       apb_timeout_r;

////////////////////////////////////////////////////////////////////////////////
// Assigning current state value for APB FSM
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    curr_state <= C_IDLE ;
  end else begin
    curr_state <= nxt_state ;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Assigning next state value for APB FSM
////////////////////////////////////////////////////////////////////////////////
always @ (*) begin
  case (curr_state)
    C_IDLE : begin
      if (gen_apb_tran == 1'b1 && init_seq_complete == 1'b0) begin
        nxt_state = C_SETUP;
      end else begin
        nxt_state = C_IDLE;
      end
    end
    C_SETUP : begin
      nxt_state = C_ACCESS;
    end
    C_ACCESS : begin
      if (pready == 1'b1 && polling_r == 1'b1 && apb_poll_complete_r == 1'b1) begin
        nxt_state = C_IDLE;
      end else if (pready == 1'b1 && polling_r == 1'b0 && reading_r == 1'b1 && apb_read_complete_r == 1'b1) begin
        nxt_state = C_IDLE;
      end else if (pready == 1'b1 && (data_cnt_r > 2'b00 || gen_apb_tran == 1'b1 || (polling_r == 1'b1 && apb_poll_complete_r == 1'b0))) begin
        nxt_state = C_SETUP;
      end else if (pready == 1'b1 && data_cnt_r == 2'b00 && gen_apb_tran == 1'b0) begin
        nxt_state = C_IDLE;
      end else begin
        nxt_state = C_ACCESS;
      end
    end
    default : nxt_state = C_IDLE;
  endcase
end

////////////////////////////////////////////////////////////////////////////////
// Registering the polling bit to indicate FSM for performing polling operation
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    gen_poll_r <= 1'b0 ;
  end else if (apb_poll_complete_r == 1'b1) begin
    gen_poll_r <= 1'b0 ;
  end else if (gen_poll == 1'b1) begin
    gen_poll_r <= 1'b1 ;
  end
end

always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    polling_r <= 1'b0 ;
  end else if (apb_poll_complete_r == 1'b1) begin
    polling_r <= 1'b0 ;
  end else if (gen_poll_r == 1'b1 && (nxt_state == C_ACCESS) && (curr_state == C_SETUP) && (data_cnt_r == 2'b01)) begin
    polling_r <= 1'b1 ;
  end else if (gen_poll_r == 1'b1 && (curr_state == C_ACCESS) && (nxt_state == C_SETUP) && (data_cnt_r == 2'b01)) begin
    polling_r <= 1'b1 ;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Incrementing a timeout counter when polling is happening. After pre-defined
// attempts if polling is not complete, assert timeout flag.
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    timeout_cnt_r <= 24'h00_0000 ;
  end else if (apb_poll_complete_r == 1'b1) begin
    timeout_cnt_r <= 24'h00_0000 ;
  end else if (curr_state == C_ACCESS && nxt_state == C_SETUP && polling_r == 1'b1 && (INIT_SEQ_TIMEOUT != 24'h000000)) begin
    timeout_cnt_r <= timeout_cnt_r + 24'h00_0001 ;
  end
end

always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    apb_timeout_r <= 1'b0 ;
  end else if (INIT_SEQ_TIMEOUT == 24'h000000) begin
    apb_timeout_r <= 1'b0 ;
  end else if (timeout_cnt_r == INIT_SEQ_TIMEOUT) begin
    apb_timeout_r <= 1'b1 ;
  end
end


////////////////////////////////////////////////////////////////////////////////
// Registering the data when transaction request comes
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    gen_apb_addr_r <= {APB_ADDR_WIDTH{1'b0}};
    gen_apb_data_r <= {APB_DATA_WIDTH{1'b0}};
  end else if (gen_apb_tran) begin
    gen_apb_addr_r <= gen_apb_addr;
    gen_apb_data_r <= gen_apb_data;
  end
end

////////////////////////////////////////////////////////////////////////////////
// For polling read transactions, generating polling done flag when the read
// data matches the expected value
////////////////////////////////////////////////////////////////////////////////
always @ (curr_state or pready or prdata or gen_apb_data_r or polling_r) begin
  if ((curr_state == C_ACCESS) && (pready == 1'b1) && (polling_r == 1'b1)) begin
    if (prdata == gen_apb_data_r) begin
      apb_poll_complete_r = 1'b1;
    end else begin
      apb_poll_complete_r = 1'b0;
    end
  end else begin
    apb_poll_complete_r = 1'b0;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Registering the write-read signal. This will be used for comparing data in
// case of read operation
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    gen_apb_wr_rd_r <= 1'b0;
  end else if (apb_read_complete_r) begin
    gen_apb_wr_rd_r <= 1'b0;
  end else if (gen_apb_tran && gen_apb_wr_rd) begin
    gen_apb_wr_rd_r <= 1'b1;
  end
end

always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    reading_r <= 1'b0 ;
  end else if (apb_read_complete_r == 1'b1) begin
    reading_r <= 1'b0 ;
  end else if (gen_apb_wr_rd_r == 1'b1 && (nxt_state == C_ACCESS) && (curr_state == C_SETUP) && (data_cnt_r == 2'b01)) begin
    reading_r <= 1'b1 ;
  end else if (gen_apb_wr_rd_r == 1'b1 && (curr_state == C_ACCESS) && (nxt_state == C_SETUP) && (data_cnt_r == 2'b01)) begin
    reading_r <= 1'b1 ;
  end
end

////////////////////////////////////////////////////////////////////////////////
// For read transactions, generating read done flag when the pready is asserted
////////////////////////////////////////////////////////////////////////////////
always @ (curr_state or pready or prdata or gen_apb_wr_rd_r or reading_r) begin
  if ((curr_state == C_ACCESS) && (pready == 1'b1) && (gen_apb_wr_rd_r == 1'b1) && (reading_r == 1'b1)) begin
    apb_read_complete_r = 1'b1;
  end else begin
    apb_read_complete_r = 1'b0;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Checking the read data of Valid window status register. If the Valid window
// read data is not matching the expected data assert a traing_fail flag
////////////////////////////////////////////////////////////////////////////////
always @ (curr_state or pready or prdata or gen_apb_addr_r or gen_apb_data_r or reading_r) begin
  if ((curr_state == C_ACCESS) && (pready == 1'b1) && (reading_r == 1'b1) &&
      (gen_apb_addr_r == 22'h00_0060 || gen_apb_addr_r == 22'h02_0060 ||
       gen_apb_addr_r == 22'h04_0060 || gen_apb_addr_r == 22'h06_0060 ||
       gen_apb_addr_r == 22'h08_0060 || gen_apb_addr_r == 22'h0a_0060 ||
       gen_apb_addr_r == 22'h0c_0060 || gen_apb_addr_r == 22'h0e_0060)) begin
    if (prdata[31:30] == gen_apb_data_r[31:30]) begin
      valid_window_fail_r = 1'b0;
    end else begin
      valid_window_fail_r = 1'b1;
    end
  end else begin
    valid_window_fail_r = 1'b0;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Latching the training_fail flag forever until system reset
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    valid_window_fail_latch_r <= 1'b0;
  end else if (valid_window_fail_r)begin
    valid_window_fail_latch_r <= 1'b1;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Storing the data fetched from BRAM when APB is not ready to transfer the data
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    data_cnt_r <= 2'b00;
  end else if (curr_state == C_SETUP && gen_apb_tran == 1'b0 && (data_cnt_r != 2'b00) && (polling_r == 1'b0) && (reading_r == 1'b0)) begin
    data_cnt_r <= data_cnt_r - 1'b1;
  end else if (curr_state == C_ACCESS && ((polling_r == 1'b1 && apb_poll_complete_r == 1'b1) || (polling_r == 1'b0 && reading_r == 1'b1 && apb_read_complete_r == 1'b1)) && (data_cnt_r != 2'b00)) begin
    data_cnt_r <= data_cnt_r - 1'b1;
  end else if (gen_apb_tran == 1'b1 && (curr_state == C_IDLE || curr_state == C_ACCESS) && init_seq_complete == 1'b0) begin
    data_cnt_r <= data_cnt_r + 1'b1;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Storing the address for transmitting over APB interface. This is required in
// case of backpressure situation (i.e. when pready not asserted in time). Till
// the backpressure reaches the FETCH logic module maximum of two addr-data pair
// would have been read already. So need to store these two data in two
// registers.
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    addr_store_0  <= {APB_ADDR_WIDTH{1'b0}};
    wr_rd_store_0 <= 1'b0;
  end else if (curr_state == C_SETUP && data_cnt_r == 2'b01 && gen_apb_tran == 1'b1) begin
    addr_store_0  <= gen_apb_addr;
    wr_rd_store_0 <= gen_apb_wr_rd;
  end else if (curr_state == C_SETUP && data_cnt_r == 2'b01 && polling_r == 1'b0) begin
    addr_store_0  <= {APB_ADDR_WIDTH{1'b0}};
    wr_rd_store_0 <= 1'b0;
  end else if (curr_state == C_SETUP && data_cnt_r > 2'b01) begin
    addr_store_0  <= addr_store_1;
    wr_rd_store_0 <= wr_rd_store_1;
  end else if (gen_apb_tran == 1'b1 && data_cnt_r == 2'b00) begin
    addr_store_0  <= gen_apb_addr;
    wr_rd_store_0 <= gen_apb_wr_rd;
  end
end

always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    addr_store_1  <= {APB_ADDR_WIDTH{1'b0}};
    wr_rd_store_1 <= 1'b0;
  end else if (curr_state == C_SETUP && data_cnt_r >= 2'b10) begin
    addr_store_1  <= {APB_ADDR_WIDTH{1'b0}};
    wr_rd_store_1 <= 1'b0;
  end else if (gen_apb_tran == 1'b1 && data_cnt_r == 2'b01 && curr_state != C_SETUP) begin
    addr_store_1  <= gen_apb_addr;
    wr_rd_store_1 <= gen_apb_wr_rd;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Storing the data for transmitting over APB interface. This is required in
// case of backpressure situation (i.e. when pready not asserted in time). Till
// the backpressure reaches the FETCH logic module maximum of two addr-data pair
// would have been read already. So need to store these two data in two
// registers.
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    data_store_0 <= {APB_ADDR_WIDTH{1'b0}};
  end else if (curr_state == C_SETUP && data_cnt_r == 2'b01 && gen_apb_tran == 1'b1) begin
    data_store_0 <= gen_apb_data;
  end else if (curr_state == C_SETUP && data_cnt_r == 2'b01 && polling_r == 1'b0) begin
    data_store_0 <= {APB_ADDR_WIDTH{1'b0}};
  end else if (curr_state == C_SETUP && data_cnt_r > 2'b01) begin
    data_store_0 <= data_store_1;
  end else if (gen_apb_tran == 1'b1 && data_cnt_r == 2'b00) begin
    data_store_0 <= gen_apb_data;
  end
end

always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    data_store_1 <= {APB_ADDR_WIDTH{1'b0}};
  end else if (curr_state == C_SETUP && data_cnt_r >= 2'b10) begin
    data_store_1 <= {APB_ADDR_WIDTH{1'b0}};
  end else if (gen_apb_tran == 1'b1 && data_cnt_r == 2'b01 && curr_state != C_SETUP) begin
    data_store_1 <= gen_apb_data;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Driving the APB output singals
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    apb_psel_r    <= 1'b0;
    apb_pwrite_r  <= 1'b0;
    apb_penable_r <= 1'b0;
    apb_paddr_r   <= {APB_ADDR_WIDTH{1'b0}};
    apb_pwdata_r  <= {APB_DATA_WIDTH{1'b0}};
  end else if (curr_state == C_IDLE && nxt_state == C_SETUP) begin
    apb_psel_r    <= 1'b1;
    apb_pwrite_r  <= ~gen_apb_wr_rd;
    apb_penable_r <= 1'b0;
    apb_paddr_r   <= gen_apb_addr;
    apb_pwdata_r  <= gen_apb_data;
  end else if (curr_state == C_ACCESS && nxt_state == C_SETUP && data_cnt_r == 2'b00) begin
    apb_psel_r    <= 1'b1;
    apb_pwrite_r  <= ~gen_apb_wr_rd;
    apb_penable_r <= 1'b0;
    apb_paddr_r   <= gen_apb_addr;
    apb_pwdata_r  <= gen_apb_data;
  end else if (curr_state == C_ACCESS && nxt_state == C_SETUP && data_cnt_r != 2'b00) begin
    apb_psel_r    <= 1'b1;
    apb_pwrite_r  <= ~wr_rd_store_0;
    apb_penable_r <= 1'b0;
    apb_paddr_r   <= addr_store_0;
    apb_pwdata_r  <= data_store_0;
  end else if (curr_state == C_SETUP && nxt_state == C_ACCESS) begin
    apb_psel_r    <= 1'b1;
    apb_pwrite_r  <= apb_pwrite_r;
    apb_penable_r <= 1'b1;
    apb_paddr_r   <= apb_paddr_r;
    apb_pwdata_r  <= apb_pwdata_r;
  end else if (curr_state == C_ACCESS && nxt_state == C_IDLE) begin
    apb_psel_r    <= 1'b0;
    apb_pwrite_r  <= 1'b0;
    apb_penable_r <= 1'b0;
    apb_paddr_r   <= {APB_ADDR_WIDTH{1'b0}};
    apb_pwdata_r  <= {APB_DATA_WIDTH{1'b0}};
  end
end

////////////////////////////////////////////////////////////////////////////////
// Generating a back pressure flag when PRADY is not asserted immediately in the
// C_ACCESS state
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    apb_back_press_r    <= 1'b0;
  end else if (curr_state == C_IDLE && gen_apb_tran == 1'b1) begin
    apb_back_press_r    <= 1'b1;
  end else if (curr_state == C_SETUP) begin
    apb_back_press_r    <= 1'b1;
  end else if (gen_poll_r == 1'b1 && apb_poll_complete_r == 1'b0) begin
    apb_back_press_r    <= 1'b1;
  end else if (curr_state == C_ACCESS && gen_apb_tran == 1'b1) begin
    apb_back_press_r    <= 1'b1;
  end else if (curr_state == C_ACCESS && nxt_state == C_SETUP) begin
    apb_back_press_r    <= 1'b1;
  end else if (curr_state == C_ACCESS && data_cnt_r > 2'b00) begin
    apb_back_press_r    <= 1'b1;
  end else if (curr_state == C_ACCESS && apb_penable_r == 1'b1) begin
    apb_back_press_r    <= 1'b0;
  end else begin
    apb_back_press_r    <= 1'b0;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Assering to a flag for MUX select that switches the APB interface control to
// user
////////////////////////////////////////////////////////////////////////////////
assign apb_switch_s = (INIT_BYPASS == "TRUE") ? 1'b1 : ((init_seq_complete && (curr_state == C_IDLE)) || apb_timeout_r);
//assign apb_switch_s = (INIT_BYPASS == "TRUE") ? 1'b1 : ((init_seq_complete && (curr_state == C_IDLE)));

////////////////////////////////////////////////////////////////////////////////
// Registering the apb_switch signal to give it to output
// This signal indicats that the initialization of all MCs completed.
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    apb_switch_r <= 1'b0;
  end else begin
    apb_switch_r <= apb_switch_s;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Assigning output signals
////////////////////////////////////////////////////////////////////////////////
assign apb_back_press        = apb_back_press_r;
assign apb_poll_complete     = apb_poll_complete_r;
assign psel                  = apb_psel_r;
assign pwrite                = apb_pwrite_r;  
assign penable               = apb_penable_r;   
assign paddr                 = apb_paddr_r;  
assign pwdata                = apb_pwdata_r;  
assign apb_switch            = apb_switch_r;
assign valid_window_fail     = valid_window_fail_latch_r;

endmodule


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
/******************************************************************************
******************************************************************************/
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor             : AMD
// \   \   \/     Version            : 1.0
//  \   \         Application        : MIG
//  /   /         Filename           : hbm_temp_rd.sv
// /___/   /\     Date Last Modified : $Date$
// \   \  /  \    Date Created       : Tue Jan 3 2017
//  \___\/\___\
//
//Device: UltraScale+ HBM
//Design Name: HBM
//*****************************************************************************

`timescale 1ps / 1ps
////////////////////////////////////////////////////////////////////////////////
// Module Declaration
////////////////////////////////////////////////////////////////////////////////
module hbm_temp_rd #(
  parameter TEMP_WAIT_PERIOD = 32'hffff_ffff,
  parameter APB_ADDR_WIDTH   = 21,
  parameter APB_DATA_WIDTH   = 32
) (
   input                       apb_clk
  ,input                       apb_rst_n

  ,output                      temp_apb_req
  ,input                       temp_apb_grant
  ,input                       init_seq_complete

  ,output                      temp_valid
  ,output [6:0]                temp_value

  ,output                      psel
  ,output                      pwrite
  ,output                      penable
  ,output [APB_ADDR_WIDTH-1:0] paddr
  ,output [APB_DATA_WIDTH-1:0] pwdata
  ,input  [APB_DATA_WIDTH-1:0] prdata
  ,input                       pready
  ,input                       pslverr

);

////////////////////////////////////////////////////////////////////////////////
// Main Temperature Reading FSM Parameter declaration
////////////////////////////////////////////////////////////////////////////////
localparam C_IDLE                 = 6'b000001;
localparam C_WAIT_INTRVL          = 6'b000010;
localparam C_APB_ACC_REQ          = 6'b000100;
localparam C_SEND_TEMP_ACC_CMD    = 6'b001000;
localparam C_POLL_TEMP_ACC_CMD_ST = 6'b010000;
localparam C_READ_TEMP            = 6'b100000;

////////////////////////////////////////////////////////////////////////////////
// APB FSM parameter declaration
////////////////////////////////////////////////////////////////////////////////
localparam C_APB_IDLE   = 3'b001;
localparam C_APB_SETUP  = 3'b010;
localparam C_APB_ACCESS = 3'b100;

////////////////////////////////////////////////////////////////////////////////
// Internal Wire / Reg Declaration
////////////////////////////////////////////////////////////////////////////////
reg  [5:0]                main_fsm_curr_state;
reg  [5:0]                main_fsm_nxt_state;
reg  [2:0]                apb_fsm_curr_state;
reg  [2:0]                apb_fsm_nxt_state;
reg  [31:0]               wait_cnt_r;
reg                       temp_apb_req_r;
reg                       temp_valid_r;
reg  [6:0]                temp_value_r;
reg                       wr_rd_store_r;
reg  [APB_ADDR_WIDTH-1:0] addr_store_r;
reg  [APB_DATA_WIDTH-1:0] data_store_r;
reg                       apb_psel_r;
reg                       apb_pwrite_r;
reg                       apb_penable_r;
reg  [APB_ADDR_WIDTH-1:0] apb_paddr_r;
reg  [APB_DATA_WIDTH-1:0] apb_pwdata_r;
reg                       apb_busy_r;
reg                       apb_poll_complete_r;
reg                       gen_poll_r;
reg                       polling_r;
reg  [APB_ADDR_WIDTH-1:0] gen_apb_addr_r;
reg  [APB_DATA_WIDTH-1:0] gen_apb_data_r;
reg                       apb_switch_r;
reg                       gen_wr_rd_r;
reg                       reading_r;
reg                       apb_read_complete_r;
reg                       gen_apb_tran_r;
reg                       gen_apb_wr_rd_r;
reg                       gen_apb_poll_r;

////////////////////////////////////////////////////////////////////////////////
// Assigning current state value for APB FSM
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    main_fsm_curr_state <= C_IDLE ;
  end else begin
    main_fsm_curr_state <= main_fsm_nxt_state ;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Assigning next state value for APB FSM
////////////////////////////////////////////////////////////////////////////////
always @ (*) begin
  case (main_fsm_curr_state)
    C_IDLE : begin
      if (init_seq_complete == 1'b1) begin
        main_fsm_nxt_state = C_WAIT_INTRVL;
      end else begin
        main_fsm_nxt_state = C_IDLE;
      end
    end
    C_WAIT_INTRVL : begin
      if (wait_cnt_r == TEMP_WAIT_PERIOD) begin
        main_fsm_nxt_state = C_APB_ACC_REQ;
      end else begin
        main_fsm_nxt_state = C_WAIT_INTRVL;
      end
    end
    C_APB_ACC_REQ : begin
      if (temp_apb_grant == 1'b1) begin
        main_fsm_nxt_state = C_SEND_TEMP_ACC_CMD;
      end else begin
        main_fsm_nxt_state = C_APB_ACC_REQ;
      end
    end
    C_SEND_TEMP_ACC_CMD : begin
      if (gen_apb_tran_r == 1'b0 && apb_busy_r == 1'b0) begin
        main_fsm_nxt_state = C_POLL_TEMP_ACC_CMD_ST;
      end else begin
        main_fsm_nxt_state = C_SEND_TEMP_ACC_CMD;
      end
    end
    C_POLL_TEMP_ACC_CMD_ST : begin
      if (gen_apb_tran_r == 1'b0 && apb_busy_r == 1'b0) begin
        main_fsm_nxt_state = C_READ_TEMP;
      end else begin
        main_fsm_nxt_state = C_POLL_TEMP_ACC_CMD_ST;
      end
    end
    C_READ_TEMP : begin
      if (gen_apb_tran_r == 1'b0 && apb_busy_r == 1'b0) begin
        main_fsm_nxt_state = C_WAIT_INTRVL;
      end else begin
        main_fsm_nxt_state = C_READ_TEMP;
      end
    end
    default : main_fsm_nxt_state = C_IDLE;
  endcase
end

////////////////////////////////////////////////////////////////////////////////
// Counter implemeneted to count interval between two succesive temperature read
// access
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    wait_cnt_r <= 32'h0000_0000;
  end else if (main_fsm_curr_state != C_WAIT_INTRVL) begin
    wait_cnt_r <= 32'h0000_0000;
  end else if (main_fsm_curr_state == C_WAIT_INTRVL) begin
    wait_cnt_r <= wait_cnt_r + 1'b1;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Generating APB bus request for readin IEEE1500 Temperature sensor register
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    temp_apb_req_r <= 1'b0;
  end else if (main_fsm_curr_state != C_IDLE && main_fsm_curr_state != C_WAIT_INTRVL) begin
    temp_apb_req_r <= 1'b1;
  end else begin
    temp_apb_req_r <= 1'b0;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Generating APB transaction command at different stages.
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    gen_apb_tran_r  <= 1'b0;
    gen_apb_wr_rd_r <= 1'b0;
    gen_apb_poll_r  <= 1'b0;
    gen_apb_addr_r  <= 22'h00_0000;
    gen_apb_data_r  <= 32'h0000_0000;
  end else if (main_fsm_curr_state == C_APB_ACC_REQ && main_fsm_nxt_state == C_SEND_TEMP_ACC_CMD) begin
    gen_apb_tran_r  <= 1'b1;
    gen_apb_wr_rd_r <= 1'b0;
    gen_apb_poll_r  <= 1'b0;
    gen_apb_addr_r  <= 22'h24_0004;
    gen_apb_data_r  <= 32'h00A0_800F;
  end else if (main_fsm_curr_state == C_SEND_TEMP_ACC_CMD && main_fsm_nxt_state == C_POLL_TEMP_ACC_CMD_ST) begin
    gen_apb_tran_r  <= 1'b1;
    gen_apb_wr_rd_r <= 1'b1;
    gen_apb_poll_r  <= 1'b1;
    gen_apb_addr_r  <= 22'h24_0004;
    gen_apb_data_r  <= 32'h0020_800F;
  end else if (main_fsm_curr_state == C_POLL_TEMP_ACC_CMD_ST && main_fsm_nxt_state == C_POLL_TEMP_ACC_CMD_ST) begin
    gen_apb_tran_r  <= 1'b0;
    gen_apb_wr_rd_r <= 1'b0;
    gen_apb_poll_r  <= 1'b0;
    gen_apb_addr_r  <= 22'h24_0004;
    gen_apb_data_r  <= 32'h0020_800F;
  end else if (main_fsm_curr_state == C_POLL_TEMP_ACC_CMD_ST && main_fsm_nxt_state == C_READ_TEMP) begin
    gen_apb_tran_r  <= 1'b1;
    gen_apb_wr_rd_r <= 1'b1;
    gen_apb_poll_r  <= 1'b0;
    gen_apb_addr_r  <= 22'h24_000C;
    gen_apb_data_r  <= 32'h0020_800F;
  end else begin
    gen_apb_tran_r  <= 1'b0;
    gen_apb_wr_rd_r <= 1'b0;
    gen_apb_poll_r  <= 1'b0;
    gen_apb_addr_r  <= 22'h00_0000;
    gen_apb_data_r  <= 32'h0000_0000;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Storing the temperature data read through IEEE1500 interface
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    temp_valid_r <= 1'b0;
    temp_value_r <= 7'b000_0000;
  end else if (main_fsm_curr_state == C_READ_TEMP && pready == 1'b1) begin
    temp_valid_r <= prdata[31];
    temp_value_r <= prdata[30:24];
  end else begin
    temp_valid_r <= 1'b0;
    temp_value_r <= temp_value_r;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Assigning current state value for APB FSM
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    apb_fsm_curr_state <= C_IDLE ;
  end else begin
    apb_fsm_curr_state <= apb_fsm_nxt_state ;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Assigning next state value for APB FSM
////////////////////////////////////////////////////////////////////////////////
always @ (*) begin
  case (apb_fsm_curr_state)
    C_APB_IDLE : begin
      if (gen_apb_tran_r == 1'b1) begin
        apb_fsm_nxt_state = C_APB_SETUP;
      end else begin
        apb_fsm_nxt_state = C_APB_IDLE;
      end
    end
    C_APB_SETUP : begin
      apb_fsm_nxt_state = C_APB_ACCESS;
    end
    C_APB_ACCESS : begin
      if (pready == 1'b1 && polling_r == 1'b1 && apb_poll_complete_r == 1'b1) begin
        apb_fsm_nxt_state = C_APB_IDLE;
      end else if (pready == 1'b1 && polling_r == 1'b0 && reading_r == 1'b1 && apb_read_complete_r == 1'b1) begin
        apb_fsm_nxt_state = C_APB_IDLE;
      end else if (pready == 1'b1 && polling_r == 1'b0 && reading_r == 1'b0) begin
        apb_fsm_nxt_state = C_APB_IDLE;
      end else if (pready == 1'b1 && (polling_r == 1'b1 && apb_poll_complete_r == 1'b0)) begin
        apb_fsm_nxt_state = C_APB_SETUP;
      end else begin
        apb_fsm_nxt_state = C_APB_ACCESS;
      end
    end
    default : apb_fsm_nxt_state = C_APB_IDLE;
  endcase
end

////////////////////////////////////////////////////////////////////////////////
// Registering the polling bit to indicate FSM for performing polling operation
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    gen_poll_r <= 1'b0 ;
  end else if (apb_poll_complete_r == 1'b1) begin
    gen_poll_r <= 1'b0 ;
  end else if (gen_apb_poll_r == 1'b1) begin
    gen_poll_r <= 1'b1 ;
  end
end

always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    polling_r <= 1'b0 ;
  end else if (apb_poll_complete_r == 1'b1) begin
    polling_r <= 1'b0 ;
  end else if (gen_poll_r == 1'b1 && (apb_fsm_nxt_state == C_APB_ACCESS) && (apb_fsm_curr_state == C_APB_SETUP)) begin
    polling_r <= 1'b1 ;
  end else if (gen_poll_r == 1'b1 && (apb_fsm_curr_state == C_APB_ACCESS) && (apb_fsm_nxt_state == C_APB_SETUP)) begin
    polling_r <= 1'b1 ;
  end
end

////////////////////////////////////////////////////////////////////////////////
// For polling read transactions, generating polling done flag when the read
// data matches the expected value
////////////////////////////////////////////////////////////////////////////////
always @ (apb_fsm_curr_state or pready or prdata or gen_apb_data_r or polling_r) begin
  if ((apb_fsm_curr_state == C_APB_ACCESS) && (pready == 1'b1) && (polling_r == 1'b1)) begin
    if (prdata[23:0] == gen_apb_data_r[23:0]) begin
      apb_poll_complete_r = 1'b1;
    end else begin
      apb_poll_complete_r = 1'b0;
    end
  end else begin
    apb_poll_complete_r = 1'b0;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Registering the write-read signal. This will be used for comparing data in
// case of read operation
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    gen_wr_rd_r <= 1'b0;
  end else if (apb_read_complete_r) begin
    gen_wr_rd_r <= 1'b0;
  end else if (gen_apb_tran_r && gen_apb_wr_rd_r) begin
    gen_wr_rd_r <= 1'b1;
  end
end

always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    reading_r <= 1'b0 ;
  end else if (apb_read_complete_r == 1'b1) begin
    reading_r <= 1'b0 ;
  end else if (gen_wr_rd_r == 1'b1 && (apb_fsm_nxt_state == C_APB_ACCESS) && (apb_fsm_curr_state == C_APB_SETUP)) begin
    reading_r <= 1'b1 ;
  end
end

////////////////////////////////////////////////////////////////////////////////
// For read transactions, generating read done flag when the pready is asserted
////////////////////////////////////////////////////////////////////////////////
always @ (apb_fsm_curr_state or pready or prdata or gen_wr_rd_r or reading_r) begin
  if ((apb_fsm_curr_state == C_APB_ACCESS) && (pready == 1'b1) && (gen_wr_rd_r == 1'b1) && (reading_r == 1'b1)) begin
    apb_read_complete_r = 1'b1;
  end else begin
    apb_read_complete_r = 1'b0;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Storing the address for transmitting over APB interface. This is required in
// case of polling.
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    addr_store_r  <= {APB_ADDR_WIDTH{1'b0}};
    data_store_r  <= {APB_ADDR_WIDTH{1'b0}};
    wr_rd_store_r <= 1'b0;
  end else if (gen_apb_tran_r == 1'b1) begin
    addr_store_r  <= gen_apb_addr_r;
    wr_rd_store_r <= gen_apb_wr_rd_r;
    data_store_r  <= gen_apb_data_r;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Driving the APB output singals
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    apb_psel_r    <= 1'b0;
    apb_pwrite_r  <= 1'b0;
    apb_penable_r <= 1'b0;
    apb_paddr_r   <= {APB_ADDR_WIDTH{1'b0}};
    apb_pwdata_r  <= {APB_DATA_WIDTH{1'b0}};
  end else if (apb_fsm_curr_state == C_IDLE && apb_fsm_nxt_state == C_APB_SETUP) begin
    apb_psel_r    <= 1'b1;
    apb_pwrite_r  <= ~gen_apb_wr_rd_r;
    apb_penable_r <= 1'b0;
    apb_paddr_r   <= gen_apb_addr_r;
    apb_pwdata_r  <= gen_apb_data_r;
  end else if (apb_fsm_curr_state == C_APB_ACCESS && apb_fsm_nxt_state == C_APB_SETUP) begin
    apb_psel_r    <= 1'b1;
    apb_pwrite_r  <= ~wr_rd_store_r;
    apb_penable_r <= 1'b0;
    apb_paddr_r   <= addr_store_r;
    apb_pwdata_r  <= data_store_r;
  end else if (apb_fsm_curr_state == C_APB_SETUP && apb_fsm_nxt_state == C_APB_ACCESS) begin
    apb_psel_r    <= 1'b1;
    apb_pwrite_r  <= apb_pwrite_r;
    apb_penable_r <= 1'b1;
    apb_paddr_r   <= apb_paddr_r;
    apb_pwdata_r  <= apb_pwdata_r;
  end else if (apb_fsm_curr_state == C_APB_ACCESS && apb_fsm_nxt_state == C_IDLE) begin
    apb_psel_r    <= 1'b0;
    apb_pwrite_r  <= 1'b0;
    apb_penable_r <= 1'b0;
    apb_paddr_r   <= {APB_ADDR_WIDTH{1'b0}};
    apb_pwdata_r  <= {APB_DATA_WIDTH{1'b0}};
  end
end

////////////////////////////////////////////////////////////////////////////////
// Generating a busy flag when APB transaction is going on
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    apb_busy_r    <= 1'b0;
  end else if (apb_fsm_curr_state == C_IDLE && gen_apb_tran_r == 1'b1) begin
    apb_busy_r    <= 1'b1;
  end else if (apb_fsm_curr_state == C_APB_ACCESS && apb_fsm_nxt_state == C_APB_IDLE) begin
    apb_busy_r    <= 1'b0;
  end else if (apb_fsm_curr_state == C_APB_SETUP || apb_fsm_curr_state == C_APB_ACCESS) begin
    apb_busy_r    <= 1'b1;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Assigning output signals
////////////////////////////////////////////////////////////////////////////////
assign psel          = apb_psel_r;
assign pwrite        = apb_pwrite_r;  
assign penable       = apb_penable_r;   
assign paddr         = apb_paddr_r;  
assign pwdata        = apb_pwdata_r;  

assign temp_apb_req  = temp_apb_req_r;

assign temp_valid    = temp_valid_r;
assign temp_value    = temp_value_r;

endmodule


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
/******************************************************************************
******************************************************************************/
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor             : AMD
// \   \   \/     Version            : 1.0
//  \   \         Application        : MIG
//  /   /         Filename           : hbm_apb_arbiter.sv
// /___/   /\     Date Last Modified : $Date$
// \   \  /  \    Date Created       : Tue Feb 15 2018
//  \___\/\___\
//
//Device: UltraScale+ HBM
//Design Name: HBM
//*****************************************************************************

`timescale 1ps / 1ps
////////////////////////////////////////////////////////////////////////////////
// Module Declaration
////////////////////////////////////////////////////////////////////////////////
module hbm_apb_arbiter #(
  parameter INIT_BYPASS    = "FALSE",
  parameter APB_ADDR_WIDTH = 21,
  parameter APB_DATA_WIDTH = 32
) (
   input                       apb_clk
  ,input                       apb_rst_n

  ,input                       intrnl_apb_complete
  ,input                       intrnl_apb_psel
  ,input                       intrnl_apb_pwrite
  ,input                       intrnl_apb_penable
  ,input  [APB_ADDR_WIDTH-1:0] intrnl_apb_paddr
  ,input  [APB_DATA_WIDTH-1:0] intrnl_apb_pwdata
  ,output [APB_DATA_WIDTH-1:0] intrnl_apb_prdata
  ,output                      intrnl_apb_pready
  ,output                      intrnl_apb_pslverr

  ,input                       extrnl_apb_psel
  ,input                       extrnl_apb_pwrite
  ,input                       extrnl_apb_penable
  ,input  [APB_ADDR_WIDTH-1:0] extrnl_apb_paddr
  ,input  [APB_DATA_WIDTH-1:0] extrnl_apb_pwdata
  ,output [APB_DATA_WIDTH-1:0] extrnl_apb_prdata
  ,output                      extrnl_apb_pready
  ,output                      extrnl_apb_pslverr

  ,input                       xsdb_apb_req
  ,output                      xsdb_apb_grant
  ,input                       xsdb_apb_psel
  ,input                       xsdb_apb_pwrite
  ,input                       xsdb_apb_penable
  ,input  [APB_ADDR_WIDTH-1:0] xsdb_apb_paddr
  ,input  [APB_DATA_WIDTH-1:0] xsdb_apb_pwdata
  ,output [APB_DATA_WIDTH-1:0] xsdb_apb_prdata
  ,output                      xsdb_apb_pready
  ,output                      xsdb_apb_pslverr

  ,input                       temp_apb_req
  ,output                      temp_apb_grant
  ,input                       temp_apb_psel
  ,input                       temp_apb_pwrite
  ,input                       temp_apb_penable
  ,input  [APB_ADDR_WIDTH-1:0] temp_apb_paddr
  ,input  [APB_DATA_WIDTH-1:0] temp_apb_pwdata
  ,output [APB_DATA_WIDTH-1:0] temp_apb_prdata
  ,output                      temp_apb_pready
  ,output                      temp_apb_pslverr

  ,output                      psel
  ,output                      pwrite
  ,output                      penable
  ,output [APB_ADDR_WIDTH-1:0] paddr
  ,output [APB_DATA_WIDTH-1:0] pwdata
  ,input  [APB_DATA_WIDTH-1:0] prdata
  ,input                       pready
  ,input                       pslverr

);

////////////////////////////////////////////////////////////////////////////////
// Internal Parameter declaration
////////////////////////////////////////////////////////////////////////////////
localparam C_IDLE    = 3'b001;
localparam C_SETUP   = 3'b010;
localparam C_ACCESS  = 3'b100;

////////////////////////////////////////////////////////////////////////////////
// Internal Wire / Reg Declaration
////////////////////////////////////////////////////////////////////////////////
reg  [1:0]                apb_mux_sel_r;
reg                       xsdb_apb_grant_r;
reg                       temp_apb_grant_r;

reg                       apb_psel_r;
reg                       apb_pwrite_r;
reg                       apb_penable_r;
reg  [APB_ADDR_WIDTH-1:0] apb_paddr_r;
reg  [APB_DATA_WIDTH-1:0] apb_pwdata_r;

reg  [APB_DATA_WIDTH-1:0] intrnl_apb_prdata_r;
reg                       intrnl_apb_pready_r;
reg                       intrnl_apb_pslverr_r;

reg  [APB_DATA_WIDTH-1:0] extrnl_apb_prdata_r;
reg                       extrnl_apb_pready_r;
reg                       extrnl_apb_pslverr_r;

reg  [APB_DATA_WIDTH-1:0] xsdb_apb_prdata_r;
reg                       xsdb_apb_pready_r;
reg                       xsdb_apb_pslverr_r;

reg  [APB_DATA_WIDTH-1:0] temp_apb_prdata_r;
reg                       temp_apb_pready_r;
reg                       temp_apb_pslverr_r;

////////////////////////////////////////////////////////////////////////////////
// Generating MUX select based on the APB bus request from different masters.
// Following is the algorithm for granting the APB bus assess to different
// masters.
//
//  MUX SEL     Description
//==============================================================================
//  2'b00       Internal ABP master gets grant. If the INIT_BYPASS is "FALSE"
//              and all transactions of internal APB master not completed the
//              APB interface grants remains with internal APB master
//
//  2'b01       External APB master gets grant. If all internal master
//              transactions are complete and there is no pending request from
//              XSDB master then APB interface grant given to external APB
//              master
//
//  2'b10       XSDB APB master gets grant. When internal master transactions
//              are complete and no transaction going on from external master
//              then if a reqest is asserted from XSDB master the APB interface
//              grant is given to XSDB master
//
//  2'b11       TEMPERATURE APB master gets grant.
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    apb_mux_sel_r <= 2'b00;
  end else if (INIT_BYPASS == "FALSE" && intrnl_apb_complete == 1'b0) begin
    apb_mux_sel_r <= 2'b00;
  end else if ((INIT_BYPASS == "TRUE" || intrnl_apb_complete == 1'b1) && (temp_apb_req == 1'b1) && (((extrnl_apb_psel == 1'b0) && (xsdb_apb_req == 1'b0)) || (((extrnl_apb_psel == 1'b1) || (xsdb_apb_req == 1'b1)) && (apb_mux_sel_r == 2'b11)))) begin
    apb_mux_sel_r <= 2'b11;
  end else if ((INIT_BYPASS == "TRUE" || intrnl_apb_complete == 1'b1) && (temp_apb_req == 1'b1) && (extrnl_apb_psel == 1'b0) && (xsdb_apb_req == 1'b1) && (xsdb_apb_penable == 1'b0)) begin
    apb_mux_sel_r <= 2'b11;
  end else if ((INIT_BYPASS == "TRUE" || intrnl_apb_complete == 1'b1) && (xsdb_apb_req == 1'b0)) begin
    apb_mux_sel_r <= 2'b01;
  end else if ((INIT_BYPASS == "TRUE" || intrnl_apb_complete == 1'b1) && (extrnl_apb_psel == 1'b0) && (xsdb_apb_req == 1'b1)) begin
    apb_mux_sel_r <= 2'b10;
  end
end

//   ////////////////////////////////////////////////////////////////////////////////
//   // Generating Grant for XSDB master
//   ////////////////////////////////////////////////////////////////////////////////
//   always @ (posedge apb_clk or negedge apb_rst_n) begin
//     if (~apb_rst_n) begin
//       xsdb_apb_grant_r <= 1'b0;
//     end else if (xsdb_apb_req == 1'b0) begin
//       xsdb_apb_grant_r <= 1'b0;
//     end else if ((INIT_BYPASS == "TRUE" || intrnl_apb_complete == 1'b1) && (extrnl_apb_psel == 1'b0) && (xsdb_apb_req == 1'b1)) begin
//       xsdb_apb_grant_r <= 1'b1;
//     end
//   end

////////////////////////////////////////////////////////////////////////////////
// APB MUX
////////////////////////////////////////////////////////////////////////////////
always @ (*) begin
  case (apb_mux_sel_r)
    2'b00: begin
      apb_psel_r    = intrnl_apb_psel;
      apb_pwrite_r  = intrnl_apb_pwrite;
      apb_penable_r = intrnl_apb_penable;
      apb_paddr_r   = intrnl_apb_paddr;
      apb_pwdata_r  = intrnl_apb_pwdata;
      xsdb_apb_grant_r = 1'b0;
      temp_apb_grant_r = 1'b0;
    end
    2'b01: begin
      apb_psel_r    = extrnl_apb_psel;
      apb_pwrite_r  = extrnl_apb_pwrite;
      apb_penable_r = extrnl_apb_penable;
      apb_paddr_r   = extrnl_apb_paddr;
      apb_pwdata_r  = extrnl_apb_pwdata;
      xsdb_apb_grant_r = 1'b0;
      temp_apb_grant_r = 1'b0;
    end
    2'b10: begin
      apb_psel_r    = xsdb_apb_psel;
      apb_pwrite_r  = xsdb_apb_pwrite;
      apb_penable_r = xsdb_apb_penable;
      apb_paddr_r   = xsdb_apb_paddr;
      apb_pwdata_r  = xsdb_apb_pwdata;
      xsdb_apb_grant_r = 1'b1;
      temp_apb_grant_r = 1'b0;
    end
    2'b11: begin
      apb_psel_r    = temp_apb_psel;
      apb_pwrite_r  = temp_apb_pwrite;
      apb_penable_r = temp_apb_penable;
      apb_paddr_r   = temp_apb_paddr;
      apb_pwdata_r  = temp_apb_pwdata;
      xsdb_apb_grant_r = 1'b0;
      temp_apb_grant_r = 1'b1;
    end
    default: begin
      apb_psel_r    = 1'b0;
      apb_pwrite_r  = 1'b0;
      apb_penable_r = 1'b0;
      apb_paddr_r   = {APB_ADDR_WIDTH{1'b0}};
      apb_pwdata_r  = {APB_DATA_WIDTH{1'b0}};
      xsdb_apb_grant_r = 1'b0;
      temp_apb_grant_r = 1'b0;
    end
  endcase
end

////////////////////////////////////////////////////////////////////////////////
// APB MUX Internal Master Read data interface
////////////////////////////////////////////////////////////////////////////////
always @ (*) begin
  if (apb_mux_sel_r == 2'b00) begin
    intrnl_apb_prdata_r  = prdata;
    intrnl_apb_pready_r  = pready;
    intrnl_apb_pslverr_r = pslverr;
  end else begin
    intrnl_apb_prdata_r  = {APB_DATA_WIDTH{1'b0}};
    intrnl_apb_pready_r  = 1'b0;
    intrnl_apb_pslverr_r = 1'b0;
  end
end

////////////////////////////////////////////////////////////////////////////////
// APB MUX External Master Read data interface
////////////////////////////////////////////////////////////////////////////////
always @ (*) begin
  if (apb_mux_sel_r == 2'b01) begin
    extrnl_apb_prdata_r  = prdata;
    extrnl_apb_pready_r  = pready;
    extrnl_apb_pslverr_r = pslverr;
  end else begin
    extrnl_apb_prdata_r  = {APB_DATA_WIDTH{1'b0}};
    extrnl_apb_pready_r  = 1'b0;
    extrnl_apb_pslverr_r = 1'b0;
  end
end

////////////////////////////////////////////////////////////////////////////////
// APB MUX XSDB Master Read data interface
////////////////////////////////////////////////////////////////////////////////
always @ (*) begin
  if (apb_mux_sel_r == 2'b10) begin
    xsdb_apb_prdata_r  = prdata;
    xsdb_apb_pready_r  = pready;
    xsdb_apb_pslverr_r = pslverr;
  end else begin
    xsdb_apb_prdata_r  = {APB_DATA_WIDTH{1'b0}};
    xsdb_apb_pready_r  = 1'b0;
    xsdb_apb_pslverr_r = 1'b0;
  end
end

////////////////////////////////////////////////////////////////////////////////
// APB MUX TEMP Master Read data interface
////////////////////////////////////////////////////////////////////////////////
always @ (*) begin
  if (apb_mux_sel_r == 2'b11) begin
    temp_apb_prdata_r  = prdata;
    temp_apb_pready_r  = pready;
    temp_apb_pslverr_r = pslverr;
  end else begin
    temp_apb_prdata_r  = {APB_DATA_WIDTH{1'b0}};
    temp_apb_pready_r  = 1'b0;
    temp_apb_pslverr_r = 1'b0;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Driving output signals
////////////////////////////////////////////////////////////////////////////////
assign psel               = apb_psel_r;
assign pwrite             = apb_pwrite_r;  
assign penable            = apb_penable_r;   
assign paddr              = apb_paddr_r;  
assign pwdata             = apb_pwdata_r;  

assign intrnl_apb_prdata  = intrnl_apb_prdata_r;
assign intrnl_apb_pready  = intrnl_apb_pready_r;
assign intrnl_apb_pslverr = intrnl_apb_pslverr_r;

assign extrnl_apb_prdata  = extrnl_apb_prdata_r;
assign extrnl_apb_pready  = extrnl_apb_pready_r;
assign extrnl_apb_pslverr = extrnl_apb_pslverr_r;

assign xsdb_apb_prdata    = xsdb_apb_prdata_r;
assign xsdb_apb_pready    = xsdb_apb_pready_r;
assign xsdb_apb_pslverr   = xsdb_apb_pslverr_r;
assign xsdb_apb_grant     = xsdb_apb_grant_r;

assign temp_apb_prdata    = temp_apb_prdata_r;
assign temp_apb_pready    = temp_apb_pready_r;
assign temp_apb_pslverr   = temp_apb_pslverr_r;
assign temp_apb_grant     = temp_apb_grant_r;

endmodule


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
/******************************************************************************
******************************************************************************/
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor             : AMD
// \   \   \/     Version            : 1.0
//  \   \         Application        : MIG
//  /   /         Filename           : hbm_data_fetch.sv
// /___/   /\     Date Last Modified : $Date$
// \   \  /  \    Date Created       : Tue Jan 3 2017
//  \___\/\___\
//
//Device: UltraScale+ HBM
//Design Name: HBM
//*****************************************************************************

`timescale 1ps / 1ps
////////////////////////////////////////////////////////////////////////////////
// Module Declaration
////////////////////////////////////////////////////////////////////////////////
module hbm_data_fetch #(
  parameter XPM_ADDR_WIDTH = 8,
  parameter XPM_DATA_WIDTH = 32,
  parameter APB_ADDR_WIDTH = 21,
  parameter APB_DATA_WIDTH = 32
) (
   input apb_clk
  ,input apb_rst_n
  ,output xpm_ena
  ,output xpm_wea
  ,output [XPM_ADDR_WIDTH-1:0] xpm_addra
  ,output [XPM_DATA_WIDTH-1:0] xpm_dina
  ,input  [XPM_DATA_WIDTH-1:0] xpm_douta

  ,input  apb_back_press
  ,input  apb_poll_complete
  ,output init_seq_complete
  ,output gen_apb_tran
  ,output gen_apb_wr_rd
  ,output gen_poll
  ,output [APB_ADDR_WIDTH-1:0] gen_apb_addr
  ,output [APB_DATA_WIDTH-1:0] gen_apb_data

);

////////////////////////////////////////////////////////////////////////////////
// Internal Wire / Reg Declaration
////////////////////////////////////////////////////////////////////////////////
wire                      xpm_ena_s;
wire                      xpm_wea_s;
wire [XPM_DATA_WIDTH-1:0] xpm_dina_s;
wire                      init_seq_complete_s;

reg                       xpm_ena_r;
reg  [XPM_ADDR_WIDTH-1:0] xpm_addra_r;
reg                       init_seq_complete_r;
reg                       addr_data_toggle_r;
reg                       addr_data_toggle_r1;
reg                       addr_data_toggle_r2;
reg                       apb_wr_rd_r;
reg                       apb_poll_r;
reg                       apb_poll_pend_r;
reg                       apb_wr_rd_pend_r;
reg  [APB_ADDR_WIDTH-1:0] apb_addr_pend_r;
reg  [APB_DATA_WIDTH-1:0] apb_data_pend_r;
reg  [APB_ADDR_WIDTH-1:0] apb_addr_r;
reg  [APB_DATA_WIDTH-1:0] apb_data_r;
reg                       data_rcvd_r;
reg                       gen_apb_tran_r;
reg                       gen_apb_wr_rd_r;
reg                       gen_poll_r;
reg  [APB_ADDR_WIDTH-1:0] gen_apb_addr_r;
reg  [APB_DATA_WIDTH-1:0] gen_apb_data_r;
reg                       stall_rd_r;

////////////////////////////////////////////////////////////////////////////////
// Reading from the XPM memory as soon as reset is deactivated. The reading is
// stopped when read data received is reserved value 0xFFFF_FFFF
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk) begin
  if (~apb_rst_n) begin
    xpm_ena_r <= 1'b0;
  end else if (addr_data_toggle_r || addr_data_toggle_r1 || addr_data_toggle_r2 || apb_back_press || init_seq_complete_r) begin
    xpm_ena_r <= 1'b0;
  end else begin
    xpm_ena_r <= 1'b1;
  end
end

assign xpm_ena_s = xpm_ena_r && ~((xpm_douta == 32'hffff_ffff) && addr_data_toggle_r == 1'b1) && ~(apb_poll_pend_r);

////////////////////////////////////////////////////////////////////////////////
// Generating the address to read from XPM memory 
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk) begin
  if (~apb_rst_n) begin
    xpm_addra_r <= {XPM_ADDR_WIDTH{1'b0}};
  end else if (init_seq_complete_r == 1'b1) begin
    xpm_addra_r <= {XPM_ADDR_WIDTH{1'b0}};
  end else if (xpm_ena_r == 1'b1 && apb_poll_pend_r == 1'b0) begin
    xpm_addra_r <= xpm_addra_r + 1'b1;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Driving all bits of WEA and DINA signals to '0'. This is done as only read
// transactions are performed to XPM memory
////////////////////////////////////////////////////////////////////////////////
assign xpm_wea_s  = 1'b0;
assign xpm_dina_s = {XPM_DATA_WIDTH{1'b0}};

////////////////////////////////////////////////////////////////////////////////
// The init_seq_complete flag is asserted when the data read from XPM memory is
// 32'hffff_ffff. This is reserved data, written in to XPM memory to indicate
// end of initialization sequence
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    init_seq_complete_r <= 1'b0;
  end else if (xpm_douta == 32'hffff_ffff && addr_data_toggle_r == 1'b1) begin
    init_seq_complete_r <= 1'b1;
  end
end

assign init_seq_complete_s = init_seq_complete_r && ~(gen_poll_r);

////////////////////////////////////////////////////////////////////////////////
// Togging a flag to register address and data for APB transactions
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    addr_data_toggle_r <= 1'b0;
  end else if (xpm_ena_r == 1'b1) begin
    addr_data_toggle_r <= ~addr_data_toggle_r;
  end else begin
    addr_data_toggle_r <= 1'b0;
  end
end

always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    addr_data_toggle_r1 <= 1'b0;
    addr_data_toggle_r2 <= 1'b0;
  end else begin
    addr_data_toggle_r1 <= addr_data_toggle_r;
    addr_data_toggle_r2 <= addr_data_toggle_r1;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Registering Address and Data for APB transactions
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    apb_wr_rd_r <= 1'b0;
    apb_poll_r  <= 1'b0;
    apb_addr_r  <= {APB_ADDR_WIDTH{1'b0}};
    apb_data_r  <= {APB_DATA_WIDTH{1'b0}};
  end else if (apb_poll_r == 1'b1 && apb_poll_complete == 1'b1) begin
    apb_poll_r  <= apb_poll_pend_r;
    apb_wr_rd_r <= apb_wr_rd_pend_r;
    apb_addr_r  <= apb_addr_pend_r;
    apb_data_r  <= apb_data_pend_r;
  end else if (addr_data_toggle_r == 1'b1 && xpm_addra_r != {XPM_ADDR_WIDTH{1'b0}}  && apb_poll_pend_r == 1'b0) begin
    apb_addr_r  <= xpm_douta[APB_ADDR_WIDTH-1:0];
    apb_wr_rd_r <= xpm_douta[24];
    apb_poll_r  <= xpm_douta[25];
  end else if (addr_data_toggle_r == 1'b0 && xpm_addra_r != {XPM_ADDR_WIDTH{1'b0}}) begin
    apb_data_r <= xpm_douta[APB_DATA_WIDTH-1:0];
  end
end

////////////////////////////////////////////////////////////////////////////////
// Storing the second read polling request if the first polling request is not yet
// serverd
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    apb_poll_pend_r  <= 1'b0;
    apb_wr_rd_pend_r <= 1'b0;
    apb_addr_pend_r  <= {APB_ADDR_WIDTH{1'b0}};
    apb_data_pend_r  <= {APB_DATA_WIDTH{1'b0}};
  end else if (apb_poll_complete == 1'b1) begin
    apb_poll_pend_r  <= 1'b0;
    apb_wr_rd_pend_r <= 1'b0;
    apb_addr_pend_r  <= {APB_ADDR_WIDTH{1'b0}};
    apb_data_pend_r  <= {APB_DATA_WIDTH{1'b0}};
  end else if (apb_poll_r == 1'b1 && addr_data_toggle_r == 1'b1 && xpm_addra_r != {XPM_ADDR_WIDTH{1'b0}} && apb_poll_pend_r == 1'b0) begin
    apb_addr_pend_r  <= xpm_douta[APB_ADDR_WIDTH-1:0];
    apb_wr_rd_pend_r <= xpm_douta[24];
    apb_poll_pend_r  <= xpm_douta[25];
  end else if (apb_poll_r == 1'b1 && addr_data_toggle_r == 1'b0 && xpm_addra_r != {XPM_ADDR_WIDTH{1'b0}}) begin
    apb_data_pend_r <= xpm_douta[APB_DATA_WIDTH-1:0];
  end
end

////////////////////////////////////////////////////////////////////////////////
// Generating a flag to indicate first data received from XPM. This flag will
// remain asserted till init_seq_complete is set to '1'.
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    data_rcvd_r <= 1'b0;
  end else if (init_seq_complete_r == 1'b1) begin
    data_rcvd_r <= 1'b0;
  end else if (xpm_ena_r == 1'b1 && xpm_addra_r != {XPM_ADDR_WIDTH{1'b0}}) begin
    data_rcvd_r <= 1'b1;
  end
end

always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    stall_rd_r <= 1'b0;
  end else if (apb_poll_r == 1'b1 && gen_poll_r == 1'b0) begin
    stall_rd_r <= 1'b1;
  end else if (gen_apb_tran_r == 1'b1) begin
    stall_rd_r <= 1'b0;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Generating Transaction Enable, WR/RD command and Polling enable signals to
// indicate new APB transaction
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    gen_apb_tran_r  <= 1'b0;
    gen_apb_wr_rd_r <= 1'b0;
    gen_poll_r      <= 1'b0;
  end else begin
    gen_apb_tran_r  <= data_rcvd_r && (addr_data_toggle_r) && ~(apb_back_press && apb_poll_pend_r);
    gen_apb_wr_rd_r <= apb_wr_rd_r;
    gen_poll_r      <= data_rcvd_r && (addr_data_toggle_r) && apb_poll_r;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Generating Address and write Data for new APB transactions
////////////////////////////////////////////////////////////////////////////////
always @ (posedge apb_clk or negedge apb_rst_n) begin
  if (~apb_rst_n) begin
    gen_apb_addr_r  <= {APB_ADDR_WIDTH{1'b0}};
    gen_apb_data_r  <= {APB_DATA_WIDTH{1'b0}};
  end else if (~init_seq_complete_r) begin
    gen_apb_addr_r  <= apb_addr_r;
    gen_apb_data_r  <= apb_data_r;
  end else begin
    gen_apb_addr_r  <= gen_apb_addr_r;
    gen_apb_data_r  <= gen_apb_data_r;
  end
end

////////////////////////////////////////////////////////////////////////////////
// Assigning output signals
////////////////////////////////////////////////////////////////////////////////
assign xpm_ena           = xpm_ena_r;
assign xpm_wea           = xpm_wea_s;
assign xpm_addra         = xpm_addra_r;
assign xpm_dina          = xpm_dina_s;
assign init_seq_complete = init_seq_complete_s;
assign gen_apb_tran      = addr_data_toggle_r2;
assign gen_apb_wr_rd     = apb_wr_rd_r;
assign gen_poll          = apb_poll_r;
assign gen_apb_addr      = apb_addr_r;
assign gen_apb_data      = apb_data_r;

endmodule


