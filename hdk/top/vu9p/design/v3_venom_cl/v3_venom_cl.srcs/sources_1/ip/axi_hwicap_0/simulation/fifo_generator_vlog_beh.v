/*
 *******************************************************************************
 *
 * FIFO Generator - Verilog Behavioral Model
 *
 *******************************************************************************
 *
 * (c) Copyright 1995 - 2009 Xilinx, Inc. All rights reserved.
 *
 * This file contains confidential and proprietary information
 * of Xilinx, Inc. and is protected under U.S. and
 * international copyright and other intellectual property
 * laws.
 *
 * DISCLAIMER
 * This disclaimer is not a license and does not grant any
 * rights to the materials distributed herewith. Except as
 * otherwise provided in a valid license issued to you by
 * Xilinx, and to the maximum extent permitted by applicable
 * law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
 * WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
 * AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
 * BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
 * INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
 * (2) Xilinx shall not be liable (whether in contract or tort,
 * including negligence, or under any other theory of
 * liability) for any loss or damage of any kind or nature
 * related to, arising under or in connection with these
 * materials, including for any direct, or any indirect,
 * special, incidental, or consequential loss or damage
 * (including loss of data, profits, goodwill, or any type of
 * loss or damage suffered as a result of any action brought
 * by a third party) even if such damage or loss was
 * reasonably foreseeable or Xilinx had been advised of the
 * possibility of the same.
 *
 * CRITICAL APPLICATIONS
 * Xilinx products are not designed or intended to be fail-
 * safe, or for use in any application requiring fail-safe
 * performance, such as life-support or safety devices or
 * systems, Class III medical devices, nuclear facilities,
 * applications related to the deployment of airbags, or any
 * other applications that could lead to death, personal
 * injury, or severe property or environmental damage
 * (individually and collectively, "Critical
 * Applications"). Customer assumes the sole risk and
 * liability of any use of Xilinx products in Critical
 * Applications, subject only to applicable laws and
 * regulations governing limitations on product liability.
 *
 * THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
 * PART OF THIS FILE AT ALL TIMES.
 *
 *******************************************************************************
 *******************************************************************************
 *
 * Filename: fifo_generator_vlog_beh.v
 *
 * Author     : Xilinx
 *
 *******************************************************************************
 * Structure:
 * 
 * fifo_generator_vlog_beh.v
 *    |
 *    +-fifo_generator_v13_1_2_bhv_ver_as
 *    |
 *    +-fifo_generator_v13_1_2_bhv_ver_ss
 *    |
 *    +-fifo_generator_v13_1_2_bhv_ver_preload0
 * 
 *******************************************************************************
 * Description:
 *
 * The Verilog behavioral model for the FIFO Generator.
 *
 *   The behavioral model has three parts:
 *      - The behavioral model for independent clocks FIFOs (_as)
 *      - The behavioral model for common clock FIFOs (_ss)
 *      - The "preload logic" block which implements First-word Fall-through
 * 
 *******************************************************************************
 * Description:
 *  The verilog behavioral model for the FIFO generator core.
 *
 *******************************************************************************
 */

`timescale 1ps/1ps
`ifndef TCQ
 `define TCQ 100
`endif


/*******************************************************************************
 * Declaration of top-level module
 ******************************************************************************/
module fifo_generator_vlog_beh
  #(
    //-----------------------------------------------------------------------
    // Generic Declarations
    //-----------------------------------------------------------------------
    parameter C_COMMON_CLOCK                 = 0,
    parameter C_COUNT_TYPE                   = 0,
    parameter C_DATA_COUNT_WIDTH             = 2,
    parameter C_DEFAULT_VALUE                = "",
    parameter C_DIN_WIDTH                    = 8,
    parameter C_DOUT_RST_VAL                 = "",
    parameter C_DOUT_WIDTH                   = 8,
    parameter C_ENABLE_RLOCS                 = 0,
    parameter C_FAMILY                       = "",
    parameter C_FULL_FLAGS_RST_VAL           = 1,
    parameter C_HAS_ALMOST_EMPTY             = 0,
    parameter C_HAS_ALMOST_FULL              = 0,
    parameter C_HAS_BACKUP                   = 0,
    parameter C_HAS_DATA_COUNT               = 0,
    parameter C_HAS_INT_CLK                  = 0,
    parameter C_HAS_MEMINIT_FILE             = 0,
    parameter C_HAS_OVERFLOW                 = 0,
    parameter C_HAS_RD_DATA_COUNT            = 0,
    parameter C_HAS_RD_RST                   = 0,
    parameter C_HAS_RST                      = 1,
    parameter C_HAS_SRST                     = 0,
    parameter C_HAS_UNDERFLOW                = 0,
    parameter C_HAS_VALID                    = 0,
    parameter C_HAS_WR_ACK                   = 0,
    parameter C_HAS_WR_DATA_COUNT            = 0,
    parameter C_HAS_WR_RST                   = 0,
    parameter C_IMPLEMENTATION_TYPE          = 0,
    parameter C_INIT_WR_PNTR_VAL             = 0,
    parameter C_MEMORY_TYPE                  = 1,
    parameter C_MIF_FILE_NAME                = "",
    parameter C_OPTIMIZATION_MODE            = 0,
    parameter C_OVERFLOW_LOW                 = 0,
    parameter C_EN_SAFETY_CKT                = 0,
    parameter C_PRELOAD_LATENCY              = 1,
    parameter C_PRELOAD_REGS                 = 0,
    parameter C_PRIM_FIFO_TYPE               = "4kx4",
    parameter C_PROG_EMPTY_THRESH_ASSERT_VAL = 0,
    parameter C_PROG_EMPTY_THRESH_NEGATE_VAL = 0,
    parameter C_PROG_EMPTY_TYPE              = 0,
    parameter C_PROG_FULL_THRESH_ASSERT_VAL  = 0,
    parameter C_PROG_FULL_THRESH_NEGATE_VAL  = 0,
    parameter C_PROG_FULL_TYPE               = 0,
    parameter C_RD_DATA_COUNT_WIDTH          = 2,
    parameter C_RD_DEPTH                     = 256,
    parameter C_RD_FREQ                      = 1,
    parameter C_RD_PNTR_WIDTH                = 8,
    parameter C_UNDERFLOW_LOW                = 0,
    parameter C_USE_DOUT_RST                 = 0,
    parameter C_USE_ECC                      = 0,
    parameter C_USE_EMBEDDED_REG             = 0,
    parameter C_USE_PIPELINE_REG             = 0,
    parameter C_POWER_SAVING_MODE            = 0,
    parameter C_USE_FIFO16_FLAGS             = 0,
    parameter C_USE_FWFT_DATA_COUNT          = 0,
    parameter C_VALID_LOW                    = 0,
    parameter C_WR_ACK_LOW                   = 0,
    parameter C_WR_DATA_COUNT_WIDTH          = 2,
    parameter C_WR_DEPTH                     = 256,
    parameter C_WR_FREQ                      = 1,
    parameter C_WR_PNTR_WIDTH                = 8,
    parameter C_WR_RESPONSE_LATENCY          = 1,
    parameter C_MSGON_VAL                    = 1,
    parameter C_ENABLE_RST_SYNC              = 1,
    parameter C_ERROR_INJECTION_TYPE         = 0,
    parameter C_SYNCHRONIZER_STAGE           = 2,

    // AXI Interface related parameters start here
    parameter C_INTERFACE_TYPE               = 0, // 0: Native Interface, 1: AXI4 Stream, 2: AXI4/AXI3
    parameter C_AXI_TYPE                     = 0, // 1: AXI4, 2: AXI4 Lite, 3: AXI3
    parameter C_HAS_AXI_WR_CHANNEL           = 0,
    parameter C_HAS_AXI_RD_CHANNEL           = 0,
    parameter C_HAS_SLAVE_CE                 = 0,
    parameter C_HAS_MASTER_CE                = 0,
    parameter C_ADD_NGC_CONSTRAINT           = 0,
    parameter C_USE_COMMON_UNDERFLOW         = 0,
    parameter C_USE_COMMON_OVERFLOW          = 0,
    parameter C_USE_DEFAULT_SETTINGS         = 0,

    // AXI Full/Lite
    parameter C_AXI_ID_WIDTH                 = 0,
    parameter C_AXI_ADDR_WIDTH               = 0,
    parameter C_AXI_DATA_WIDTH               = 0,
    parameter C_AXI_LEN_WIDTH                = 8,
    parameter C_AXI_LOCK_WIDTH               = 2,
    parameter C_HAS_AXI_ID                   = 0,
    parameter C_HAS_AXI_AWUSER               = 0,
    parameter C_HAS_AXI_WUSER                = 0,
    parameter C_HAS_AXI_BUSER                = 0,
    parameter C_HAS_AXI_ARUSER               = 0,
    parameter C_HAS_AXI_RUSER                = 0,
    parameter C_AXI_ARUSER_WIDTH             = 0,
    parameter C_AXI_AWUSER_WIDTH             = 0,
    parameter C_AXI_WUSER_WIDTH              = 0,
    parameter C_AXI_BUSER_WIDTH              = 0,
    parameter C_AXI_RUSER_WIDTH              = 0,

    // AXI Streaming
    parameter C_HAS_AXIS_TDATA               = 0,
    parameter C_HAS_AXIS_TID                 = 0,
    parameter C_HAS_AXIS_TDEST               = 0,
    parameter C_HAS_AXIS_TUSER               = 0,
    parameter C_HAS_AXIS_TREADY              = 0,
    parameter C_HAS_AXIS_TLAST               = 0,
    parameter C_HAS_AXIS_TSTRB               = 0,
    parameter C_HAS_AXIS_TKEEP               = 0,
    parameter C_AXIS_TDATA_WIDTH             = 1,
    parameter C_AXIS_TID_WIDTH               = 1,
    parameter C_AXIS_TDEST_WIDTH             = 1,
    parameter C_AXIS_TUSER_WIDTH             = 1,
    parameter C_AXIS_TSTRB_WIDTH             = 1,
    parameter C_AXIS_TKEEP_WIDTH             = 1,

    // AXI Channel Type
    // WACH --> Write Address Channel
    // WDCH --> Write Data Channel
    // WRCH --> Write Response Channel
    // RACH --> Read Address Channel
    // RDCH --> Read Data Channel
    // AXIS --> AXI Streaming
    parameter C_WACH_TYPE                    = 0, // 0 = FIFO, 1 = Register Slice, 2 = Pass Through Logic
    parameter C_WDCH_TYPE                    = 0, // 0 = FIFO, 1 = Register Slice, 2 = Pass Through Logie
    parameter C_WRCH_TYPE                    = 0, // 0 = FIFO, 1 = Register Slice, 2 = Pass Through Logie
    parameter C_RACH_TYPE                    = 0, // 0 = FIFO, 1 = Register Slice, 2 = Pass Through Logie
    parameter C_RDCH_TYPE                    = 0, // 0 = FIFO, 1 = Register Slice, 2 = Pass Through Logie
    parameter C_AXIS_TYPE                    = 0, // 0 = FIFO, 1 = Register Slice, 2 = Pass Through Logie

    // AXI Implementation Type
    // 1 = Common Clock Block RAM FIFO
    // 2 = Common Clock Distributed RAM FIFO
    // 11 = Independent Clock Block RAM FIFO
    // 12 = Independent Clock Distributed RAM FIFO
    parameter C_IMPLEMENTATION_TYPE_WACH     = 0,
    parameter C_IMPLEMENTATION_TYPE_WDCH     = 0,
    parameter C_IMPLEMENTATION_TYPE_WRCH     = 0,
    parameter C_IMPLEMENTATION_TYPE_RACH     = 0,
    parameter C_IMPLEMENTATION_TYPE_RDCH     = 0,
    parameter C_IMPLEMENTATION_TYPE_AXIS     = 0,

    // AXI FIFO Type
    // 0 = Data FIFO
    // 1 = Packet FIFO
    // 2 = Low Latency Sync FIFO
    // 3 = Low Latency Async FIFO
    parameter C_APPLICATION_TYPE_WACH        = 0,
    parameter C_APPLICATION_TYPE_WDCH        = 0,
    parameter C_APPLICATION_TYPE_WRCH        = 0,
    parameter C_APPLICATION_TYPE_RACH        = 0,
    parameter C_APPLICATION_TYPE_RDCH        = 0,
    parameter C_APPLICATION_TYPE_AXIS        = 0,

    // AXI Built-in FIFO Primitive Type
    // 512x36, 1kx18, 2kx9, 4kx4, etc
    parameter C_PRIM_FIFO_TYPE_WACH          = "512x36",
    parameter C_PRIM_FIFO_TYPE_WDCH          = "512x36",
    parameter C_PRIM_FIFO_TYPE_WRCH          = "512x36",
    parameter C_PRIM_FIFO_TYPE_RACH          = "512x36",
    parameter C_PRIM_FIFO_TYPE_RDCH          = "512x36",
    parameter C_PRIM_FIFO_TYPE_AXIS          = "512x36",

    // Enable ECC
    // 0 = ECC disabled
    // 1 = ECC enabled
    parameter C_USE_ECC_WACH                 = 0,
    parameter C_USE_ECC_WDCH                 = 0,
    parameter C_USE_ECC_WRCH                 = 0,
    parameter C_USE_ECC_RACH                 = 0,
    parameter C_USE_ECC_RDCH                 = 0,
    parameter C_USE_ECC_AXIS                 = 0,

    // ECC Error Injection Type
    // 0 = No Error Injection
    // 1 = Single Bit Error Injection
    // 2 = Double Bit Error Injection
    // 3 = Single Bit and Double Bit Error Injection
    parameter C_ERROR_INJECTION_TYPE_WACH    = 0,
    parameter C_ERROR_INJECTION_TYPE_WDCH    = 0,
    parameter C_ERROR_INJECTION_TYPE_WRCH    = 0,
    parameter C_ERROR_INJECTION_TYPE_RACH    = 0,
    parameter C_ERROR_INJECTION_TYPE_RDCH    = 0,
    parameter C_ERROR_INJECTION_TYPE_AXIS    = 0,

    // Input Data Width
    // Accumulation of all AXI input signal's width
    parameter C_DIN_WIDTH_WACH               = 1,
    parameter C_DIN_WIDTH_WDCH               = 1,
    parameter C_DIN_WIDTH_WRCH               = 1,
    parameter C_DIN_WIDTH_RACH               = 1,
    parameter C_DIN_WIDTH_RDCH               = 1,
    parameter C_DIN_WIDTH_AXIS               = 1,

    parameter C_WR_DEPTH_WACH                = 16,
    parameter C_WR_DEPTH_WDCH                = 16,
    parameter C_WR_DEPTH_WRCH                = 16,
    parameter C_WR_DEPTH_RACH                = 16,
    parameter C_WR_DEPTH_RDCH                = 16,
    parameter C_WR_DEPTH_AXIS                = 16,

    parameter C_WR_PNTR_WIDTH_WACH           = 4,
    parameter C_WR_PNTR_WIDTH_WDCH           = 4,
    parameter C_WR_PNTR_WIDTH_WRCH           = 4,
    parameter C_WR_PNTR_WIDTH_RACH           = 4,
    parameter C_WR_PNTR_WIDTH_RDCH           = 4,
    parameter C_WR_PNTR_WIDTH_AXIS           = 4,

    parameter C_HAS_DATA_COUNTS_WACH         = 0,
    parameter C_HAS_DATA_COUNTS_WDCH         = 0,
    parameter C_HAS_DATA_COUNTS_WRCH         = 0,
    parameter C_HAS_DATA_COUNTS_RACH         = 0,
    parameter C_HAS_DATA_COUNTS_RDCH         = 0,
    parameter C_HAS_DATA_COUNTS_AXIS         = 0,

    parameter C_HAS_PROG_FLAGS_WACH          = 0,
    parameter C_HAS_PROG_FLAGS_WDCH          = 0,
    parameter C_HAS_PROG_FLAGS_WRCH          = 0,
    parameter C_HAS_PROG_FLAGS_RACH          = 0,
    parameter C_HAS_PROG_FLAGS_RDCH          = 0,
    parameter C_HAS_PROG_FLAGS_AXIS          = 0,

    parameter C_PROG_FULL_TYPE_WACH          = 0,
    parameter C_PROG_FULL_TYPE_WDCH          = 0,
    parameter C_PROG_FULL_TYPE_WRCH          = 0,
    parameter C_PROG_FULL_TYPE_RACH          = 0,
    parameter C_PROG_FULL_TYPE_RDCH          = 0,
    parameter C_PROG_FULL_TYPE_AXIS          = 0,

    parameter C_PROG_FULL_THRESH_ASSERT_VAL_WACH      = 0,
    parameter C_PROG_FULL_THRESH_ASSERT_VAL_WDCH      = 0,
    parameter C_PROG_FULL_THRESH_ASSERT_VAL_WRCH      = 0,
    parameter C_PROG_FULL_THRESH_ASSERT_VAL_RACH      = 0,
    parameter C_PROG_FULL_THRESH_ASSERT_VAL_RDCH      = 0,
    parameter C_PROG_FULL_THRESH_ASSERT_VAL_AXIS      = 0,

    parameter C_PROG_EMPTY_TYPE_WACH         = 0,
    parameter C_PROG_EMPTY_TYPE_WDCH         = 0,
    parameter C_PROG_EMPTY_TYPE_WRCH         = 0,
    parameter C_PROG_EMPTY_TYPE_RACH         = 0,
    parameter C_PROG_EMPTY_TYPE_RDCH         = 0,
    parameter C_PROG_EMPTY_TYPE_AXIS         = 0,

    parameter C_PROG_EMPTY_THRESH_ASSERT_VAL_WACH     = 0,
    parameter C_PROG_EMPTY_THRESH_ASSERT_VAL_WDCH     = 0,
    parameter C_PROG_EMPTY_THRESH_ASSERT_VAL_WRCH     = 0,
    parameter C_PROG_EMPTY_THRESH_ASSERT_VAL_RACH     = 0,
    parameter C_PROG_EMPTY_THRESH_ASSERT_VAL_RDCH     = 0,
    parameter C_PROG_EMPTY_THRESH_ASSERT_VAL_AXIS     = 0,

    parameter C_REG_SLICE_MODE_WACH          = 0,
    parameter C_REG_SLICE_MODE_WDCH          = 0,
    parameter C_REG_SLICE_MODE_WRCH          = 0,
    parameter C_REG_SLICE_MODE_RACH          = 0,
    parameter C_REG_SLICE_MODE_RDCH          = 0,
    parameter C_REG_SLICE_MODE_AXIS          = 0

    )

   (
    //------------------------------------------------------------------------------
    // Input and Output Declarations
    //------------------------------------------------------------------------------

    // Conventional FIFO Interface Signals
    input                               backup,
    input                               backup_marker,
    input                               clk,
    input                               rst,
    input                               srst,
    input                               wr_clk,
    input                               wr_rst,
    input                               rd_clk,
    input                               rd_rst,
    input [C_DIN_WIDTH-1:0]             din,
    input                               wr_en,
    input                               rd_en,
    // Optional inputs
    input [C_RD_PNTR_WIDTH-1:0]         prog_empty_thresh,
    input [C_RD_PNTR_WIDTH-1:0]         prog_empty_thresh_assert,
    input [C_RD_PNTR_WIDTH-1:0]         prog_empty_thresh_negate,
    input [C_WR_PNTR_WIDTH-1:0]         prog_full_thresh,
    input [C_WR_PNTR_WIDTH-1:0]         prog_full_thresh_assert,
    input [C_WR_PNTR_WIDTH-1:0]         prog_full_thresh_negate,
    input                               int_clk,
    input                               injectdbiterr,
    input                               injectsbiterr,
    input                               sleep,

    output [C_DOUT_WIDTH-1:0]           dout,
    output                              full,
    output                              almost_full,
    output                              wr_ack,
    output                              overflow,
    output                              empty,
    output                              almost_empty,
    output                              valid,
    output                              underflow,
    output [C_DATA_COUNT_WIDTH-1:0]     data_count,
    output [C_RD_DATA_COUNT_WIDTH-1:0]  rd_data_count,
    output [C_WR_DATA_COUNT_WIDTH-1:0]  wr_data_count,
    output                              prog_full,
    output                              prog_empty,
    output                              sbiterr,
    output                              dbiterr,
    output                              wr_rst_busy,
    output                              rd_rst_busy,


    // AXI Global Signal
    input                               m_aclk,
    input                               s_aclk,
    input                               s_aresetn,
    input                               s_aclk_en,
    input                               m_aclk_en,
    
    // AXI Full/Lite Slave Write Channel (write side)
    input [C_AXI_ID_WIDTH-1:0]          s_axi_awid,
    input [C_AXI_ADDR_WIDTH-1:0]        s_axi_awaddr,
    input [C_AXI_LEN_WIDTH-1:0]         s_axi_awlen,
    input [3-1:0]                       s_axi_awsize,
    input [2-1:0]                       s_axi_awburst,
    input [C_AXI_LOCK_WIDTH-1:0]        s_axi_awlock,
    input [4-1:0]                       s_axi_awcache,
    input [3-1:0]                       s_axi_awprot,
    input [4-1:0]                       s_axi_awqos,
    input [4-1:0]                       s_axi_awregion,
    input [C_AXI_AWUSER_WIDTH-1:0]      s_axi_awuser,
    input                               s_axi_awvalid,
    output                              s_axi_awready,
    input [C_AXI_ID_WIDTH-1:0]          s_axi_wid,
    input [C_AXI_DATA_WIDTH-1:0]        s_axi_wdata,
    input [C_AXI_DATA_WIDTH/8-1:0]      s_axi_wstrb,
    input                               s_axi_wlast,
    input [C_AXI_WUSER_WIDTH-1:0]       s_axi_wuser,
    input                               s_axi_wvalid,
    output                              s_axi_wready,
    output [C_AXI_ID_WIDTH-1:0]         s_axi_bid,
    output [2-1:0]                      s_axi_bresp,
    output [C_AXI_BUSER_WIDTH-1:0]      s_axi_buser,
    output                              s_axi_bvalid,
    input                               s_axi_bready,
    
    // AXI Full/Lite Master Write Channel (read side)
    output [C_AXI_ID_WIDTH-1:0]         m_axi_awid,
    output [C_AXI_ADDR_WIDTH-1:0]       m_axi_awaddr,
    output [C_AXI_LEN_WIDTH-1:0]        m_axi_awlen,
    output [3-1:0]                      m_axi_awsize,
    output [2-1:0]                      m_axi_awburst,
    output [C_AXI_LOCK_WIDTH-1:0]       m_axi_awlock,
    output [4-1:0]                      m_axi_awcache,
    output [3-1:0]                      m_axi_awprot,
    output [4-1:0]                      m_axi_awqos,
    output [4-1:0]                      m_axi_awregion,
    output [C_AXI_AWUSER_WIDTH-1:0]     m_axi_awuser,
    output                              m_axi_awvalid,
    input                               m_axi_awready,
    output [C_AXI_ID_WIDTH-1:0]         m_axi_wid,
    output [C_AXI_DATA_WIDTH-1:0]       m_axi_wdata,
    output [C_AXI_DATA_WIDTH/8-1:0]     m_axi_wstrb,
    output                              m_axi_wlast,
    output [C_AXI_WUSER_WIDTH-1:0]      m_axi_wuser,
    output                              m_axi_wvalid,
    input                               m_axi_wready,
    input [C_AXI_ID_WIDTH-1:0]          m_axi_bid,
    input [2-1:0]                       m_axi_bresp,
    input [C_AXI_BUSER_WIDTH-1:0]       m_axi_buser,
    input                               m_axi_bvalid,
    output                              m_axi_bready,
    
    
    // AXI Full/Lite Slave Read Channel (write side)
    input [C_AXI_ID_WIDTH-1:0]          s_axi_arid,
    input [C_AXI_ADDR_WIDTH-1:0]        s_axi_araddr, 
    input [C_AXI_LEN_WIDTH-1:0]         s_axi_arlen,
    input [3-1:0]                       s_axi_arsize,
    input [2-1:0]                       s_axi_arburst,
    input [C_AXI_LOCK_WIDTH-1:0]        s_axi_arlock,
    input [4-1:0]                       s_axi_arcache,
    input [3-1:0]                       s_axi_arprot,
    input [4-1:0]                       s_axi_arqos,
    input [4-1:0]                       s_axi_arregion,
    input [C_AXI_ARUSER_WIDTH-1:0]      s_axi_aruser,
    input                               s_axi_arvalid,
    output                              s_axi_arready,
    output [C_AXI_ID_WIDTH-1:0]         s_axi_rid,       
    output [C_AXI_DATA_WIDTH-1:0]       s_axi_rdata, 
    output [2-1:0]                      s_axi_rresp,
    output                              s_axi_rlast,
    output [C_AXI_RUSER_WIDTH-1:0]      s_axi_ruser,
    output                              s_axi_rvalid,
    input                               s_axi_rready,
    
    
    
    // AXI Full/Lite Master Read Channel (read side)
    output [C_AXI_ID_WIDTH-1:0]         m_axi_arid,        
    output [C_AXI_ADDR_WIDTH-1:0]       m_axi_araddr,  
    output [C_AXI_LEN_WIDTH-1:0]        m_axi_arlen,
    output [3-1:0]                      m_axi_arsize,
    output [2-1:0]                      m_axi_arburst,
    output [C_AXI_LOCK_WIDTH-1:0]       m_axi_arlock,
    output [4-1:0]                      m_axi_arcache,
    output [3-1:0]                      m_axi_arprot,
    output [4-1:0]                      m_axi_arqos,
    output [4-1:0]                      m_axi_arregion,
    output [C_AXI_ARUSER_WIDTH-1:0]     m_axi_aruser,
    output                              m_axi_arvalid,
    input                               m_axi_arready,
    input [C_AXI_ID_WIDTH-1:0]          m_axi_rid,        
    input [C_AXI_DATA_WIDTH-1:0]        m_axi_rdata,  
    input [2-1:0]                       m_axi_rresp,
    input                               m_axi_rlast,
    input [C_AXI_RUSER_WIDTH-1:0]       m_axi_ruser,
    input                               m_axi_rvalid,
    output                              m_axi_rready,
    
    
    // AXI Streaming Slave Signals (Write side)
    input                               s_axis_tvalid,
    output                              s_axis_tready,
    input [C_AXIS_TDATA_WIDTH-1:0]      s_axis_tdata,
    input [C_AXIS_TSTRB_WIDTH-1:0]      s_axis_tstrb,
    input [C_AXIS_TKEEP_WIDTH-1:0]      s_axis_tkeep,
    input                               s_axis_tlast,
    input [C_AXIS_TID_WIDTH-1:0]        s_axis_tid,
    input [C_AXIS_TDEST_WIDTH-1:0]      s_axis_tdest,
    input [C_AXIS_TUSER_WIDTH-1:0]      s_axis_tuser,
    
    // AXI Streaming Master Signals (Read side)
    output                              m_axis_tvalid,
    input                               m_axis_tready,
    output [C_AXIS_TDATA_WIDTH-1:0]     m_axis_tdata,
    output [C_AXIS_TSTRB_WIDTH-1:0]     m_axis_tstrb,
    output [C_AXIS_TKEEP_WIDTH-1:0]     m_axis_tkeep,
    output                              m_axis_tlast,
    output [C_AXIS_TID_WIDTH-1:0]       m_axis_tid,
    output [C_AXIS_TDEST_WIDTH-1:0]     m_axis_tdest,
    output [C_AXIS_TUSER_WIDTH-1:0]     m_axis_tuser,
    
           
    
    
    // AXI Full/Lite Write Address Channel signals
    input                               axi_aw_injectsbiterr,
    input                               axi_aw_injectdbiterr,
    input  [C_WR_PNTR_WIDTH_WACH-1:0]   axi_aw_prog_full_thresh,
    input  [C_WR_PNTR_WIDTH_WACH-1:0]   axi_aw_prog_empty_thresh,
    output [C_WR_PNTR_WIDTH_WACH:0]     axi_aw_data_count,
    output [C_WR_PNTR_WIDTH_WACH:0]     axi_aw_wr_data_count,
    output [C_WR_PNTR_WIDTH_WACH:0]     axi_aw_rd_data_count,
    output                              axi_aw_sbiterr,
    output                              axi_aw_dbiterr,
    output                              axi_aw_overflow,
    output                              axi_aw_underflow,
    output                              axi_aw_prog_full,
    output                              axi_aw_prog_empty,
    
    
    // AXI Full/Lite Write Data Channel signals
    input                               axi_w_injectsbiterr,
    input                               axi_w_injectdbiterr,
    input  [C_WR_PNTR_WIDTH_WDCH-1:0]   axi_w_prog_full_thresh,
    input  [C_WR_PNTR_WIDTH_WDCH-1:0]   axi_w_prog_empty_thresh,
    output [C_WR_PNTR_WIDTH_WDCH:0]     axi_w_data_count,
    output [C_WR_PNTR_WIDTH_WDCH:0]     axi_w_wr_data_count,
    output [C_WR_PNTR_WIDTH_WDCH:0]     axi_w_rd_data_count,
    output                              axi_w_sbiterr,
    output                              axi_w_dbiterr,
    output                              axi_w_overflow,
    output                              axi_w_underflow,
    output                              axi_w_prog_full,
    output                              axi_w_prog_empty,
    
    
    // AXI Full/Lite Write Response Channel signals
    input                               axi_b_injectsbiterr,
    input                               axi_b_injectdbiterr,
    input  [C_WR_PNTR_WIDTH_WRCH-1:0]   axi_b_prog_full_thresh,
    input  [C_WR_PNTR_WIDTH_WRCH-1:0]   axi_b_prog_empty_thresh,
    output [C_WR_PNTR_WIDTH_WRCH:0]     axi_b_data_count,
    output [C_WR_PNTR_WIDTH_WRCH:0]     axi_b_wr_data_count,
    output [C_WR_PNTR_WIDTH_WRCH:0]     axi_b_rd_data_count,
    output                              axi_b_sbiterr,
    output                              axi_b_dbiterr,
    output                              axi_b_overflow,
    output                              axi_b_underflow,
    output                              axi_b_prog_full,
    output                              axi_b_prog_empty,
    
    
    
    // AXI Full/Lite Read Address Channel signals
    input                               axi_ar_injectsbiterr,
    input                               axi_ar_injectdbiterr,
    input  [C_WR_PNTR_WIDTH_RACH-1:0]   axi_ar_prog_full_thresh,
    input  [C_WR_PNTR_WIDTH_RACH-1:0]   axi_ar_prog_empty_thresh,
    output [C_WR_PNTR_WIDTH_RACH:0]     axi_ar_data_count,
    output [C_WR_PNTR_WIDTH_RACH:0]     axi_ar_wr_data_count,
    output [C_WR_PNTR_WIDTH_RACH:0]     axi_ar_rd_data_count,
    output                              axi_ar_sbiterr,
    output                              axi_ar_dbiterr,
    output                              axi_ar_overflow,
    output                              axi_ar_underflow,
    output                              axi_ar_prog_full,
    output                              axi_ar_prog_empty,

    
    // AXI Full/Lite Read Data Channel Signals
    input                               axi_r_injectsbiterr,
    input                               axi_r_injectdbiterr,
    input  [C_WR_PNTR_WIDTH_RDCH-1:0]   axi_r_prog_full_thresh,
    input  [C_WR_PNTR_WIDTH_RDCH-1:0]   axi_r_prog_empty_thresh,
    output [C_WR_PNTR_WIDTH_RDCH:0]     axi_r_data_count,
    output [C_WR_PNTR_WIDTH_RDCH:0]     axi_r_wr_data_count,
    output [C_WR_PNTR_WIDTH_RDCH:0]     axi_r_rd_data_count,
    output                              axi_r_sbiterr,
    output                              axi_r_dbiterr,
    output                              axi_r_overflow,
    output                              axi_r_underflow,
    output                              axi_r_prog_full,
    output                              axi_r_prog_empty,

    
    // AXI Streaming FIFO Related Signals
    input                               axis_injectsbiterr,
    input                               axis_injectdbiterr,
    input  [C_WR_PNTR_WIDTH_AXIS-1:0]   axis_prog_full_thresh,
    input  [C_WR_PNTR_WIDTH_AXIS-1:0]   axis_prog_empty_thresh,
    output [C_WR_PNTR_WIDTH_AXIS:0]     axis_data_count,
    output [C_WR_PNTR_WIDTH_AXIS:0]     axis_wr_data_count,
    output [C_WR_PNTR_WIDTH_AXIS:0]     axis_rd_data_count,
    output                              axis_sbiterr,
    output                              axis_dbiterr,
    output                              axis_overflow,
    output                              axis_underflow,
    output                              axis_prog_full,
    output                              axis_prog_empty

    );

    wire                              BACKUP;
    wire                              BACKUP_MARKER;
    wire                              CLK;
    wire                              RST;
    wire                              SRST;
    wire                              WR_CLK;
    wire                              WR_RST;
    wire                              RD_CLK;
    wire                              RD_RST;
    wire [C_DIN_WIDTH-1:0]            DIN;
    wire                              WR_EN;
    wire                              RD_EN;
    wire [C_RD_PNTR_WIDTH-1:0]        PROG_EMPTY_THRESH;
    wire [C_RD_PNTR_WIDTH-1:0]        PROG_EMPTY_THRESH_ASSERT;
    wire [C_RD_PNTR_WIDTH-1:0]        PROG_EMPTY_THRESH_NEGATE;
    wire [C_WR_PNTR_WIDTH-1:0]        PROG_FULL_THRESH;
    wire [C_WR_PNTR_WIDTH-1:0]        PROG_FULL_THRESH_ASSERT;
    wire [C_WR_PNTR_WIDTH-1:0]        PROG_FULL_THRESH_NEGATE;
    wire                              INT_CLK;
    wire                              INJECTDBITERR;
    wire                              INJECTSBITERR;
    wire                              SLEEP;
    wire [C_DOUT_WIDTH-1:0]           DOUT;
    wire                              FULL;
    wire                              ALMOST_FULL;
    wire                              WR_ACK;
    wire                              OVERFLOW;
    wire                              EMPTY;
    wire                              ALMOST_EMPTY;
    wire                              VALID;
    wire                              UNDERFLOW;
    wire [C_DATA_COUNT_WIDTH-1:0]     DATA_COUNT;
    wire [C_RD_DATA_COUNT_WIDTH-1:0]  RD_DATA_COUNT;
    wire [C_WR_DATA_COUNT_WIDTH-1:0]  WR_DATA_COUNT;
    wire                              PROG_FULL;
    wire                              PROG_EMPTY;
    wire                              SBITERR;
    wire                              DBITERR;
    wire                              WR_RST_BUSY;
    wire                              RD_RST_BUSY;
    wire                              M_ACLK;
    wire                              S_ACLK;
    wire                              S_ARESETN;
    wire                              S_ACLK_EN;
    wire                              M_ACLK_EN;
    wire [C_AXI_ID_WIDTH-1:0]         S_AXI_AWID;
    wire [C_AXI_ADDR_WIDTH-1:0]       S_AXI_AWADDR;
    wire [C_AXI_LEN_WIDTH-1:0]        S_AXI_AWLEN;
    wire [3-1:0]                      S_AXI_AWSIZE;
    wire [2-1:0]                      S_AXI_AWBURST;
    wire [C_AXI_LOCK_WIDTH-1:0]       S_AXI_AWLOCK;
    wire [4-1:0]                      S_AXI_AWCACHE;
    wire [3-1:0]                      S_AXI_AWPROT;
    wire [4-1:0]                      S_AXI_AWQOS;
    wire [4-1:0]                      S_AXI_AWREGION;
    wire [C_AXI_AWUSER_WIDTH-1:0]     S_AXI_AWUSER;
    wire                              S_AXI_AWVALID;
    wire                              S_AXI_AWREADY;
    wire [C_AXI_ID_WIDTH-1:0]         S_AXI_WID;
    wire [C_AXI_DATA_WIDTH-1:0]       S_AXI_WDATA;
    wire [C_AXI_DATA_WIDTH/8-1:0]     S_AXI_WSTRB;
    wire                              S_AXI_WLAST;
    wire [C_AXI_WUSER_WIDTH-1:0]      S_AXI_WUSER;
    wire                              S_AXI_WVALID;
    wire                              S_AXI_WREADY;
    wire [C_AXI_ID_WIDTH-1:0]         S_AXI_BID;
    wire [2-1:0]                      S_AXI_BRESP;
    wire [C_AXI_BUSER_WIDTH-1:0]      S_AXI_BUSER;
    wire                              S_AXI_BVALID;
    wire                              S_AXI_BREADY;
    wire [C_AXI_ID_WIDTH-1:0]         M_AXI_AWID;
    wire [C_AXI_ADDR_WIDTH-1:0]       M_AXI_AWADDR;
    wire [C_AXI_LEN_WIDTH-1:0]        M_AXI_AWLEN;
    wire [3-1:0]                      M_AXI_AWSIZE;
    wire [2-1:0]                      M_AXI_AWBURST;
    wire [C_AXI_LOCK_WIDTH-1:0]       M_AXI_AWLOCK;
    wire [4-1:0]                      M_AXI_AWCACHE;
    wire [3-1:0]                      M_AXI_AWPROT;
    wire [4-1:0]                      M_AXI_AWQOS;
    wire [4-1:0]                      M_AXI_AWREGION;
    wire [C_AXI_AWUSER_WIDTH-1:0]     M_AXI_AWUSER;
    wire                              M_AXI_AWVALID;
    wire                              M_AXI_AWREADY;
    wire [C_AXI_ID_WIDTH-1:0]         M_AXI_WID;
    wire [C_AXI_DATA_WIDTH-1:0]       M_AXI_WDATA;
    wire [C_AXI_DATA_WIDTH/8-1:0]     M_AXI_WSTRB;
    wire                              M_AXI_WLAST;
    wire [C_AXI_WUSER_WIDTH-1:0]      M_AXI_WUSER;
    wire                              M_AXI_WVALID;
    wire                              M_AXI_WREADY;
    wire [C_AXI_ID_WIDTH-1:0]         M_AXI_BID;
    wire [2-1:0]                      M_AXI_BRESP;
    wire [C_AXI_BUSER_WIDTH-1:0]      M_AXI_BUSER;
    wire                              M_AXI_BVALID;
    wire                              M_AXI_BREADY;
    wire [C_AXI_ID_WIDTH-1:0]         S_AXI_ARID;
    wire [C_AXI_ADDR_WIDTH-1:0]       S_AXI_ARADDR; 
    wire [C_AXI_LEN_WIDTH-1:0]        S_AXI_ARLEN;
    wire [3-1:0]                      S_AXI_ARSIZE;
    wire [2-1:0]                      S_AXI_ARBURST;
    wire [C_AXI_LOCK_WIDTH-1:0]       S_AXI_ARLOCK;
    wire [4-1:0]                      S_AXI_ARCACHE;
    wire [3-1:0]                      S_AXI_ARPROT;
    wire [4-1:0]                      S_AXI_ARQOS;
    wire [4-1:0]                      S_AXI_ARREGION;
    wire [C_AXI_ARUSER_WIDTH-1:0]     S_AXI_ARUSER;
    wire                              S_AXI_ARVALID;
    wire                              S_AXI_ARREADY;
    wire [C_AXI_ID_WIDTH-1:0]         S_AXI_RID;       
    wire [C_AXI_DATA_WIDTH-1:0]       S_AXI_RDATA; 
    wire [2-1:0]                      S_AXI_RRESP;
    wire                              S_AXI_RLAST;
    wire [C_AXI_RUSER_WIDTH-1:0]      S_AXI_RUSER;
    wire                              S_AXI_RVALID;
    wire                              S_AXI_RREADY;
    wire [C_AXI_ID_WIDTH-1:0]         M_AXI_ARID;        
    wire [C_AXI_ADDR_WIDTH-1:0]       M_AXI_ARADDR;  
    wire [C_AXI_LEN_WIDTH-1:0]        M_AXI_ARLEN;
    wire [3-1:0]                      M_AXI_ARSIZE;
    wire [2-1:0]                      M_AXI_ARBURST;
    wire [C_AXI_LOCK_WIDTH-1:0]       M_AXI_ARLOCK;
    wire [4-1:0]                      M_AXI_ARCACHE;
    wire [3-1:0]                      M_AXI_ARPROT;
    wire [4-1:0]                      M_AXI_ARQOS;
    wire [4-1:0]                      M_AXI_ARREGION;
    wire [C_AXI_ARUSER_WIDTH-1:0]     M_AXI_ARUSER;
    wire                              M_AXI_ARVALID;
    wire                              M_AXI_ARREADY;
    wire [C_AXI_ID_WIDTH-1:0]         M_AXI_RID;        
    wire [C_AXI_DATA_WIDTH-1:0]       M_AXI_RDATA;  
    wire [2-1:0]                      M_AXI_RRESP;
    wire                              M_AXI_RLAST;
    wire [C_AXI_RUSER_WIDTH-1:0]      M_AXI_RUSER;
    wire                              M_AXI_RVALID;
    wire                              M_AXI_RREADY;
    wire                              S_AXIS_TVALID;
    wire                              S_AXIS_TREADY;
    wire [C_AXIS_TDATA_WIDTH-1:0]     S_AXIS_TDATA;
    wire [C_AXIS_TSTRB_WIDTH-1:0]     S_AXIS_TSTRB;
    wire [C_AXIS_TKEEP_WIDTH-1:0]     S_AXIS_TKEEP;
    wire                              S_AXIS_TLAST;
    wire [C_AXIS_TID_WIDTH-1:0]       S_AXIS_TID;
    wire [C_AXIS_TDEST_WIDTH-1:0]     S_AXIS_TDEST;
    wire [C_AXIS_TUSER_WIDTH-1:0]     S_AXIS_TUSER;
    wire                              M_AXIS_TVALID;
    wire                              M_AXIS_TREADY;
    wire [C_AXIS_TDATA_WIDTH-1:0]     M_AXIS_TDATA;
    wire [C_AXIS_TSTRB_WIDTH-1:0]     M_AXIS_TSTRB;
    wire [C_AXIS_TKEEP_WIDTH-1:0]     M_AXIS_TKEEP;
    wire                              M_AXIS_TLAST;
    wire [C_AXIS_TID_WIDTH-1:0]       M_AXIS_TID;
    wire [C_AXIS_TDEST_WIDTH-1:0]     M_AXIS_TDEST;
    wire [C_AXIS_TUSER_WIDTH-1:0]     M_AXIS_TUSER;
    wire                              AXI_AW_INJECTSBITERR;
    wire                              AXI_AW_INJECTDBITERR;
    wire [C_WR_PNTR_WIDTH_WACH-1:0]   AXI_AW_PROG_FULL_THRESH;
    wire [C_WR_PNTR_WIDTH_WACH-1:0]   AXI_AW_PROG_EMPTY_THRESH;
    wire [C_WR_PNTR_WIDTH_WACH:0]     AXI_AW_DATA_COUNT;
    wire [C_WR_PNTR_WIDTH_WACH:0]     AXI_AW_WR_DATA_COUNT;
    wire [C_WR_PNTR_WIDTH_WACH:0]     AXI_AW_RD_DATA_COUNT;
    wire                              AXI_AW_SBITERR;
    wire                              AXI_AW_DBITERR;
    wire                              AXI_AW_OVERFLOW;
    wire                              AXI_AW_UNDERFLOW;
    wire                              AXI_AW_PROG_FULL;
    wire                              AXI_AW_PROG_EMPTY;
    wire                              AXI_W_INJECTSBITERR;
    wire                              AXI_W_INJECTDBITERR;
    wire [C_WR_PNTR_WIDTH_WDCH-1:0]   AXI_W_PROG_FULL_THRESH;
    wire [C_WR_PNTR_WIDTH_WDCH-1:0]   AXI_W_PROG_EMPTY_THRESH;
    wire [C_WR_PNTR_WIDTH_WDCH:0]     AXI_W_DATA_COUNT;
    wire [C_WR_PNTR_WIDTH_WDCH:0]     AXI_W_WR_DATA_COUNT;
    wire [C_WR_PNTR_WIDTH_WDCH:0]     AXI_W_RD_DATA_COUNT;
    wire                              AXI_W_SBITERR;
    wire                              AXI_W_DBITERR;
    wire                              AXI_W_OVERFLOW;
    wire                              AXI_W_UNDERFLOW;
    wire                              AXI_W_PROG_FULL;
    wire                              AXI_W_PROG_EMPTY;
    wire                              AXI_B_INJECTSBITERR;
    wire                              AXI_B_INJECTDBITERR;
    wire [C_WR_PNTR_WIDTH_WRCH-1:0]   AXI_B_PROG_FULL_THRESH;
    wire [C_WR_PNTR_WIDTH_WRCH-1:0]   AXI_B_PROG_EMPTY_THRESH;
    wire [C_WR_PNTR_WIDTH_WRCH:0]     AXI_B_DATA_COUNT;
    wire [C_WR_PNTR_WIDTH_WRCH:0]     AXI_B_WR_DATA_COUNT;
    wire [C_WR_PNTR_WIDTH_WRCH:0]     AXI_B_RD_DATA_COUNT;
    wire                              AXI_B_SBITERR;
    wire                              AXI_B_DBITERR;
    wire                              AXI_B_OVERFLOW;
    wire                              AXI_B_UNDERFLOW;
    wire                              AXI_B_PROG_FULL;
    wire                              AXI_B_PROG_EMPTY;
    wire                              AXI_AR_INJECTSBITERR;
    wire                              AXI_AR_INJECTDBITERR;
    wire [C_WR_PNTR_WIDTH_RACH-1:0]   AXI_AR_PROG_FULL_THRESH;
    wire [C_WR_PNTR_WIDTH_RACH-1:0]   AXI_AR_PROG_EMPTY_THRESH;
    wire [C_WR_PNTR_WIDTH_RACH:0]     AXI_AR_DATA_COUNT;
    wire [C_WR_PNTR_WIDTH_RACH:0]     AXI_AR_WR_DATA_COUNT;
    wire [C_WR_PNTR_WIDTH_RACH:0]     AXI_AR_RD_DATA_COUNT;
    wire                              AXI_AR_SBITERR;
    wire                              AXI_AR_DBITERR;
    wire                              AXI_AR_OVERFLOW;
    wire                              AXI_AR_UNDERFLOW;
    wire                              AXI_AR_PROG_FULL;
    wire                              AXI_AR_PROG_EMPTY;
    wire                              AXI_R_INJECTSBITERR;
    wire                              AXI_R_INJECTDBITERR;
    wire [C_WR_PNTR_WIDTH_RDCH-1:0]   AXI_R_PROG_FULL_THRESH;
    wire [C_WR_PNTR_WIDTH_RDCH-1:0]   AXI_R_PROG_EMPTY_THRESH;
    wire [C_WR_PNTR_WIDTH_RDCH:0]     AXI_R_DATA_COUNT;
    wire [C_WR_PNTR_WIDTH_RDCH:0]     AXI_R_WR_DATA_COUNT;
    wire [C_WR_PNTR_WIDTH_RDCH:0]     AXI_R_RD_DATA_COUNT;
    wire                              AXI_R_SBITERR;
    wire                              AXI_R_DBITERR;
    wire                              AXI_R_OVERFLOW;
    wire                              AXI_R_UNDERFLOW;
    wire                              AXI_R_PROG_FULL;
    wire                              AXI_R_PROG_EMPTY;
    wire                              AXIS_INJECTSBITERR;
    wire                              AXIS_INJECTDBITERR;
    wire [C_WR_PNTR_WIDTH_AXIS-1:0]   AXIS_PROG_FULL_THRESH;
    wire [C_WR_PNTR_WIDTH_AXIS-1:0]   AXIS_PROG_EMPTY_THRESH;
    wire [C_WR_PNTR_WIDTH_AXIS:0]     AXIS_DATA_COUNT;
    wire [C_WR_PNTR_WIDTH_AXIS:0]     AXIS_WR_DATA_COUNT;
    wire [C_WR_PNTR_WIDTH_AXIS:0]     AXIS_RD_DATA_COUNT;
    wire                              AXIS_SBITERR;
    wire                              AXIS_DBITERR;
    wire                              AXIS_OVERFLOW;
    wire                              AXIS_UNDERFLOW;
    wire                              AXIS_PROG_FULL;
    wire                              AXIS_PROG_EMPTY;
    wire [C_WR_DATA_COUNT_WIDTH-1:0]  wr_data_count_in;
    wire                              wr_rst_int;
    wire                              rd_rst_int;
    wire                              wr_rst_busy_o;
    wire                              wr_rst_busy_ntve;
    wire                              wr_rst_busy_axis;
    wire                              wr_rst_busy_wach;
    wire                              wr_rst_busy_wdch;
    wire                              wr_rst_busy_wrch;
    wire                              wr_rst_busy_rach;
    wire                              wr_rst_busy_rdch;



  function integer find_log2;
    input integer int_val;
    integer i,j;
    begin
      i = 1;
      j = 0;
      for (i = 1; i < int_val; i = i*2) begin
        j = j + 1;
      end
      find_log2 = j;
    end
  endfunction




    // Conventional FIFO Interface Signals
    assign BACKUP                 = backup;
    assign BACKUP_MARKER          = backup_marker;
    assign CLK                    = clk;
    assign RST                    = rst;
    assign SRST                   = srst;
    assign WR_CLK                 = wr_clk;
    assign WR_RST                 = wr_rst;
    assign RD_CLK                 = rd_clk;
    assign RD_RST                 = rd_rst;
    assign WR_EN                  = wr_en;
    assign RD_EN                  = rd_en;
    assign INT_CLK                = int_clk;
    assign INJECTDBITERR          = injectdbiterr;
    assign INJECTSBITERR          = injectsbiterr;
    assign SLEEP                  = sleep;
    assign full                   = FULL;
    assign almost_full            = ALMOST_FULL;
    assign wr_ack                 = WR_ACK;
    assign overflow               = OVERFLOW;
    assign empty                  = EMPTY;
    assign almost_empty           = ALMOST_EMPTY;
    assign valid                  = VALID;
    assign underflow              = UNDERFLOW;
    assign prog_full              = PROG_FULL;
    assign prog_empty             = PROG_EMPTY;
    assign sbiterr                = SBITERR;
    assign dbiterr                = DBITERR;
//    assign wr_rst_busy            = WR_RST_BUSY | wr_rst_busy_o;
    assign wr_rst_busy            = wr_rst_busy_o;
    assign rd_rst_busy            = RD_RST_BUSY;
    assign M_ACLK                 = m_aclk;
    assign S_ACLK                 = s_aclk;
    assign S_ARESETN              = s_aresetn;
    assign S_ACLK_EN              = s_aclk_en;
    assign M_ACLK_EN              = m_aclk_en;
    assign S_AXI_AWVALID          = s_axi_awvalid;
    assign s_axi_awready          = S_AXI_AWREADY;
    assign S_AXI_WLAST            = s_axi_wlast;
    assign S_AXI_WVALID           = s_axi_wvalid;
    assign s_axi_wready           = S_AXI_WREADY;
    assign s_axi_bvalid           = S_AXI_BVALID;
    assign S_AXI_BREADY           = s_axi_bready;
    assign m_axi_awvalid          = M_AXI_AWVALID;
    assign M_AXI_AWREADY          = m_axi_awready;
    assign m_axi_wlast            = M_AXI_WLAST;
    assign m_axi_wvalid           = M_AXI_WVALID;
    assign M_AXI_WREADY           = m_axi_wready;
    assign M_AXI_BVALID           = m_axi_bvalid;
    assign m_axi_bready           = M_AXI_BREADY;
    assign S_AXI_ARVALID          = s_axi_arvalid;
    assign s_axi_arready          = S_AXI_ARREADY;
    assign s_axi_rlast            = S_AXI_RLAST;
    assign s_axi_rvalid           = S_AXI_RVALID;
    assign S_AXI_RREADY           = s_axi_rready;
    assign m_axi_arvalid          = M_AXI_ARVALID;
    assign M_AXI_ARREADY          = m_axi_arready;
    assign M_AXI_RLAST            = m_axi_rlast;
    assign M_AXI_RVALID           = m_axi_rvalid;
    assign m_axi_rready           = M_AXI_RREADY;
    assign S_AXIS_TVALID          = s_axis_tvalid;
    assign s_axis_tready          = S_AXIS_TREADY;
    assign S_AXIS_TLAST           = s_axis_tlast;
    assign m_axis_tvalid          = M_AXIS_TVALID;
    assign M_AXIS_TREADY          = m_axis_tready;
    assign m_axis_tlast           = M_AXIS_TLAST;
    assign AXI_AW_INJECTSBITERR   = axi_aw_injectsbiterr;
    assign AXI_AW_INJECTDBITERR   = axi_aw_injectdbiterr;
    assign axi_aw_sbiterr         = AXI_AW_SBITERR;
    assign axi_aw_dbiterr         = AXI_AW_DBITERR;
    assign axi_aw_overflow        = AXI_AW_OVERFLOW;
    assign axi_aw_underflow       = AXI_AW_UNDERFLOW;
    assign axi_aw_prog_full       = AXI_AW_PROG_FULL;
    assign axi_aw_prog_empty      = AXI_AW_PROG_EMPTY;
    assign AXI_W_INJECTSBITERR    = axi_w_injectsbiterr;
    assign AXI_W_INJECTDBITERR    = axi_w_injectdbiterr;
    assign axi_w_sbiterr          = AXI_W_SBITERR;
    assign axi_w_dbiterr          = AXI_W_DBITERR;
    assign axi_w_overflow         = AXI_W_OVERFLOW;
    assign axi_w_underflow        = AXI_W_UNDERFLOW;
    assign axi_w_prog_full        = AXI_W_PROG_FULL;
    assign axi_w_prog_empty       = AXI_W_PROG_EMPTY;
    assign AXI_B_INJECTSBITERR    = axi_b_injectsbiterr;
    assign AXI_B_INJECTDBITERR    = axi_b_injectdbiterr;
    assign axi_b_sbiterr          = AXI_B_SBITERR;
    assign axi_b_dbiterr          = AXI_B_DBITERR;
    assign axi_b_overflow         = AXI_B_OVERFLOW;
    assign axi_b_underflow        = AXI_B_UNDERFLOW;
    assign axi_b_prog_full        = AXI_B_PROG_FULL;
    assign axi_b_prog_empty       = AXI_B_PROG_EMPTY;
    assign AXI_AR_INJECTSBITERR   = axi_ar_injectsbiterr;
    assign AXI_AR_INJECTDBITERR   = axi_ar_injectdbiterr;
    assign axi_ar_sbiterr         = AXI_AR_SBITERR;
    assign axi_ar_dbiterr         = AXI_AR_DBITERR;
    assign axi_ar_overflow        = AXI_AR_OVERFLOW;
    assign axi_ar_underflow       = AXI_AR_UNDERFLOW;
    assign axi_ar_prog_full       = AXI_AR_PROG_FULL;
    assign axi_ar_prog_empty      = AXI_AR_PROG_EMPTY;
    assign AXI_R_INJECTSBITERR    = axi_r_injectsbiterr;
    assign AXI_R_INJECTDBITERR    = axi_r_injectdbiterr;
    assign axi_r_sbiterr          = AXI_R_SBITERR;
    assign axi_r_dbiterr          = AXI_R_DBITERR;
    assign axi_r_overflow         = AXI_R_OVERFLOW;
    assign axi_r_underflow        = AXI_R_UNDERFLOW;
    assign axi_r_prog_full        = AXI_R_PROG_FULL;
    assign axi_r_prog_empty       = AXI_R_PROG_EMPTY;
    assign AXIS_INJECTSBITERR     = axis_injectsbiterr;
    assign AXIS_INJECTDBITERR     = axis_injectdbiterr;
    assign axis_sbiterr           = AXIS_SBITERR;
    assign axis_dbiterr           = AXIS_DBITERR;
    assign axis_overflow          = AXIS_OVERFLOW;
    assign axis_underflow         = AXIS_UNDERFLOW;
    assign axis_prog_full         = AXIS_PROG_FULL;
    assign axis_prog_empty        = AXIS_PROG_EMPTY;


    assign DIN                       = din;
    assign PROG_EMPTY_THRESH         = prog_empty_thresh;
    assign PROG_EMPTY_THRESH_ASSERT  = prog_empty_thresh_assert;
    assign PROG_EMPTY_THRESH_NEGATE  = prog_empty_thresh_negate;
    assign PROG_FULL_THRESH          = prog_full_thresh;
    assign PROG_FULL_THRESH_ASSERT   = prog_full_thresh_assert;
    assign PROG_FULL_THRESH_NEGATE   = prog_full_thresh_negate;
    assign dout                      = DOUT;
    assign data_count                = DATA_COUNT;
    assign rd_data_count             = RD_DATA_COUNT;
    assign wr_data_count             = WR_DATA_COUNT;
    assign S_AXI_AWID                = s_axi_awid;
    assign S_AXI_AWADDR              = s_axi_awaddr;
    assign S_AXI_AWLEN               = s_axi_awlen;
    assign S_AXI_AWSIZE              = s_axi_awsize;
    assign S_AXI_AWBURST             = s_axi_awburst;
    assign S_AXI_AWLOCK              = s_axi_awlock;
    assign S_AXI_AWCACHE             = s_axi_awcache;
    assign S_AXI_AWPROT              = s_axi_awprot;
    assign S_AXI_AWQOS               = s_axi_awqos;
    assign S_AXI_AWREGION            = s_axi_awregion;
    assign S_AXI_AWUSER              = s_axi_awuser;
    assign S_AXI_WID                 = s_axi_wid;
    assign S_AXI_WDATA               = s_axi_wdata;
    assign S_AXI_WSTRB               = s_axi_wstrb;
    assign S_AXI_WUSER               = s_axi_wuser;
    assign s_axi_bid                 = S_AXI_BID;
    assign s_axi_bresp               = S_AXI_BRESP;
    assign s_axi_buser               = S_AXI_BUSER;
    assign m_axi_awid                = M_AXI_AWID;
    assign m_axi_awaddr              = M_AXI_AWADDR;
    assign m_axi_awlen               = M_AXI_AWLEN;
    assign m_axi_awsize              = M_AXI_AWSIZE;
    assign m_axi_awburst             = M_AXI_AWBURST;
    assign m_axi_awlock              = M_AXI_AWLOCK;
    assign m_axi_awcache             = M_AXI_AWCACHE;
    assign m_axi_awprot              = M_AXI_AWPROT;
    assign m_axi_awqos               = M_AXI_AWQOS;
    assign m_axi_awregion            = M_AXI_AWREGION;
    assign m_axi_awuser              = M_AXI_AWUSER;
    assign m_axi_wid                 = M_AXI_WID;
    assign m_axi_wdata               = M_AXI_WDATA;
    assign m_axi_wstrb               = M_AXI_WSTRB;
    assign m_axi_wuser               = M_AXI_WUSER;
    assign M_AXI_BID                 = m_axi_bid;
    assign M_AXI_BRESP               = m_axi_bresp;
    assign M_AXI_BUSER               = m_axi_buser;
    assign S_AXI_ARID                = s_axi_arid;
    assign S_AXI_ARADDR              = s_axi_araddr; 
    assign S_AXI_ARLEN               = s_axi_arlen;
    assign S_AXI_ARSIZE              = s_axi_arsize;
    assign S_AXI_ARBURST             = s_axi_arburst;
    assign S_AXI_ARLOCK              = s_axi_arlock;
    assign S_AXI_ARCACHE             = s_axi_arcache;
    assign S_AXI_ARPROT              = s_axi_arprot;
    assign S_AXI_ARQOS               = s_axi_arqos;
    assign S_AXI_ARREGION            = s_axi_arregion;
    assign S_AXI_ARUSER              = s_axi_aruser;
    assign s_axi_rid                 = S_AXI_RID;
    assign s_axi_rdata               = S_AXI_RDATA;
    assign s_axi_rresp               = S_AXI_RRESP;
    assign s_axi_ruser               = S_AXI_RUSER;
    assign m_axi_arid                = M_AXI_ARID;        
    assign m_axi_araddr              = M_AXI_ARADDR;  
    assign m_axi_arlen               = M_AXI_ARLEN;
    assign m_axi_arsize              = M_AXI_ARSIZE;
    assign m_axi_arburst             = M_AXI_ARBURST;
    assign m_axi_arlock              = M_AXI_ARLOCK;
    assign m_axi_arcache             = M_AXI_ARCACHE;
    assign m_axi_arprot              = M_AXI_ARPROT;
    assign m_axi_arqos               = M_AXI_ARQOS;
    assign m_axi_arregion            = M_AXI_ARREGION;
    assign m_axi_aruser              = M_AXI_ARUSER;
    assign M_AXI_RID                 = m_axi_rid;        
    assign M_AXI_RDATA               = m_axi_rdata;  
    assign M_AXI_RRESP               = m_axi_rresp;
    assign M_AXI_RUSER               = m_axi_ruser;
    assign S_AXIS_TDATA              = s_axis_tdata;
    assign S_AXIS_TSTRB              = s_axis_tstrb;
    assign S_AXIS_TKEEP              = s_axis_tkeep;
    assign S_AXIS_TID                = s_axis_tid;
    assign S_AXIS_TDEST              = s_axis_tdest;
    assign S_AXIS_TUSER              = s_axis_tuser;
    assign m_axis_tdata              = M_AXIS_TDATA;
    assign m_axis_tstrb              = M_AXIS_TSTRB;
    assign m_axis_tkeep              = M_AXIS_TKEEP;
    assign m_axis_tid                = M_AXIS_TID;
    assign m_axis_tdest              = M_AXIS_TDEST;
    assign m_axis_tuser              = M_AXIS_TUSER;
    assign AXI_AW_PROG_FULL_THRESH   = axi_aw_prog_full_thresh;
    assign AXI_AW_PROG_EMPTY_THRESH  = axi_aw_prog_empty_thresh;
    assign axi_aw_data_count         = AXI_AW_DATA_COUNT;
    assign axi_aw_wr_data_count      = AXI_AW_WR_DATA_COUNT;
    assign axi_aw_rd_data_count      = AXI_AW_RD_DATA_COUNT;
    assign AXI_W_PROG_FULL_THRESH    = axi_w_prog_full_thresh;
    assign AXI_W_PROG_EMPTY_THRESH   = axi_w_prog_empty_thresh;
    assign axi_w_data_count          = AXI_W_DATA_COUNT;
    assign axi_w_wr_data_count       = AXI_W_WR_DATA_COUNT;
    assign axi_w_rd_data_count       = AXI_W_RD_DATA_COUNT;
    assign AXI_B_PROG_FULL_THRESH    = axi_b_prog_full_thresh;
    assign AXI_B_PROG_EMPTY_THRESH   = axi_b_prog_empty_thresh;
    assign axi_b_data_count          = AXI_B_DATA_COUNT;
    assign axi_b_wr_data_count       = AXI_B_WR_DATA_COUNT;
    assign axi_b_rd_data_count       = AXI_B_RD_DATA_COUNT;
    assign AXI_AR_PROG_FULL_THRESH   = axi_ar_prog_full_thresh;
    assign AXI_AR_PROG_EMPTY_THRESH  = axi_ar_prog_empty_thresh;
    assign axi_ar_data_count         = AXI_AR_DATA_COUNT;
    assign axi_ar_wr_data_count      = AXI_AR_WR_DATA_COUNT;
    assign axi_ar_rd_data_count      = AXI_AR_RD_DATA_COUNT;
    assign AXI_R_PROG_FULL_THRESH    = axi_r_prog_full_thresh;
    assign AXI_R_PROG_EMPTY_THRESH   = axi_r_prog_empty_thresh;
    assign axi_r_data_count          = AXI_R_DATA_COUNT;
    assign axi_r_wr_data_count       = AXI_R_WR_DATA_COUNT;
    assign axi_r_rd_data_count       = AXI_R_RD_DATA_COUNT;
    assign AXIS_PROG_FULL_THRESH     = axis_prog_full_thresh;
    assign AXIS_PROG_EMPTY_THRESH    = axis_prog_empty_thresh;
    assign axis_data_count           = AXIS_DATA_COUNT;
    assign axis_wr_data_count        = AXIS_WR_DATA_COUNT;
    assign axis_rd_data_count        = AXIS_RD_DATA_COUNT;


  generate if (C_INTERFACE_TYPE == 0) begin : conv_fifo

    fifo_generator_v13_1_2_CONV_VER
      #(
        .C_COMMON_CLOCK 		(C_COMMON_CLOCK),
        .C_INTERFACE_TYPE 		(C_INTERFACE_TYPE),
        .C_COUNT_TYPE			(C_COUNT_TYPE),
        .C_DATA_COUNT_WIDTH		(C_DATA_COUNT_WIDTH),
        .C_DEFAULT_VALUE		(C_DEFAULT_VALUE),
        .C_DIN_WIDTH			(C_DIN_WIDTH),
        .C_DOUT_RST_VAL			(C_USE_DOUT_RST == 1 ? C_DOUT_RST_VAL : 0),
        .C_DOUT_WIDTH			(C_DOUT_WIDTH),
        .C_ENABLE_RLOCS			(C_ENABLE_RLOCS),
        .C_FAMILY			(C_FAMILY),
        .C_FULL_FLAGS_RST_VAL           (C_FULL_FLAGS_RST_VAL),
        .C_HAS_ALMOST_EMPTY		(C_HAS_ALMOST_EMPTY),
        .C_HAS_ALMOST_FULL		(C_HAS_ALMOST_FULL),
        .C_HAS_BACKUP			(C_HAS_BACKUP),
        .C_HAS_DATA_COUNT		(C_HAS_DATA_COUNT),
        .C_HAS_INT_CLK                  (C_HAS_INT_CLK),
        .C_HAS_MEMINIT_FILE		(C_HAS_MEMINIT_FILE),
        .C_HAS_OVERFLOW			(C_HAS_OVERFLOW),
        .C_HAS_RD_DATA_COUNT		(C_HAS_RD_DATA_COUNT),
        .C_HAS_RD_RST			(C_HAS_RD_RST),
        .C_HAS_RST			(C_HAS_RST),
        .C_HAS_SRST			(C_HAS_SRST),
        .C_HAS_UNDERFLOW		(C_HAS_UNDERFLOW),
        .C_HAS_VALID			(C_HAS_VALID),
        .C_HAS_WR_ACK			(C_HAS_WR_ACK),
        .C_HAS_WR_DATA_COUNT		(C_HAS_WR_DATA_COUNT),
        .C_HAS_WR_RST			(C_HAS_WR_RST),
        .C_IMPLEMENTATION_TYPE		(C_IMPLEMENTATION_TYPE),
        .C_INIT_WR_PNTR_VAL		(C_INIT_WR_PNTR_VAL),
        .C_MEMORY_TYPE			(C_MEMORY_TYPE),
        .C_MIF_FILE_NAME		(C_MIF_FILE_NAME),
        .C_OPTIMIZATION_MODE		(C_OPTIMIZATION_MODE),
        .C_OVERFLOW_LOW			(C_OVERFLOW_LOW),
        .C_PRELOAD_LATENCY		(C_PRELOAD_LATENCY),
        .C_PRELOAD_REGS			(C_PRELOAD_REGS),
        .C_PRIM_FIFO_TYPE		(C_PRIM_FIFO_TYPE),
        .C_PROG_EMPTY_THRESH_ASSERT_VAL	(C_PROG_EMPTY_THRESH_ASSERT_VAL),
        .C_PROG_EMPTY_THRESH_NEGATE_VAL	(C_PROG_EMPTY_THRESH_NEGATE_VAL),
        .C_PROG_EMPTY_TYPE		(C_PROG_EMPTY_TYPE),
        .C_PROG_FULL_THRESH_ASSERT_VAL	(C_PROG_FULL_THRESH_ASSERT_VAL),
        .C_PROG_FULL_THRESH_NEGATE_VAL	(C_PROG_FULL_THRESH_NEGATE_VAL),
        .C_PROG_FULL_TYPE		(C_PROG_FULL_TYPE),
        .C_RD_DATA_COUNT_WIDTH		(C_RD_DATA_COUNT_WIDTH),
        .C_RD_DEPTH			(C_RD_DEPTH),
        .C_RD_FREQ			(C_RD_FREQ),
        .C_RD_PNTR_WIDTH		(C_RD_PNTR_WIDTH),
        .C_UNDERFLOW_LOW		(C_UNDERFLOW_LOW),
        .C_USE_DOUT_RST                 (C_USE_DOUT_RST),
        .C_USE_ECC                      (C_USE_ECC),
        .C_USE_EMBEDDED_REG		(C_USE_EMBEDDED_REG),
        .C_EN_SAFETY_CKT		(C_EN_SAFETY_CKT),
        .C_USE_FIFO16_FLAGS		(C_USE_FIFO16_FLAGS),
        .C_USE_FWFT_DATA_COUNT		(C_USE_FWFT_DATA_COUNT),
        .C_VALID_LOW			(C_VALID_LOW),
        .C_WR_ACK_LOW			(C_WR_ACK_LOW),
        .C_WR_DATA_COUNT_WIDTH		(C_WR_DATA_COUNT_WIDTH),
        .C_WR_DEPTH			(C_WR_DEPTH),
        .C_WR_FREQ			(C_WR_FREQ),
        .C_WR_PNTR_WIDTH		(C_WR_PNTR_WIDTH),
        .C_WR_RESPONSE_LATENCY		(C_WR_RESPONSE_LATENCY),
        .C_MSGON_VAL                    (C_MSGON_VAL),
        .C_ENABLE_RST_SYNC              (C_ENABLE_RST_SYNC),
        .C_ERROR_INJECTION_TYPE         (C_ERROR_INJECTION_TYPE),
        .C_AXI_TYPE                     (C_AXI_TYPE),
        .C_SYNCHRONIZER_STAGE           (C_SYNCHRONIZER_STAGE)
      )
    fifo_generator_v13_1_2_conv_dut
      (
        .BACKUP                   (BACKUP),
        .BACKUP_MARKER            (BACKUP_MARKER),
        .CLK                      (CLK),
        .RST                      (RST),
        .SRST                     (SRST),
        .WR_CLK                   (WR_CLK),
        .WR_RST                   (WR_RST),
        .RD_CLK                   (RD_CLK),
        .RD_RST                   (RD_RST),
        .DIN                      (DIN),
        .WR_EN                    (WR_EN),
        .RD_EN                    (RD_EN),
        .PROG_EMPTY_THRESH        (PROG_EMPTY_THRESH),
        .PROG_EMPTY_THRESH_ASSERT (PROG_EMPTY_THRESH_ASSERT),
        .PROG_EMPTY_THRESH_NEGATE (PROG_EMPTY_THRESH_NEGATE),
        .PROG_FULL_THRESH         (PROG_FULL_THRESH),
        .PROG_FULL_THRESH_ASSERT  (PROG_FULL_THRESH_ASSERT),
        .PROG_FULL_THRESH_NEGATE  (PROG_FULL_THRESH_NEGATE),
        .INT_CLK                  (INT_CLK),
        .INJECTDBITERR            (INJECTDBITERR), 
        .INJECTSBITERR            (INJECTSBITERR),
  
        .DOUT                     (DOUT),
        .FULL                     (FULL),
        .ALMOST_FULL              (ALMOST_FULL),
        .WR_ACK                   (WR_ACK),
        .OVERFLOW                 (OVERFLOW),
        .EMPTY                    (EMPTY),
        .ALMOST_EMPTY             (ALMOST_EMPTY),
        .VALID                    (VALID),
        .UNDERFLOW                (UNDERFLOW),
        .DATA_COUNT               (DATA_COUNT),
        .RD_DATA_COUNT            (RD_DATA_COUNT),
        .WR_DATA_COUNT            (wr_data_count_in),
        .PROG_FULL                (PROG_FULL),
        .PROG_EMPTY               (PROG_EMPTY),
        .SBITERR                  (SBITERR),
        .DBITERR                  (DBITERR),
        .wr_rst_busy_o            (wr_rst_busy_o),
        .wr_rst_busy              (wr_rst_busy_i),
        .rd_rst_busy              (rd_rst_busy),
        .wr_rst_i_out             (wr_rst_int),
        .rd_rst_i_out             (rd_rst_int)
       );
  end endgenerate



  localparam IS_8SERIES         = (C_FAMILY == "virtexu" || C_FAMILY == "kintexu" || C_FAMILY == "artixu" || C_FAMILY == "virtexuplus" || C_FAMILY == "zynquplus" || C_FAMILY == "kintexuplus") ? 1 : 0;
  localparam C_AXI_SIZE_WIDTH   = 3;
  localparam C_AXI_BURST_WIDTH  = 2;
  localparam C_AXI_CACHE_WIDTH  = 4;
  localparam C_AXI_PROT_WIDTH   = 3;
  localparam C_AXI_QOS_WIDTH    = 4;
  localparam C_AXI_REGION_WIDTH = 4;
  localparam C_AXI_BRESP_WIDTH  = 2;
  localparam C_AXI_RRESP_WIDTH  = 2;

  localparam IS_AXI_STREAMING  = C_INTERFACE_TYPE == 1 ? 1 : 0;
  localparam TDATA_OFFSET      = C_HAS_AXIS_TDATA == 1 ? C_DIN_WIDTH_AXIS-C_AXIS_TDATA_WIDTH : C_DIN_WIDTH_AXIS;
  localparam TSTRB_OFFSET      = C_HAS_AXIS_TSTRB == 1 ? TDATA_OFFSET-C_AXIS_TSTRB_WIDTH : TDATA_OFFSET;
  localparam TKEEP_OFFSET      = C_HAS_AXIS_TKEEP == 1 ? TSTRB_OFFSET-C_AXIS_TKEEP_WIDTH : TSTRB_OFFSET;
  localparam TID_OFFSET        = C_HAS_AXIS_TID   == 1 ? TKEEP_OFFSET-C_AXIS_TID_WIDTH : TKEEP_OFFSET;
  localparam TDEST_OFFSET      = C_HAS_AXIS_TDEST == 1 ? TID_OFFSET-C_AXIS_TDEST_WIDTH : TID_OFFSET;
  localparam TUSER_OFFSET      = C_HAS_AXIS_TUSER == 1 ? TDEST_OFFSET-C_AXIS_TUSER_WIDTH : TDEST_OFFSET;
  localparam LOG_DEPTH_AXIS    = find_log2(C_WR_DEPTH_AXIS); 
  localparam LOG_WR_DEPTH      = find_log2(C_WR_DEPTH); 


  function [LOG_DEPTH_AXIS-1:0] bin2gray;
      input [LOG_DEPTH_AXIS-1:0] x;
      begin
         bin2gray = x ^ (x>>1);
      end
   endfunction

  function [LOG_DEPTH_AXIS-1:0] gray2bin;
      input [LOG_DEPTH_AXIS-1:0] x;
      integer                i;
      begin
         gray2bin[LOG_DEPTH_AXIS-1] = x[LOG_DEPTH_AXIS-1];
         for(i=LOG_DEPTH_AXIS-2; i>=0; i=i-1) begin
            gray2bin[i] =  gray2bin[i+1] ^ x[i];
         end
      end
   endfunction

wire [(LOG_WR_DEPTH)-1 : 0] w_cnt_gc_asreg_last;
wire  [LOG_WR_DEPTH-1 : 0]  w_q [0:C_SYNCHRONIZER_STAGE] ;
wire [LOG_WR_DEPTH-1 : 0] w_q_temp [1:C_SYNCHRONIZER_STAGE]  ;
reg [LOG_WR_DEPTH-1 : 0] w_cnt_rd = 0;
reg [LOG_WR_DEPTH-1 : 0] w_cnt = 0;
reg [LOG_WR_DEPTH-1 : 0] w_cnt_gc = 0;
reg [LOG_WR_DEPTH-1 : 0] r_cnt = 0;
wire [LOG_WR_DEPTH : 0] adj_w_cnt_rd_pad;
wire [LOG_WR_DEPTH : 0] r_inv_pad;
wire [LOG_WR_DEPTH-1 : 0] d_cnt;
reg [LOG_WR_DEPTH : 0] d_cnt_pad = 0;
reg adj_w_cnt_rd_pad_0 = 0;
reg r_inv_pad_0 = 0;


   genvar l;

   generate for (l = 1; ((l <= C_SYNCHRONIZER_STAGE) && (C_HAS_DATA_COUNTS_AXIS == 3 && C_INTERFACE_TYPE == 0) ); l = l + 1) begin : g_cnt_sync_stage
     fifo_generator_v13_1_2_sync_stage
       #(
         .C_WIDTH  (LOG_WR_DEPTH)
        )
     rd_stg_inst
        (
         .RST      (rd_rst_int), 
         .CLK      (RD_CLK), 
         .DIN      (w_q[l-1]), 
         .DOUT     (w_q[l])
        );
   end endgenerate // gpkt_cnt_sync_stage



      generate if (C_INTERFACE_TYPE == 0 && C_HAS_DATA_COUNTS_AXIS == 3) begin : fifo_ic_adapter
    assign wr_eop_ad = WR_EN & !(FULL);
    assign rd_eop_ad = RD_EN & !(EMPTY);


  always @ (posedge wr_rst_int or posedge WR_CLK)
    begin
      if (wr_rst_int)
        w_cnt    <= 1'b0;
      else if (wr_eop_ad)
        w_cnt    <= w_cnt + 1;
    end

  always @ (posedge wr_rst_int or posedge WR_CLK)
    begin
      if (wr_rst_int)
        w_cnt_gc    <= 1'b0;
      else 
        w_cnt_gc    <= bin2gray(w_cnt);
    end


    assign  w_q[0]  = w_cnt_gc;
    assign  w_cnt_gc_asreg_last       = w_q[C_SYNCHRONIZER_STAGE];



  always @ (posedge rd_rst_int or posedge RD_CLK)
    begin
      if (rd_rst_int)
        w_cnt_rd    <= 1'b0;
      else 
        w_cnt_rd    <= gray2bin(w_cnt_gc_asreg_last);
    end

  always @ (posedge rd_rst_int or posedge RD_CLK)
    begin
      if (rd_rst_int)
        r_cnt    <= 1'b0;
      else if (rd_eop_ad)
        r_cnt    <= r_cnt + 1;
    end


  // Take the difference of write and read packet count
  // Logic is similar to rd_pe_as
   assign adj_w_cnt_rd_pad[LOG_WR_DEPTH : 1] = w_cnt_rd;
   assign r_inv_pad[LOG_WR_DEPTH : 1]        = ~r_cnt;
   assign adj_w_cnt_rd_pad[0]                = adj_w_cnt_rd_pad_0;
   assign r_inv_pad[0]                       = r_inv_pad_0;


  always @ ( rd_eop_ad )
    begin
      if (!rd_eop_ad) begin
        adj_w_cnt_rd_pad_0    <= 1'b1;
        r_inv_pad_0           <= 1'b1;
      end else begin 
        adj_w_cnt_rd_pad_0    <= 1'b0;
        r_inv_pad_0           <= 1'b0;
      end	
    end

  always @ (posedge rd_rst_int or posedge RD_CLK)
    begin
      if (rd_rst_int)
        d_cnt_pad    <= 1'b0;
      else 
        d_cnt_pad    <= adj_w_cnt_rd_pad + r_inv_pad ;
    end

   assign  d_cnt = d_cnt_pad [LOG_WR_DEPTH : 1] ;
   assign  WR_DATA_COUNT = d_cnt;

  end endgenerate // fifo_ic_adapter

      generate if (C_INTERFACE_TYPE == 0 && C_HAS_DATA_COUNTS_AXIS != 3) begin : fifo_icn_adapter
   assign  WR_DATA_COUNT = wr_data_count_in;

  end endgenerate // fifo_icn_adapter



  wire                          inverted_reset = ~S_ARESETN;
  wire                          axi_rs_rst;
  wire  [C_DIN_WIDTH_AXIS-1:0]  axis_din          ;
  wire  [C_DIN_WIDTH_AXIS-1:0]  axis_dout         ;
  wire                          axis_full         ;
  wire                          axis_almost_full  ;
  wire                          axis_empty        ;
  wire                          axis_s_axis_tready;
  wire                          axis_m_axis_tvalid;
  wire                          axis_wr_en        ;
  wire                          axis_rd_en        ;
  wire                          axis_we           ;
  wire                          axis_re           ;
  wire [C_WR_PNTR_WIDTH_AXIS:0] axis_dc;
  reg                           axis_pkt_read = 1'b0;
  wire                          axis_rd_rst;
  wire                          axis_wr_rst;

  generate if (C_INTERFACE_TYPE > 0 && (C_AXIS_TYPE == 1 || C_WACH_TYPE == 1 ||
               C_WDCH_TYPE == 1 || C_WRCH_TYPE == 1 || C_RACH_TYPE == 1 || C_RDCH_TYPE == 1)) begin : gaxi_rs_rst
      reg                           rst_d1 = 0        ;
      reg                           rst_d2 = 0        ;
      reg [3:0]                    axi_rst = 4'h0     ;
      always @ (posedge inverted_reset or posedge S_ACLK) begin
        if (inverted_reset) begin
          rst_d1         <= 1'b1;
          rst_d2         <= 1'b1;
          axi_rst        <= 4'hf;
        end else begin
          rst_d1         <= #`TCQ 1'b0;
          rst_d2         <= #`TCQ rst_d1;
          axi_rst        <= #`TCQ {axi_rst[2:0],1'b0};
        end
      end

      assign axi_rs_rst = axi_rst[3];//rst_d2;
  end endgenerate // gaxi_rs_rst

  generate if (IS_AXI_STREAMING == 1 && C_AXIS_TYPE == 0) begin : axi_streaming

    // Write protection when almost full or prog_full is high
    assign axis_we    = (C_PROG_FULL_TYPE_AXIS != 0) ? axis_s_axis_tready & S_AXIS_TVALID : 
                        (C_APPLICATION_TYPE_AXIS == 1) ? axis_s_axis_tready & S_AXIS_TVALID : S_AXIS_TVALID;

    // Read protection when almost empty or prog_empty is high
    assign axis_re    = (C_PROG_EMPTY_TYPE_AXIS != 0) ? axis_m_axis_tvalid & M_AXIS_TREADY :
                        (C_APPLICATION_TYPE_AXIS == 1) ? axis_m_axis_tvalid & M_AXIS_TREADY : M_AXIS_TREADY;
    assign axis_wr_en = (C_HAS_SLAVE_CE == 1)  ? axis_we & S_ACLK_EN : axis_we;
    assign axis_rd_en = (C_HAS_MASTER_CE == 1) ? axis_re & M_ACLK_EN : axis_re;

    fifo_generator_v13_1_2_CONV_VER
      #(
        .C_FAMILY			(C_FAMILY),
        .C_COMMON_CLOCK                 (C_COMMON_CLOCK),
        .C_INTERFACE_TYPE               (C_INTERFACE_TYPE),
        .C_MEMORY_TYPE			((C_IMPLEMENTATION_TYPE_AXIS == 1  || C_IMPLEMENTATION_TYPE_AXIS == 11) ? 1 :
                                         (C_IMPLEMENTATION_TYPE_AXIS == 2  || C_IMPLEMENTATION_TYPE_AXIS == 12) ? 2 : 4),
        .C_IMPLEMENTATION_TYPE		((C_IMPLEMENTATION_TYPE_AXIS == 1  || C_IMPLEMENTATION_TYPE_AXIS == 2) ? 0 :
                                         (C_IMPLEMENTATION_TYPE_AXIS == 11 || C_IMPLEMENTATION_TYPE_AXIS == 12) ? 2 : 6),
        .C_PRELOAD_REGS			(1), // always FWFT for AXI
        .C_PRELOAD_LATENCY		(0), // always FWFT for AXI
        .C_DIN_WIDTH			(C_DIN_WIDTH_AXIS),
        .C_WR_DEPTH			(C_WR_DEPTH_AXIS),
        .C_WR_PNTR_WIDTH		(C_WR_PNTR_WIDTH_AXIS),
        .C_DOUT_WIDTH			(C_DIN_WIDTH_AXIS),
        .C_RD_DEPTH			(C_WR_DEPTH_AXIS),
        .C_RD_PNTR_WIDTH		(C_WR_PNTR_WIDTH_AXIS),
        .C_PROG_FULL_TYPE		(C_PROG_FULL_TYPE_AXIS),
        .C_PROG_FULL_THRESH_ASSERT_VAL	(C_PROG_FULL_THRESH_ASSERT_VAL_AXIS),
        .C_PROG_EMPTY_TYPE		(C_PROG_EMPTY_TYPE_AXIS),
        .C_PROG_EMPTY_THRESH_ASSERT_VAL	(C_PROG_EMPTY_THRESH_ASSERT_VAL_AXIS),
        .C_USE_ECC                      (C_USE_ECC_AXIS),
        .C_ERROR_INJECTION_TYPE         (C_ERROR_INJECTION_TYPE_AXIS),
        .C_HAS_ALMOST_EMPTY		(0),
        .C_HAS_ALMOST_FULL		(C_APPLICATION_TYPE_AXIS == 1 ? 1: 0),
        .C_AXI_TYPE                     (C_INTERFACE_TYPE == 1 ? 0 : C_AXI_TYPE),
        .C_USE_EMBEDDED_REG		(C_USE_EMBEDDED_REG),
        .C_FIFO_TYPE                    (C_APPLICATION_TYPE_AXIS == 1 ? 0: C_APPLICATION_TYPE_AXIS),
        .C_SYNCHRONIZER_STAGE           (C_SYNCHRONIZER_STAGE),

        .C_HAS_WR_RST			(0),
        .C_HAS_RD_RST			(0),
        .C_HAS_RST			(1),
        .C_HAS_SRST			(0),
        .C_DOUT_RST_VAL			(0),

        .C_HAS_VALID			(0),
        .C_VALID_LOW			(C_VALID_LOW),
        .C_HAS_UNDERFLOW		(C_HAS_UNDERFLOW),
        .C_UNDERFLOW_LOW		(C_UNDERFLOW_LOW),
        .C_HAS_WR_ACK			(0),
        .C_WR_ACK_LOW			(C_WR_ACK_LOW),
        .C_HAS_OVERFLOW			(C_HAS_OVERFLOW),
        .C_OVERFLOW_LOW			(C_OVERFLOW_LOW),

        .C_HAS_DATA_COUNT		((C_COMMON_CLOCK == 1 && C_HAS_DATA_COUNTS_AXIS == 1) ? 1 : 0),
        .C_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_AXIS + 1),
        .C_HAS_RD_DATA_COUNT		((C_COMMON_CLOCK == 0 && C_HAS_DATA_COUNTS_AXIS == 1) ? 1 : 0),
        .C_RD_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_AXIS + 1),
        .C_USE_FWFT_DATA_COUNT		(1), // use extra logic is always true
        .C_HAS_WR_DATA_COUNT		((C_COMMON_CLOCK == 0 && C_HAS_DATA_COUNTS_AXIS == 1) ? 1 : 0),
        .C_WR_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_AXIS + 1),
        .C_FULL_FLAGS_RST_VAL           (1),
        .C_USE_DOUT_RST                 (0),
        .C_MSGON_VAL                    (C_MSGON_VAL),
        .C_ENABLE_RST_SYNC              (1),
        .C_EN_SAFETY_CKT                ((C_IMPLEMENTATION_TYPE_AXIS == 1 || C_IMPLEMENTATION_TYPE_AXIS == 11) ? 1 : 0),
        .C_COUNT_TYPE			(C_COUNT_TYPE),
        .C_DEFAULT_VALUE		(C_DEFAULT_VALUE),
        .C_ENABLE_RLOCS			(C_ENABLE_RLOCS),
        .C_HAS_BACKUP			(C_HAS_BACKUP),
        .C_HAS_INT_CLK                  (C_HAS_INT_CLK),
        .C_MIF_FILE_NAME		(C_MIF_FILE_NAME),
        .C_HAS_MEMINIT_FILE		(C_HAS_MEMINIT_FILE),
        .C_INIT_WR_PNTR_VAL		(C_INIT_WR_PNTR_VAL),
        .C_OPTIMIZATION_MODE		(C_OPTIMIZATION_MODE),
        .C_PRIM_FIFO_TYPE		(C_PRIM_FIFO_TYPE),
        .C_RD_FREQ			(C_RD_FREQ),
        .C_USE_FIFO16_FLAGS		(C_USE_FIFO16_FLAGS),
        .C_WR_FREQ			(C_WR_FREQ),
        .C_WR_RESPONSE_LATENCY		(C_WR_RESPONSE_LATENCY)
      )
    fifo_generator_v13_1_2_axis_dut
      (
        .CLK                      (S_ACLK),
        .WR_CLK                   (S_ACLK),
        .RD_CLK                   (M_ACLK),
        .RST                      (inverted_reset),
        .SRST                     (1'b0),
        .WR_RST                   (inverted_reset),
        .RD_RST                   (inverted_reset),
        .WR_EN                    (axis_wr_en),
        .RD_EN                    (axis_rd_en),
        .PROG_FULL_THRESH         (AXIS_PROG_FULL_THRESH),
        .PROG_FULL_THRESH_ASSERT  ({C_WR_PNTR_WIDTH_AXIS{1'b0}}),
        .PROG_FULL_THRESH_NEGATE  ({C_WR_PNTR_WIDTH_AXIS{1'b0}}),
        .PROG_EMPTY_THRESH        (AXIS_PROG_EMPTY_THRESH),
        .PROG_EMPTY_THRESH_ASSERT ({C_WR_PNTR_WIDTH_AXIS{1'b0}}),
        .PROG_EMPTY_THRESH_NEGATE ({C_WR_PNTR_WIDTH_AXIS{1'b0}}),
        .INJECTDBITERR            (AXIS_INJECTDBITERR), 
        .INJECTSBITERR            (AXIS_INJECTSBITERR),
  
        .DIN                      (axis_din),
        .DOUT                     (axis_dout),
        .FULL                     (axis_full),
        .EMPTY                    (axis_empty),
        .ALMOST_FULL              (axis_almost_full),
        .PROG_FULL                (AXIS_PROG_FULL),
        .ALMOST_EMPTY             (),
        .PROG_EMPTY               (AXIS_PROG_EMPTY),
  
        .WR_ACK                   (),
        .OVERFLOW                 (AXIS_OVERFLOW),
        .VALID                    (),
        .UNDERFLOW                (AXIS_UNDERFLOW),
        .DATA_COUNT               (axis_dc),
        .RD_DATA_COUNT            (AXIS_RD_DATA_COUNT),
        .WR_DATA_COUNT            (AXIS_WR_DATA_COUNT),
        .SBITERR                  (AXIS_SBITERR),
        .DBITERR                  (AXIS_DBITERR),
        .wr_rst_busy              (wr_rst_busy_axis),
        .rd_rst_busy              (rd_rst_busy_axis),
        .wr_rst_i_out             (axis_wr_rst),
        .rd_rst_i_out             (axis_rd_rst),
  
        .BACKUP                   (BACKUP),
        .BACKUP_MARKER            (BACKUP_MARKER),
        .INT_CLK                  (INT_CLK)
       );

    assign axis_s_axis_tready    = (IS_8SERIES == 0) ? ~axis_full : (C_IMPLEMENTATION_TYPE_AXIS == 5 || C_IMPLEMENTATION_TYPE_AXIS == 13) ? ~(axis_full | wr_rst_busy_axis) : ~axis_full;
    assign axis_m_axis_tvalid    = (C_APPLICATION_TYPE_AXIS != 1) ? ~axis_empty : ~axis_empty & axis_pkt_read;
    assign S_AXIS_TREADY         = axis_s_axis_tready;
    assign M_AXIS_TVALID         = axis_m_axis_tvalid;

  end endgenerate // axi_streaming

  wire axis_wr_eop;
  reg  axis_wr_eop_d1 = 1'b0;
  wire axis_rd_eop;
  integer  axis_pkt_cnt;

  generate if (C_APPLICATION_TYPE_AXIS == 1 && C_COMMON_CLOCK == 1) begin : gaxis_pkt_fifo_cc
    assign axis_wr_eop = axis_wr_en & S_AXIS_TLAST;
    assign axis_rd_eop = axis_rd_en & axis_dout[0];

    always @ (posedge inverted_reset or posedge S_ACLK)
    begin
      if (inverted_reset)
        axis_pkt_read    <= 1'b0;
      else if (axis_rd_eop && (axis_pkt_cnt == 1) && ~axis_wr_eop_d1)
        axis_pkt_read    <= 1'b0;
      else if ((axis_pkt_cnt > 0) || (axis_almost_full && ~axis_empty))
        axis_pkt_read    <= 1'b1;
    end

    always @ (posedge inverted_reset or posedge S_ACLK)
    begin
      if (inverted_reset)
        axis_wr_eop_d1    <= 1'b0;
      else
        axis_wr_eop_d1   <= axis_wr_eop;
    end

    always @ (posedge inverted_reset or posedge S_ACLK)
    begin
      if (inverted_reset)
        axis_pkt_cnt    <= 0;
      else if (axis_wr_eop_d1 && ~axis_rd_eop)
        axis_pkt_cnt    <= axis_pkt_cnt + 1;
      else if (axis_rd_eop && ~axis_wr_eop_d1)
        axis_pkt_cnt    <= axis_pkt_cnt - 1;
    end
  end endgenerate // gaxis_pkt_fifo_cc


reg [LOG_DEPTH_AXIS-1 : 0] axis_wpkt_cnt_gc = 0;
wire [(LOG_DEPTH_AXIS)-1 : 0] axis_wpkt_cnt_gc_asreg_last;
wire axis_rd_has_rst;
wire [0:C_SYNCHRONIZER_STAGE] axis_af_q ;
wire  [LOG_DEPTH_AXIS-1 : 0]  wpkt_q [0:C_SYNCHRONIZER_STAGE] ;
wire [1:C_SYNCHRONIZER_STAGE] axis_af_q_temp = 0;
wire [LOG_DEPTH_AXIS-1 : 0] wpkt_q_temp [1:C_SYNCHRONIZER_STAGE]  ;
reg [LOG_DEPTH_AXIS-1 : 0] axis_wpkt_cnt_rd = 0;
reg [LOG_DEPTH_AXIS-1 : 0] axis_wpkt_cnt = 0;
reg [LOG_DEPTH_AXIS-1 : 0] axis_rpkt_cnt = 0;
wire [LOG_DEPTH_AXIS : 0] adj_axis_wpkt_cnt_rd_pad;
wire [LOG_DEPTH_AXIS : 0] rpkt_inv_pad;
wire [LOG_DEPTH_AXIS-1 : 0] diff_pkt_cnt;
reg [LOG_DEPTH_AXIS : 0] diff_pkt_cnt_pad = 0;
reg adj_axis_wpkt_cnt_rd_pad_0 = 0;
reg rpkt_inv_pad_0 = 0;
wire axis_af_rd ;

generate if (C_HAS_RST == 1) begin : rst_blk_has
  assign axis_rd_has_rst = axis_rd_rst;
end endgenerate //rst_blk_has

generate if (C_HAS_RST == 0) begin :rst_blk_no
  assign axis_rd_has_rst = 1'b0;
end endgenerate //rst_blk_no

   genvar i;

   generate for (i = 1; ((i <= C_SYNCHRONIZER_STAGE) && (C_APPLICATION_TYPE_AXIS == 1 && C_COMMON_CLOCK == 0) ); i = i + 1) begin : gpkt_cnt_sync_stage
     fifo_generator_v13_1_2_sync_stage
       #(
         .C_WIDTH  (LOG_DEPTH_AXIS)
        )
     rd_stg_inst
        (
         .RST      (axis_rd_has_rst), 
         .CLK      (M_ACLK), 
         .DIN      (wpkt_q[i-1]), 
         .DOUT     (wpkt_q[i])
        );
 
     fifo_generator_v13_1_2_sync_stage
       #(
         .C_WIDTH  (1)
        )
     wr_stg_inst
        (
         .RST      (axis_rd_has_rst), 
         .CLK      (M_ACLK), 
         .DIN      (axis_af_q[i-1]), 
         .DOUT     (axis_af_q[i])
        );
   end endgenerate // gpkt_cnt_sync_stage


  generate if (C_APPLICATION_TYPE_AXIS == 1 && C_COMMON_CLOCK == 0) begin : gaxis_pkt_fifo_ic
    assign axis_wr_eop = axis_wr_en & S_AXIS_TLAST;
    assign axis_rd_eop = axis_rd_en & axis_dout[0];

    always @ (posedge axis_rd_has_rst or posedge M_ACLK)
    begin
      if (axis_rd_has_rst)
        axis_pkt_read    <= 1'b0;
      else if (axis_rd_eop && (diff_pkt_cnt == 1))
        axis_pkt_read    <= 1'b0;
      else if ((diff_pkt_cnt > 0) || (axis_af_rd && ~axis_empty))
        axis_pkt_read    <= 1'b1;
    end

  always @ (posedge axis_wr_rst or posedge S_ACLK)
    begin
      if (axis_wr_rst)
        axis_wpkt_cnt    <= 1'b0;
      else if (axis_wr_eop)
        axis_wpkt_cnt    <= axis_wpkt_cnt + 1;
    end

  always @ (posedge axis_wr_rst or posedge S_ACLK)
    begin
      if (axis_wr_rst)
        axis_wpkt_cnt_gc    <= 1'b0;
      else 
        axis_wpkt_cnt_gc    <= bin2gray(axis_wpkt_cnt);
    end


    assign  wpkt_q[0]  = axis_wpkt_cnt_gc;
    assign  axis_wpkt_cnt_gc_asreg_last       = wpkt_q[C_SYNCHRONIZER_STAGE];
    assign  axis_af_q[0]                      = axis_almost_full;
    //assign  axis_af_q[1:C_SYNCHRONIZER_STAGE] = axis_af_q_temp[1:C_SYNCHRONIZER_STAGE];
    assign  axis_af_rd                        = axis_af_q[C_SYNCHRONIZER_STAGE];



  always @ (posedge axis_rd_has_rst or posedge M_ACLK)
    begin
      if (axis_rd_has_rst)
        axis_wpkt_cnt_rd    <= 1'b0;
      else 
        axis_wpkt_cnt_rd    <= gray2bin(axis_wpkt_cnt_gc_asreg_last);
    end

  always @ (posedge axis_rd_rst or posedge M_ACLK)
    begin
      if (axis_rd_has_rst)
        axis_rpkt_cnt    <= 1'b0;
      else if (axis_rd_eop)
        axis_rpkt_cnt    <= axis_rpkt_cnt + 1;
    end


  // Take the difference of write and read packet count
  // Logic is similar to rd_pe_as
   assign adj_axis_wpkt_cnt_rd_pad[LOG_DEPTH_AXIS : 1] = axis_wpkt_cnt_rd;
   assign rpkt_inv_pad[LOG_DEPTH_AXIS : 1]             = ~axis_rpkt_cnt;
   assign adj_axis_wpkt_cnt_rd_pad[0]                                = adj_axis_wpkt_cnt_rd_pad_0;
   assign rpkt_inv_pad[0]                                            = rpkt_inv_pad_0;


  always @ ( axis_rd_eop )
    begin
      if (!axis_rd_eop) begin
        adj_axis_wpkt_cnt_rd_pad_0    <= 1'b1;
        rpkt_inv_pad_0                <= 1'b1;
      end else begin 
        adj_axis_wpkt_cnt_rd_pad_0    <= 1'b0;
        rpkt_inv_pad_0                <= 1'b0;
      end	
    end

  always @ (posedge axis_rd_rst or posedge M_ACLK)
    begin
      if (axis_rd_has_rst)
        diff_pkt_cnt_pad    <= 1'b0;
      else 
        diff_pkt_cnt_pad    <= adj_axis_wpkt_cnt_rd_pad + rpkt_inv_pad ;
    end

   assign  diff_pkt_cnt = diff_pkt_cnt_pad [LOG_DEPTH_AXIS : 1] ;





   end endgenerate // gaxis_pkt_fifo_ic




  // Generate the accurate data count for axi stream packet fifo configuration
  reg [C_WR_PNTR_WIDTH_AXIS:0] axis_dc_pkt_fifo = 0;
  generate if (IS_AXI_STREAMING == 1 && C_HAS_DATA_COUNTS_AXIS == 1 && C_APPLICATION_TYPE_AXIS == 1) begin : gdc_pkt
    always @ (posedge inverted_reset or posedge S_ACLK)
    begin
      if (inverted_reset)
        axis_dc_pkt_fifo <= 0;
      else if (axis_wr_en && (~axis_rd_en))
        axis_dc_pkt_fifo <= #`TCQ axis_dc_pkt_fifo + 1;
      else if (~axis_wr_en && axis_rd_en)
        axis_dc_pkt_fifo <= #`TCQ axis_dc_pkt_fifo - 1;
    end
    assign AXIS_DATA_COUNT = axis_dc_pkt_fifo;
  end endgenerate // gdc_pkt

  generate if (IS_AXI_STREAMING == 1 && C_HAS_DATA_COUNTS_AXIS == 0 && C_APPLICATION_TYPE_AXIS == 1) begin : gndc_pkt
    assign AXIS_DATA_COUNT = 0;
  end endgenerate // gndc_pkt

  generate if (IS_AXI_STREAMING == 1 && C_APPLICATION_TYPE_AXIS != 1) begin : gdc
    assign AXIS_DATA_COUNT = axis_dc;
  end endgenerate // gdc

  // Register Slice for Write Address Channel
  generate if (C_AXIS_TYPE == 1) begin : gaxis_reg_slice
    assign axis_wr_en = (C_HAS_SLAVE_CE == 1)  ? S_AXIS_TVALID & S_ACLK_EN : S_AXIS_TVALID;
    assign axis_rd_en = (C_HAS_MASTER_CE == 1) ? M_AXIS_TREADY & M_ACLK_EN : M_AXIS_TREADY;

    fifo_generator_v13_1_2_axic_reg_slice
          #(
            .C_FAMILY                (C_FAMILY),
            .C_DATA_WIDTH            (C_DIN_WIDTH_AXIS),
            .C_REG_CONFIG            (C_REG_SLICE_MODE_AXIS)
            )
    axis_reg_slice_inst
        (
          // System Signals
          .ACLK                      (S_ACLK),
          .ARESET                    (axi_rs_rst),

          // Slave side
          .S_PAYLOAD_DATA            (axis_din),
          .S_VALID                   (axis_wr_en),
          .S_READY                   (S_AXIS_TREADY),

          // Master side
          .M_PAYLOAD_DATA            (axis_dout),
          .M_VALID                   (M_AXIS_TVALID),
          .M_READY                   (axis_rd_en)
          );
  end endgenerate // gaxis_reg_slice



  generate if ((IS_AXI_STREAMING == 1 || C_AXIS_TYPE == 1) && C_HAS_AXIS_TDATA == 1) begin : tdata
    assign axis_din[C_DIN_WIDTH_AXIS-1:TDATA_OFFSET] = S_AXIS_TDATA;
    assign M_AXIS_TDATA   = axis_dout[C_DIN_WIDTH_AXIS-1:TDATA_OFFSET];
  end endgenerate

  generate if ((IS_AXI_STREAMING == 1 || C_AXIS_TYPE == 1) && C_HAS_AXIS_TSTRB == 1) begin : tstrb
    assign axis_din[TDATA_OFFSET-1:TSTRB_OFFSET] = S_AXIS_TSTRB;
    assign M_AXIS_TSTRB   = axis_dout[TDATA_OFFSET-1:TSTRB_OFFSET];
  end endgenerate

  generate if ((IS_AXI_STREAMING == 1 || C_AXIS_TYPE == 1) && C_HAS_AXIS_TKEEP == 1) begin : tkeep
    assign axis_din[TSTRB_OFFSET-1:TKEEP_OFFSET] = S_AXIS_TKEEP;
    assign M_AXIS_TKEEP   = axis_dout[TSTRB_OFFSET-1:TKEEP_OFFSET];
  end endgenerate

  generate if ((IS_AXI_STREAMING == 1 || C_AXIS_TYPE == 1) && C_HAS_AXIS_TID == 1) begin : tid
    assign axis_din[TKEEP_OFFSET-1:TID_OFFSET] = S_AXIS_TID;
    assign M_AXIS_TID     = axis_dout[TKEEP_OFFSET-1:TID_OFFSET];
  end endgenerate

  generate if ((IS_AXI_STREAMING == 1 || C_AXIS_TYPE == 1) && C_HAS_AXIS_TDEST == 1) begin : tdest
    assign axis_din[TID_OFFSET-1:TDEST_OFFSET] = S_AXIS_TDEST;
    assign M_AXIS_TDEST   = axis_dout[TID_OFFSET-1:TDEST_OFFSET];
  end endgenerate

  generate if ((IS_AXI_STREAMING == 1 || C_AXIS_TYPE == 1) && C_HAS_AXIS_TUSER == 1) begin : tuser
    assign axis_din[TDEST_OFFSET-1:TUSER_OFFSET] = S_AXIS_TUSER;
    assign M_AXIS_TUSER   = axis_dout[TDEST_OFFSET-1:TUSER_OFFSET];
  end endgenerate

  generate if ((IS_AXI_STREAMING == 1 || C_AXIS_TYPE == 1) && C_HAS_AXIS_TLAST == 1) begin : tlast
    assign axis_din[0] = S_AXIS_TLAST;
    assign M_AXIS_TLAST   = axis_dout[0];
  end endgenerate

  //###########################################################################
  //  AXI FULL Write Channel (axi_write_channel)
  //###########################################################################

  localparam IS_AXI_FULL       = ((C_INTERFACE_TYPE == 2) && (C_AXI_TYPE != 2)) ? 1 : 0;
  localparam IS_AXI_LITE       = ((C_INTERFACE_TYPE == 2) && (C_AXI_TYPE == 2)) ? 1 : 0;

  localparam IS_AXI_FULL_WACH  = ((IS_AXI_FULL == 1) && (C_WACH_TYPE == 0) && C_HAS_AXI_WR_CHANNEL == 1) ? 1 : 0;
  localparam IS_AXI_FULL_WDCH  = ((IS_AXI_FULL == 1) && (C_WDCH_TYPE == 0) && C_HAS_AXI_WR_CHANNEL == 1) ? 1 : 0;
  localparam IS_AXI_FULL_WRCH  = ((IS_AXI_FULL == 1) && (C_WRCH_TYPE == 0) && C_HAS_AXI_WR_CHANNEL == 1) ? 1 : 0;
  localparam IS_AXI_FULL_RACH  = ((IS_AXI_FULL == 1) && (C_RACH_TYPE == 0) && C_HAS_AXI_RD_CHANNEL == 1) ? 1 : 0;
  localparam IS_AXI_FULL_RDCH  = ((IS_AXI_FULL == 1) && (C_RDCH_TYPE == 0) && C_HAS_AXI_RD_CHANNEL == 1) ? 1 : 0;

  localparam IS_AXI_LITE_WACH  = ((IS_AXI_LITE == 1) && (C_WACH_TYPE == 0) && C_HAS_AXI_WR_CHANNEL == 1) ? 1 : 0;
  localparam IS_AXI_LITE_WDCH  = ((IS_AXI_LITE == 1) && (C_WDCH_TYPE == 0) && C_HAS_AXI_WR_CHANNEL == 1) ? 1 : 0;
  localparam IS_AXI_LITE_WRCH  = ((IS_AXI_LITE == 1) && (C_WRCH_TYPE == 0) && C_HAS_AXI_WR_CHANNEL == 1) ? 1 : 0;
  localparam IS_AXI_LITE_RACH  = ((IS_AXI_LITE == 1) && (C_RACH_TYPE == 0) && C_HAS_AXI_RD_CHANNEL == 1) ? 1 : 0;
  localparam IS_AXI_LITE_RDCH  = ((IS_AXI_LITE == 1) && (C_RDCH_TYPE == 0) && C_HAS_AXI_RD_CHANNEL == 1) ? 1 : 0;

  localparam IS_WR_ADDR_CH     = ((IS_AXI_FULL_WACH == 1) || (IS_AXI_LITE_WACH == 1)) ? 1 : 0;
  localparam IS_WR_DATA_CH     = ((IS_AXI_FULL_WDCH == 1) || (IS_AXI_LITE_WDCH == 1)) ? 1 : 0;
  localparam IS_WR_RESP_CH     = ((IS_AXI_FULL_WRCH == 1) || (IS_AXI_LITE_WRCH == 1)) ? 1 : 0;
  localparam IS_RD_ADDR_CH     = ((IS_AXI_FULL_RACH == 1) || (IS_AXI_LITE_RACH == 1)) ? 1 : 0;
  localparam IS_RD_DATA_CH     = ((IS_AXI_FULL_RDCH == 1) || (IS_AXI_LITE_RDCH == 1)) ? 1 : 0;

  localparam AWID_OFFSET       = (C_AXI_TYPE != 2 && C_HAS_AXI_ID == 1) ? C_DIN_WIDTH_WACH - C_AXI_ID_WIDTH : C_DIN_WIDTH_WACH;
  localparam AWADDR_OFFSET     = AWID_OFFSET - C_AXI_ADDR_WIDTH;
  localparam AWLEN_OFFSET      = C_AXI_TYPE != 2 ? AWADDR_OFFSET - C_AXI_LEN_WIDTH : AWADDR_OFFSET;
  localparam AWSIZE_OFFSET     = C_AXI_TYPE != 2 ? AWLEN_OFFSET - C_AXI_SIZE_WIDTH : AWLEN_OFFSET;
  localparam AWBURST_OFFSET    = C_AXI_TYPE != 2 ? AWSIZE_OFFSET - C_AXI_BURST_WIDTH : AWSIZE_OFFSET;
  localparam AWLOCK_OFFSET     = C_AXI_TYPE != 2 ? AWBURST_OFFSET - C_AXI_LOCK_WIDTH : AWBURST_OFFSET;
  localparam AWCACHE_OFFSET    = C_AXI_TYPE != 2 ? AWLOCK_OFFSET - C_AXI_CACHE_WIDTH : AWLOCK_OFFSET;
  localparam AWPROT_OFFSET     = AWCACHE_OFFSET - C_AXI_PROT_WIDTH;
  localparam AWQOS_OFFSET      = AWPROT_OFFSET - C_AXI_QOS_WIDTH;
  localparam AWREGION_OFFSET   = C_AXI_TYPE == 1 ? AWQOS_OFFSET - C_AXI_REGION_WIDTH : AWQOS_OFFSET;
  localparam AWUSER_OFFSET     = C_HAS_AXI_AWUSER == 1 ? AWREGION_OFFSET-C_AXI_AWUSER_WIDTH : AWREGION_OFFSET;

  localparam WID_OFFSET        = (C_AXI_TYPE == 3 && C_HAS_AXI_ID == 1) ? C_DIN_WIDTH_WDCH - C_AXI_ID_WIDTH : C_DIN_WIDTH_WDCH;
  localparam WDATA_OFFSET      = WID_OFFSET - C_AXI_DATA_WIDTH;
  localparam WSTRB_OFFSET      = WDATA_OFFSET - C_AXI_DATA_WIDTH/8;
  localparam WUSER_OFFSET      = C_HAS_AXI_WUSER == 1 ? WSTRB_OFFSET-C_AXI_WUSER_WIDTH : WSTRB_OFFSET;

  localparam BID_OFFSET        = (C_AXI_TYPE != 2 && C_HAS_AXI_ID == 1) ? C_DIN_WIDTH_WRCH - C_AXI_ID_WIDTH : C_DIN_WIDTH_WRCH;
  localparam BRESP_OFFSET      = BID_OFFSET - C_AXI_BRESP_WIDTH;
  localparam BUSER_OFFSET      = C_HAS_AXI_BUSER == 1 ? BRESP_OFFSET-C_AXI_BUSER_WIDTH : BRESP_OFFSET;


  wire  [C_DIN_WIDTH_WACH-1:0]  wach_din          ;
  wire  [C_DIN_WIDTH_WACH-1:0]  wach_dout         ;
  wire  [C_DIN_WIDTH_WACH-1:0]  wach_dout_pkt     ;
  wire                          wach_full         ;
  wire                          wach_almost_full  ;
  wire                          wach_prog_full    ;
  wire                          wach_empty        ;
  wire                          wach_almost_empty ;
  wire                          wach_prog_empty   ;
  wire  [C_DIN_WIDTH_WDCH-1:0]  wdch_din          ;
  wire  [C_DIN_WIDTH_WDCH-1:0]  wdch_dout         ;
  wire                          wdch_full         ;
  wire                          wdch_almost_full  ;
  wire                          wdch_prog_full    ;
  wire                          wdch_empty        ;
  wire                          wdch_almost_empty ;
  wire                          wdch_prog_empty   ;
  wire  [C_DIN_WIDTH_WRCH-1:0]  wrch_din          ;
  wire  [C_DIN_WIDTH_WRCH-1:0]  wrch_dout         ;
  wire                          wrch_full         ;
  wire                          wrch_almost_full  ;
  wire                          wrch_prog_full    ;
  wire                          wrch_empty        ;
  wire                          wrch_almost_empty ;
  wire                          wrch_prog_empty   ;
  wire                          axi_aw_underflow_i;
  wire                          axi_w_underflow_i ;
  wire                          axi_b_underflow_i ;
  wire                          axi_aw_overflow_i ;
  wire                          axi_w_overflow_i  ;
  wire                          axi_b_overflow_i  ;
  wire                          axi_wr_underflow_i;
  wire                          axi_wr_overflow_i ;
  wire                          wach_s_axi_awready;
  wire                          wach_m_axi_awvalid;
  wire                          wach_wr_en        ;
  wire                          wach_rd_en        ;
  wire                          wdch_s_axi_wready ;
  wire                          wdch_m_axi_wvalid ;
  wire                          wdch_wr_en        ;
  wire                          wdch_rd_en        ;
  wire                          wrch_s_axi_bvalid ;
  wire                          wrch_m_axi_bready ;
  wire                          wrch_wr_en        ;
  wire                          wrch_rd_en        ;
  wire                          txn_count_up      ;
  wire                          txn_count_down    ;
  wire                          awvalid_en        ;
  wire                          awvalid_pkt       ;
  wire                          awready_pkt       ;
  integer                       wr_pkt_count      ;
  wire                          wach_we           ;
  wire                          wach_re           ;
  wire                          wdch_we           ;
  wire                          wdch_re           ;
  wire                          wrch_we           ;
  wire                          wrch_re           ;

  generate if (IS_WR_ADDR_CH == 1) begin : axi_write_address_channel
    // Write protection when almost full or prog_full is high
    assign wach_we    = (C_PROG_FULL_TYPE_WACH != 0) ? wach_s_axi_awready & S_AXI_AWVALID : S_AXI_AWVALID;

    // Read protection when almost empty or prog_empty is high
    assign wach_re    = (C_PROG_EMPTY_TYPE_WACH != 0 && C_APPLICATION_TYPE_WACH == 1) ? 
                        wach_m_axi_awvalid & awready_pkt & awvalid_en : 
                        (C_PROG_EMPTY_TYPE_WACH != 0 && C_APPLICATION_TYPE_WACH != 1) ? 
                        M_AXI_AWREADY && wach_m_axi_awvalid :
                        (C_PROG_EMPTY_TYPE_WACH == 0 && C_APPLICATION_TYPE_WACH == 1) ? 
                        awready_pkt & awvalid_en : 
                        (C_PROG_EMPTY_TYPE_WACH == 0 && C_APPLICATION_TYPE_WACH != 1) ? 
                        M_AXI_AWREADY : 1'b0;
    assign wach_wr_en = (C_HAS_SLAVE_CE == 1)  ? wach_we & S_ACLK_EN : wach_we;
    assign wach_rd_en = (C_HAS_MASTER_CE == 1) ? wach_re & M_ACLK_EN : wach_re;

    fifo_generator_v13_1_2_CONV_VER
      #(
        .C_FAMILY			(C_FAMILY),
        .C_COMMON_CLOCK                 (C_COMMON_CLOCK),
        .C_MEMORY_TYPE			((C_IMPLEMENTATION_TYPE_WACH == 1  || C_IMPLEMENTATION_TYPE_WACH == 11) ? 1 :
                                         (C_IMPLEMENTATION_TYPE_WACH == 2  || C_IMPLEMENTATION_TYPE_WACH == 12) ? 2 : 4),
        .C_IMPLEMENTATION_TYPE		((C_IMPLEMENTATION_TYPE_WACH == 1  || C_IMPLEMENTATION_TYPE_WACH == 2) ? 0 :
                                         (C_IMPLEMENTATION_TYPE_WACH == 11 || C_IMPLEMENTATION_TYPE_WACH == 12) ? 2 : 6),
        .C_PRELOAD_REGS			(1), // always FWFT for AXI
        .C_PRELOAD_LATENCY		(0), // always FWFT for AXI
        .C_DIN_WIDTH			(C_DIN_WIDTH_WACH),
        .C_INTERFACE_TYPE 		(C_INTERFACE_TYPE),
        .C_WR_DEPTH			(C_WR_DEPTH_WACH),
        .C_WR_PNTR_WIDTH		(C_WR_PNTR_WIDTH_WACH),
        .C_DOUT_WIDTH			(C_DIN_WIDTH_WACH),
        .C_RD_DEPTH			(C_WR_DEPTH_WACH),
        .C_RD_PNTR_WIDTH		(C_WR_PNTR_WIDTH_WACH),
        .C_PROG_FULL_TYPE		(C_PROG_FULL_TYPE_WACH),
        .C_PROG_FULL_THRESH_ASSERT_VAL	(C_PROG_FULL_THRESH_ASSERT_VAL_WACH),
        .C_PROG_EMPTY_TYPE		(C_PROG_EMPTY_TYPE_WACH),
        .C_PROG_EMPTY_THRESH_ASSERT_VAL	(C_PROG_EMPTY_THRESH_ASSERT_VAL_WACH),
        .C_USE_ECC                      (C_USE_ECC_WACH),
        .C_ERROR_INJECTION_TYPE         (C_ERROR_INJECTION_TYPE_WACH),
        .C_HAS_ALMOST_EMPTY		(0),
        .C_HAS_ALMOST_FULL		(0),
        .C_AXI_TYPE                     (C_INTERFACE_TYPE == 1 ? 0 : C_AXI_TYPE),

        .C_FIFO_TYPE                    ((C_APPLICATION_TYPE_WACH == 1)?0:C_APPLICATION_TYPE_WACH),
        .C_SYNCHRONIZER_STAGE           (C_SYNCHRONIZER_STAGE),

        .C_HAS_WR_RST			(0),
        .C_HAS_RD_RST			(0),
        .C_HAS_RST			(1),
        .C_HAS_SRST			(0),
        .C_DOUT_RST_VAL			(0),
        .C_EN_SAFETY_CKT                ((C_IMPLEMENTATION_TYPE_WACH == 1 || C_IMPLEMENTATION_TYPE_WACH == 11) ? 1 : 0),
        .C_HAS_VALID			(0),
        .C_VALID_LOW			(C_VALID_LOW),
        .C_HAS_UNDERFLOW		(C_HAS_UNDERFLOW),
        .C_UNDERFLOW_LOW		(C_UNDERFLOW_LOW),
        .C_HAS_WR_ACK			(0),
        .C_WR_ACK_LOW			(C_WR_ACK_LOW),
        .C_HAS_OVERFLOW			(C_HAS_OVERFLOW),
        .C_OVERFLOW_LOW			(C_OVERFLOW_LOW),

        .C_HAS_DATA_COUNT		((C_COMMON_CLOCK == 1 && C_HAS_DATA_COUNTS_WACH == 1) ? 1 : 0),
        .C_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_WACH + 1),
        .C_HAS_RD_DATA_COUNT		((C_COMMON_CLOCK == 0 && C_HAS_DATA_COUNTS_WACH == 1) ? 1 : 0),
        .C_RD_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_WACH + 1),
        .C_USE_FWFT_DATA_COUNT		(1), // use extra logic is always true
        .C_HAS_WR_DATA_COUNT		((C_COMMON_CLOCK == 0 && C_HAS_DATA_COUNTS_WACH == 1) ? 1 : 0),
        .C_WR_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_WACH + 1),
        .C_FULL_FLAGS_RST_VAL           (1),
        .C_USE_EMBEDDED_REG		(0),
        .C_USE_DOUT_RST                 (0),
        .C_MSGON_VAL                    (C_MSGON_VAL),
        .C_ENABLE_RST_SYNC              (1),
        .C_COUNT_TYPE			(C_COUNT_TYPE),
        .C_DEFAULT_VALUE		(C_DEFAULT_VALUE),
        .C_ENABLE_RLOCS			(C_ENABLE_RLOCS),
        .C_HAS_BACKUP			(C_HAS_BACKUP),
        .C_HAS_INT_CLK                  (C_HAS_INT_CLK),
        .C_MIF_FILE_NAME		(C_MIF_FILE_NAME),
        .C_HAS_MEMINIT_FILE		(C_HAS_MEMINIT_FILE),
        .C_INIT_WR_PNTR_VAL		(C_INIT_WR_PNTR_VAL),
        .C_OPTIMIZATION_MODE		(C_OPTIMIZATION_MODE),
        .C_PRIM_FIFO_TYPE		(C_PRIM_FIFO_TYPE),
        .C_RD_FREQ			(C_RD_FREQ),
        .C_USE_FIFO16_FLAGS		(C_USE_FIFO16_FLAGS),
        .C_WR_FREQ			(C_WR_FREQ),
        .C_WR_RESPONSE_LATENCY		(C_WR_RESPONSE_LATENCY)
      )
    fifo_generator_v13_1_2_wach_dut
      (
        .CLK                      (S_ACLK),
        .WR_CLK                   (S_ACLK),
        .RD_CLK                   (M_ACLK),
        .RST                      (inverted_reset),
        .SRST                     (1'b0),
        .WR_RST                   (inverted_reset),
        .RD_RST                   (inverted_reset),
        .WR_EN                    (wach_wr_en),
        .RD_EN                    (wach_rd_en),
        .PROG_FULL_THRESH         (AXI_AW_PROG_FULL_THRESH),
        .PROG_FULL_THRESH_ASSERT  ({C_WR_PNTR_WIDTH_WACH{1'b0}}),
        .PROG_FULL_THRESH_NEGATE  ({C_WR_PNTR_WIDTH_WACH{1'b0}}),
        .PROG_EMPTY_THRESH        (AXI_AW_PROG_EMPTY_THRESH),
        .PROG_EMPTY_THRESH_ASSERT ({C_WR_PNTR_WIDTH_WACH{1'b0}}),
        .PROG_EMPTY_THRESH_NEGATE ({C_WR_PNTR_WIDTH_WACH{1'b0}}),
        .INJECTDBITERR            (AXI_AW_INJECTDBITERR), 
        .INJECTSBITERR            (AXI_AW_INJECTSBITERR),
  
        .DIN                      (wach_din),
        .DOUT                     (wach_dout_pkt),
        .FULL                     (wach_full),
        .EMPTY                    (wach_empty),
        .ALMOST_FULL              (),
        .PROG_FULL                (AXI_AW_PROG_FULL),
        .ALMOST_EMPTY             (),
        .PROG_EMPTY               (AXI_AW_PROG_EMPTY),
  
        .WR_ACK                   (),
        .OVERFLOW                 (axi_aw_overflow_i),
        .VALID                    (),
        .UNDERFLOW                (axi_aw_underflow_i),
        .DATA_COUNT               (AXI_AW_DATA_COUNT),
        .RD_DATA_COUNT            (AXI_AW_RD_DATA_COUNT),
        .WR_DATA_COUNT            (AXI_AW_WR_DATA_COUNT),
        .SBITERR                  (AXI_AW_SBITERR),
        .DBITERR                  (AXI_AW_DBITERR),
        .wr_rst_busy              (wr_rst_busy_wach),
        .rd_rst_busy              (rd_rst_busy_wach),
        .wr_rst_i_out             (),
        .rd_rst_i_out             (),
  
        .BACKUP                   (BACKUP),
        .BACKUP_MARKER            (BACKUP_MARKER),
        .INT_CLK                  (INT_CLK)
       );

    assign wach_s_axi_awready    = (IS_8SERIES == 0) ? ~wach_full : (C_IMPLEMENTATION_TYPE_WACH == 5 || C_IMPLEMENTATION_TYPE_WACH == 13) ? ~(wach_full | wr_rst_busy_wach) : ~wach_full;
    assign wach_m_axi_awvalid   = ~wach_empty;
    assign S_AXI_AWREADY        = wach_s_axi_awready;

    assign AXI_AW_UNDERFLOW  = C_USE_COMMON_UNDERFLOW == 0 ? axi_aw_underflow_i : 0;
    assign AXI_AW_OVERFLOW   = C_USE_COMMON_OVERFLOW  == 0 ? axi_aw_overflow_i  : 0;

  end endgenerate // axi_write_address_channel

  // Register Slice for Write Address Channel
  generate if (C_WACH_TYPE == 1) begin : gwach_reg_slice

    fifo_generator_v13_1_2_axic_reg_slice
          #(
            .C_FAMILY                (C_FAMILY),
            .C_DATA_WIDTH            (C_DIN_WIDTH_WACH),
            .C_REG_CONFIG            (C_REG_SLICE_MODE_WACH)
            )
    wach_reg_slice_inst
        (
          // System Signals
          .ACLK                      (S_ACLK),
          .ARESET                    (axi_rs_rst),

          // Slave side
          .S_PAYLOAD_DATA            (wach_din),
          .S_VALID                   (S_AXI_AWVALID),
          .S_READY                   (S_AXI_AWREADY),

          // Master side
          .M_PAYLOAD_DATA            (wach_dout),
          .M_VALID                   (M_AXI_AWVALID),
          .M_READY                   (M_AXI_AWREADY)
          );
  end endgenerate // gwach_reg_slice
  
  generate if (C_APPLICATION_TYPE_WACH == 1 && C_HAS_AXI_WR_CHANNEL == 1) begin : axi_mm_pkt_fifo_wr

    fifo_generator_v13_1_2_axic_reg_slice
          #(
            .C_FAMILY                (C_FAMILY),
            .C_DATA_WIDTH            (C_DIN_WIDTH_WACH),
            .C_REG_CONFIG            (1)
            )
    wach_pkt_reg_slice_inst
        (
          // System Signals
          .ACLK                      (S_ACLK),
          .ARESET                    (inverted_reset),

          // Slave side
          .S_PAYLOAD_DATA            (wach_dout_pkt),
          .S_VALID                   (awvalid_pkt),
          .S_READY                   (awready_pkt),

          // Master side
          .M_PAYLOAD_DATA            (wach_dout),
          .M_VALID                   (M_AXI_AWVALID),
          .M_READY                   (M_AXI_AWREADY)
          );

    assign awvalid_pkt = wach_m_axi_awvalid && awvalid_en;

    assign txn_count_up = wdch_s_axi_wready && wdch_wr_en && wdch_din[0]; 
    assign txn_count_down = wach_m_axi_awvalid && awready_pkt && awvalid_en;

    always@(posedge S_ACLK or posedge inverted_reset) begin
      if(inverted_reset == 1) begin
	wr_pkt_count <= 0;
      end else begin
	if(txn_count_up == 1 && txn_count_down == 0) begin
	  wr_pkt_count <= wr_pkt_count + 1;
	end else if(txn_count_up == 0 && txn_count_down == 1) begin
	  wr_pkt_count <= wr_pkt_count - 1;
	end
      end
    end //Always end
    assign awvalid_en = (wr_pkt_count > 0)?1:0;
  end endgenerate
  
  generate if (C_APPLICATION_TYPE_WACH != 1) begin : axi_mm_fifo_wr
    assign awvalid_en    = 1;    
    assign wach_dout     = wach_dout_pkt;
    assign M_AXI_AWVALID = wach_m_axi_awvalid;
  end
  endgenerate



  generate if (IS_WR_DATA_CH == 1) begin : axi_write_data_channel
    // Write protection when almost full or prog_full is high
    assign wdch_we    = (C_PROG_FULL_TYPE_WDCH != 0) ? wdch_s_axi_wready & S_AXI_WVALID : S_AXI_WVALID;

    // Read protection when almost empty or prog_empty is high
    assign wdch_re    = (C_PROG_EMPTY_TYPE_WDCH != 0) ? wdch_m_axi_wvalid & M_AXI_WREADY : M_AXI_WREADY;
    assign wdch_wr_en = (C_HAS_SLAVE_CE == 1)  ? wdch_we & S_ACLK_EN : wdch_we;
    assign wdch_rd_en = (C_HAS_MASTER_CE == 1) ? wdch_re & M_ACLK_EN : wdch_re;


    fifo_generator_v13_1_2_CONV_VER
      #(
        .C_FAMILY			(C_FAMILY),
        .C_COMMON_CLOCK                 (C_COMMON_CLOCK),
        .C_MEMORY_TYPE			((C_IMPLEMENTATION_TYPE_WDCH == 1  || C_IMPLEMENTATION_TYPE_WDCH == 11) ? 1 :
                                         (C_IMPLEMENTATION_TYPE_WDCH == 2  || C_IMPLEMENTATION_TYPE_WDCH == 12) ? 2 : 4),
        .C_IMPLEMENTATION_TYPE		((C_IMPLEMENTATION_TYPE_WDCH == 1  || C_IMPLEMENTATION_TYPE_WDCH == 2) ? 0 :
                                         (C_IMPLEMENTATION_TYPE_WDCH == 11 || C_IMPLEMENTATION_TYPE_WDCH == 12) ? 2 : 6),
        .C_PRELOAD_REGS			(1), // always FWFT for AXI
        .C_PRELOAD_LATENCY		(0), // always FWFT for AXI
        .C_DIN_WIDTH			(C_DIN_WIDTH_WDCH),
        .C_WR_DEPTH			(C_WR_DEPTH_WDCH),
        .C_INTERFACE_TYPE 		(C_INTERFACE_TYPE),
        .C_WR_PNTR_WIDTH		(C_WR_PNTR_WIDTH_WDCH),
        .C_DOUT_WIDTH			(C_DIN_WIDTH_WDCH),
        .C_RD_DEPTH			(C_WR_DEPTH_WDCH),
        .C_RD_PNTR_WIDTH		(C_WR_PNTR_WIDTH_WDCH),
        .C_PROG_FULL_TYPE		(C_PROG_FULL_TYPE_WDCH),
        .C_PROG_FULL_THRESH_ASSERT_VAL	(C_PROG_FULL_THRESH_ASSERT_VAL_WDCH),
        .C_PROG_EMPTY_TYPE		(C_PROG_EMPTY_TYPE_WDCH),
        .C_PROG_EMPTY_THRESH_ASSERT_VAL	(C_PROG_EMPTY_THRESH_ASSERT_VAL_WDCH),
        .C_USE_ECC                      (C_USE_ECC_WDCH),
        .C_ERROR_INJECTION_TYPE         (C_ERROR_INJECTION_TYPE_WDCH),
        .C_HAS_ALMOST_EMPTY		(0),
        .C_HAS_ALMOST_FULL		(0),
        .C_AXI_TYPE                     (C_INTERFACE_TYPE == 1 ? 0 : C_AXI_TYPE),

        .C_FIFO_TYPE                    (C_APPLICATION_TYPE_WDCH),
        .C_SYNCHRONIZER_STAGE           (C_SYNCHRONIZER_STAGE),

        .C_HAS_WR_RST			(0),
        .C_HAS_RD_RST			(0),
        .C_HAS_RST			(1),
        .C_HAS_SRST			(0),
        .C_DOUT_RST_VAL			(0),

        .C_HAS_VALID			(0),
        .C_VALID_LOW			(C_VALID_LOW),
        .C_HAS_UNDERFLOW		(C_HAS_UNDERFLOW),
        .C_UNDERFLOW_LOW		(C_UNDERFLOW_LOW),
        .C_HAS_WR_ACK			(0),
        .C_WR_ACK_LOW			(C_WR_ACK_LOW),
        .C_HAS_OVERFLOW			(C_HAS_OVERFLOW),
        .C_OVERFLOW_LOW			(C_OVERFLOW_LOW),

        .C_HAS_DATA_COUNT		((C_COMMON_CLOCK == 1 && C_HAS_DATA_COUNTS_WDCH == 1) ? 1 : 0),
        .C_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_WDCH + 1),
        .C_HAS_RD_DATA_COUNT		((C_COMMON_CLOCK == 0 && C_HAS_DATA_COUNTS_WDCH == 1) ? 1 : 0),
        .C_RD_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_WDCH + 1),
        .C_USE_FWFT_DATA_COUNT		(1), // use extra logic is always true
        .C_HAS_WR_DATA_COUNT		((C_COMMON_CLOCK == 0 && C_HAS_DATA_COUNTS_WDCH == 1) ? 1 : 0),
        .C_WR_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_WDCH + 1),
        .C_FULL_FLAGS_RST_VAL           (1),
        .C_USE_EMBEDDED_REG		(0),
        .C_USE_DOUT_RST                 (0),
        .C_MSGON_VAL                    (C_MSGON_VAL),
        .C_ENABLE_RST_SYNC              (1),
        .C_EN_SAFETY_CKT                ((C_IMPLEMENTATION_TYPE_WDCH == 1 || C_IMPLEMENTATION_TYPE_WDCH == 11) ? 1 : 0),
        .C_COUNT_TYPE			(C_COUNT_TYPE),
        .C_DEFAULT_VALUE		(C_DEFAULT_VALUE),
        .C_ENABLE_RLOCS			(C_ENABLE_RLOCS),
        .C_HAS_BACKUP			(C_HAS_BACKUP),
        .C_HAS_INT_CLK                  (C_HAS_INT_CLK),
        .C_MIF_FILE_NAME		(C_MIF_FILE_NAME),
        .C_HAS_MEMINIT_FILE		(C_HAS_MEMINIT_FILE),
        .C_INIT_WR_PNTR_VAL		(C_INIT_WR_PNTR_VAL),
        .C_OPTIMIZATION_MODE		(C_OPTIMIZATION_MODE),
        .C_PRIM_FIFO_TYPE		(C_PRIM_FIFO_TYPE),
        .C_RD_FREQ			(C_RD_FREQ),
        .C_USE_FIFO16_FLAGS		(C_USE_FIFO16_FLAGS),
        .C_WR_FREQ			(C_WR_FREQ),
        .C_WR_RESPONSE_LATENCY		(C_WR_RESPONSE_LATENCY)
      )
    fifo_generator_v13_1_2_wdch_dut
      (
        .CLK                      (S_ACLK),
        .WR_CLK                   (S_ACLK),
        .RD_CLK                   (M_ACLK),
        .RST                      (inverted_reset),
        .SRST                     (1'b0),
        .WR_RST                   (inverted_reset),
        .RD_RST                   (inverted_reset),
        .WR_EN                    (wdch_wr_en),
        .RD_EN                    (wdch_rd_en),
        .PROG_FULL_THRESH         (AXI_W_PROG_FULL_THRESH),
        .PROG_FULL_THRESH_ASSERT  ({C_WR_PNTR_WIDTH_WDCH{1'b0}}),
        .PROG_FULL_THRESH_NEGATE  ({C_WR_PNTR_WIDTH_WDCH{1'b0}}),
        .PROG_EMPTY_THRESH        (AXI_W_PROG_EMPTY_THRESH),
        .PROG_EMPTY_THRESH_ASSERT ({C_WR_PNTR_WIDTH_WDCH{1'b0}}),
        .PROG_EMPTY_THRESH_NEGATE ({C_WR_PNTR_WIDTH_WDCH{1'b0}}),
        .INJECTDBITERR            (AXI_W_INJECTDBITERR), 
        .INJECTSBITERR            (AXI_W_INJECTSBITERR),
  
        .DIN                      (wdch_din),
        .DOUT                     (wdch_dout),
        .FULL                     (wdch_full),
        .EMPTY                    (wdch_empty),
        .ALMOST_FULL              (),
        .PROG_FULL                (AXI_W_PROG_FULL),
        .ALMOST_EMPTY             (),
        .PROG_EMPTY               (AXI_W_PROG_EMPTY),
  
        .WR_ACK                   (),
        .OVERFLOW                 (axi_w_overflow_i),
        .VALID                    (),
        .UNDERFLOW                (axi_w_underflow_i),
        .DATA_COUNT               (AXI_W_DATA_COUNT),
        .RD_DATA_COUNT            (AXI_W_RD_DATA_COUNT),
        .WR_DATA_COUNT            (AXI_W_WR_DATA_COUNT),
        .SBITERR                  (AXI_W_SBITERR),
        .DBITERR                  (AXI_W_DBITERR),
        .wr_rst_busy              (wr_rst_busy_wdch),
        .rd_rst_busy              (rd_rst_busy_wdch),
        .wr_rst_i_out             (),
        .rd_rst_i_out             (),
  
        .BACKUP                   (BACKUP),
        .BACKUP_MARKER            (BACKUP_MARKER),
        .INT_CLK                  (INT_CLK)
       );

    assign wdch_s_axi_wready     = (IS_8SERIES == 0) ? ~wdch_full : (C_IMPLEMENTATION_TYPE_WDCH == 5 || C_IMPLEMENTATION_TYPE_WDCH == 13) ? ~(wdch_full | wr_rst_busy_wdch) : ~wdch_full;
    assign wdch_m_axi_wvalid = ~wdch_empty;
    assign S_AXI_WREADY      = wdch_s_axi_wready;
    assign M_AXI_WVALID      = wdch_m_axi_wvalid;

    assign AXI_W_UNDERFLOW   = C_USE_COMMON_UNDERFLOW == 0 ? axi_w_underflow_i  : 0;
    assign AXI_W_OVERFLOW    = C_USE_COMMON_OVERFLOW  == 0 ? axi_w_overflow_i   : 0;

  end endgenerate // axi_write_data_channel

  // Register Slice for Write Data Channel
  generate if (C_WDCH_TYPE == 1) begin : gwdch_reg_slice

    fifo_generator_v13_1_2_axic_reg_slice
          #(
            .C_FAMILY                (C_FAMILY),
            .C_DATA_WIDTH            (C_DIN_WIDTH_WDCH),
            .C_REG_CONFIG            (C_REG_SLICE_MODE_WDCH)
            )
    wdch_reg_slice_inst
        (
          // System Signals
          .ACLK                      (S_ACLK),
          .ARESET                    (axi_rs_rst),

          // Slave side
          .S_PAYLOAD_DATA            (wdch_din),
          .S_VALID                   (S_AXI_WVALID),
          .S_READY                   (S_AXI_WREADY),

          // Master side
          .M_PAYLOAD_DATA            (wdch_dout),
          .M_VALID                   (M_AXI_WVALID),
          .M_READY                   (M_AXI_WREADY)
          );
  end endgenerate // gwdch_reg_slice

  generate if (IS_WR_RESP_CH == 1) begin : axi_write_resp_channel
    // Write protection when almost full or prog_full is high
    assign wrch_we    = (C_PROG_FULL_TYPE_WRCH != 0) ? wrch_m_axi_bready & M_AXI_BVALID : M_AXI_BVALID;

    // Read protection when almost empty or prog_empty is high
    assign wrch_re    = (C_PROG_EMPTY_TYPE_WRCH != 0) ? wrch_s_axi_bvalid & S_AXI_BREADY : S_AXI_BREADY;
    assign wrch_wr_en = (C_HAS_MASTER_CE == 1)  ? wrch_we & M_ACLK_EN : wrch_we;
    assign wrch_rd_en = (C_HAS_SLAVE_CE == 1) ? wrch_re & S_ACLK_EN : wrch_re;

    fifo_generator_v13_1_2_CONV_VER
      #(
        .C_FAMILY			(C_FAMILY),
        .C_COMMON_CLOCK                 (C_COMMON_CLOCK),
        .C_MEMORY_TYPE			((C_IMPLEMENTATION_TYPE_WRCH == 1  || C_IMPLEMENTATION_TYPE_WRCH == 11) ? 1 :
                                         (C_IMPLEMENTATION_TYPE_WRCH == 2  || C_IMPLEMENTATION_TYPE_WRCH == 12) ? 2 : 4),
        .C_IMPLEMENTATION_TYPE		((C_IMPLEMENTATION_TYPE_WRCH == 1  || C_IMPLEMENTATION_TYPE_WRCH == 2) ? 0 :
                                         (C_IMPLEMENTATION_TYPE_WRCH == 11 || C_IMPLEMENTATION_TYPE_WRCH == 12) ? 2 : 6),
        .C_PRELOAD_REGS			(1), // always FWFT for AXI
        .C_PRELOAD_LATENCY		(0), // always FWFT for AXI
        .C_DIN_WIDTH			(C_DIN_WIDTH_WRCH),
        .C_WR_DEPTH			(C_WR_DEPTH_WRCH),
        .C_WR_PNTR_WIDTH		(C_WR_PNTR_WIDTH_WRCH),
        .C_DOUT_WIDTH			(C_DIN_WIDTH_WRCH),
        .C_INTERFACE_TYPE 		(C_INTERFACE_TYPE),
        .C_RD_DEPTH			(C_WR_DEPTH_WRCH),
        .C_RD_PNTR_WIDTH		(C_WR_PNTR_WIDTH_WRCH),
        .C_PROG_FULL_TYPE		(C_PROG_FULL_TYPE_WRCH),
        .C_PROG_FULL_THRESH_ASSERT_VAL	(C_PROG_FULL_THRESH_ASSERT_VAL_WRCH),
        .C_PROG_EMPTY_TYPE		(C_PROG_EMPTY_TYPE_WRCH),
        .C_PROG_EMPTY_THRESH_ASSERT_VAL	(C_PROG_EMPTY_THRESH_ASSERT_VAL_WRCH),
        .C_USE_ECC                      (C_USE_ECC_WRCH),
        .C_ERROR_INJECTION_TYPE         (C_ERROR_INJECTION_TYPE_WRCH),
        .C_HAS_ALMOST_EMPTY		(0),
        .C_HAS_ALMOST_FULL		(0),
        .C_AXI_TYPE                     (C_INTERFACE_TYPE == 1 ? 0 : C_AXI_TYPE),

        .C_FIFO_TYPE                    (C_APPLICATION_TYPE_WRCH),
        .C_SYNCHRONIZER_STAGE           (C_SYNCHRONIZER_STAGE),

        .C_HAS_WR_RST			(0),
        .C_HAS_RD_RST			(0),
        .C_HAS_RST			(1),
        .C_HAS_SRST			(0),
        .C_DOUT_RST_VAL			(0),

        .C_HAS_VALID			(0),
        .C_VALID_LOW			(C_VALID_LOW),
        .C_HAS_UNDERFLOW		(C_HAS_UNDERFLOW),
        .C_UNDERFLOW_LOW		(C_UNDERFLOW_LOW),
        .C_HAS_WR_ACK			(0),
        .C_WR_ACK_LOW			(C_WR_ACK_LOW),
        .C_HAS_OVERFLOW			(C_HAS_OVERFLOW),
        .C_OVERFLOW_LOW			(C_OVERFLOW_LOW),

        .C_HAS_DATA_COUNT		((C_COMMON_CLOCK == 1 && C_HAS_DATA_COUNTS_WRCH == 1) ? 1 : 0),
        .C_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_WRCH + 1),
        .C_HAS_RD_DATA_COUNT		((C_COMMON_CLOCK == 0 && C_HAS_DATA_COUNTS_WRCH == 1) ? 1 : 0),
        .C_RD_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_WRCH + 1),
        .C_USE_FWFT_DATA_COUNT		(1), // use extra logic is always true
        .C_HAS_WR_DATA_COUNT		((C_COMMON_CLOCK == 0 && C_HAS_DATA_COUNTS_WRCH == 1) ? 1 : 0),
        .C_WR_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_WRCH + 1),
        .C_FULL_FLAGS_RST_VAL           (1),
        .C_USE_EMBEDDED_REG		(0),
        .C_USE_DOUT_RST                 (0),
        .C_MSGON_VAL                    (C_MSGON_VAL),
        .C_ENABLE_RST_SYNC              (1),
        .C_EN_SAFETY_CKT                ((C_IMPLEMENTATION_TYPE_WRCH == 1 || C_IMPLEMENTATION_TYPE_WRCH == 11) ? 1 : 0),
        .C_COUNT_TYPE			(C_COUNT_TYPE),
        .C_DEFAULT_VALUE		(C_DEFAULT_VALUE),
        .C_ENABLE_RLOCS			(C_ENABLE_RLOCS),
        .C_HAS_BACKUP			(C_HAS_BACKUP),
        .C_HAS_INT_CLK                  (C_HAS_INT_CLK),
        .C_MIF_FILE_NAME		(C_MIF_FILE_NAME),
        .C_HAS_MEMINIT_FILE		(C_HAS_MEMINIT_FILE),
        .C_INIT_WR_PNTR_VAL		(C_INIT_WR_PNTR_VAL),
        .C_OPTIMIZATION_MODE		(C_OPTIMIZATION_MODE),
        .C_PRIM_FIFO_TYPE		(C_PRIM_FIFO_TYPE),
        .C_RD_FREQ			(C_RD_FREQ),
        .C_USE_FIFO16_FLAGS		(C_USE_FIFO16_FLAGS),
        .C_WR_FREQ			(C_WR_FREQ),
        .C_WR_RESPONSE_LATENCY		(C_WR_RESPONSE_LATENCY)
      )
    fifo_generator_v13_1_2_wrch_dut
      (
        .CLK                      (S_ACLK),
        .WR_CLK                   (M_ACLK),
        .RD_CLK                   (S_ACLK),
        .RST                      (inverted_reset),
        .SRST                     (1'b0),
        .WR_RST                   (inverted_reset),
        .RD_RST                   (inverted_reset),
        .WR_EN                    (wrch_wr_en),
        .RD_EN                    (wrch_rd_en),
        .PROG_FULL_THRESH         (AXI_B_PROG_FULL_THRESH),
        .PROG_FULL_THRESH_ASSERT  ({C_WR_PNTR_WIDTH_WRCH{1'b0}}),
        .PROG_FULL_THRESH_NEGATE  ({C_WR_PNTR_WIDTH_WRCH{1'b0}}),
        .PROG_EMPTY_THRESH        (AXI_B_PROG_EMPTY_THRESH),
        .PROG_EMPTY_THRESH_ASSERT ({C_WR_PNTR_WIDTH_WRCH{1'b0}}),
        .PROG_EMPTY_THRESH_NEGATE ({C_WR_PNTR_WIDTH_WRCH{1'b0}}),
        .INJECTDBITERR            (AXI_B_INJECTDBITERR), 
        .INJECTSBITERR            (AXI_B_INJECTSBITERR),
  
        .DIN                      (wrch_din),
        .DOUT                     (wrch_dout),
        .FULL                     (wrch_full),
        .EMPTY                    (wrch_empty),
        .ALMOST_FULL              (),
        .ALMOST_EMPTY             (),
        .PROG_FULL                (AXI_B_PROG_FULL),
        .PROG_EMPTY               (AXI_B_PROG_EMPTY),
  
        .WR_ACK                   (),
        .OVERFLOW                 (axi_b_overflow_i),
        .VALID                    (),
        .UNDERFLOW                (axi_b_underflow_i),
        .DATA_COUNT               (AXI_B_DATA_COUNT),
        .RD_DATA_COUNT            (AXI_B_RD_DATA_COUNT),
        .WR_DATA_COUNT            (AXI_B_WR_DATA_COUNT),
        .SBITERR                  (AXI_B_SBITERR),
        .DBITERR                  (AXI_B_DBITERR),
        .wr_rst_busy              (wr_rst_busy_wrch),
        .rd_rst_busy              (rd_rst_busy_wrch),
        .wr_rst_i_out             (),
        .rd_rst_i_out             (),
  
        .BACKUP                   (BACKUP),
        .BACKUP_MARKER            (BACKUP_MARKER),
        .INT_CLK                  (INT_CLK)
       );

    assign wrch_s_axi_bvalid = ~wrch_empty;
    assign wrch_m_axi_bready     = (IS_8SERIES == 0) ? ~wrch_full : (C_IMPLEMENTATION_TYPE_WRCH == 5 || C_IMPLEMENTATION_TYPE_WRCH == 13) ? ~(wrch_full | wr_rst_busy_wrch) : ~wrch_full;
    assign S_AXI_BVALID      = wrch_s_axi_bvalid;
    assign M_AXI_BREADY      = wrch_m_axi_bready;

    assign AXI_B_UNDERFLOW   = C_USE_COMMON_UNDERFLOW == 0 ? axi_b_underflow_i  : 0;
    assign AXI_B_OVERFLOW    = C_USE_COMMON_OVERFLOW  == 0 ? axi_b_overflow_i   : 0;
  end endgenerate // axi_write_resp_channel

  // Register Slice for Write Response Channel
  generate if (C_WRCH_TYPE == 1) begin : gwrch_reg_slice

    fifo_generator_v13_1_2_axic_reg_slice
          #(
            .C_FAMILY                (C_FAMILY),
            .C_DATA_WIDTH            (C_DIN_WIDTH_WRCH),
            .C_REG_CONFIG            (C_REG_SLICE_MODE_WRCH)
            )
    wrch_reg_slice_inst
        (
          // System Signals
          .ACLK                      (S_ACLK),
          .ARESET                    (axi_rs_rst),

          // Slave side
          .S_PAYLOAD_DATA            (wrch_din),
          .S_VALID                   (M_AXI_BVALID),
          .S_READY                   (M_AXI_BREADY),

          // Master side
          .M_PAYLOAD_DATA            (wrch_dout),
          .M_VALID                   (S_AXI_BVALID),
          .M_READY                   (S_AXI_BREADY)
          );
  end endgenerate // gwrch_reg_slice


    assign axi_wr_underflow_i = C_USE_COMMON_UNDERFLOW  == 1 ? (axi_aw_underflow_i || axi_w_underflow_i || axi_b_underflow_i) : 0;
    assign axi_wr_overflow_i  = C_USE_COMMON_OVERFLOW   == 1 ? (axi_aw_overflow_i  || axi_w_overflow_i  || axi_b_overflow_i)  : 0;

  generate if (IS_AXI_FULL_WACH == 1 || (IS_AXI_FULL == 1 && C_WACH_TYPE == 1)) begin : axi_wach_output
    assign M_AXI_AWADDR    = wach_dout[AWID_OFFSET-1:AWADDR_OFFSET];    
    assign M_AXI_AWLEN     = wach_dout[AWADDR_OFFSET-1:AWLEN_OFFSET];    
    assign M_AXI_AWSIZE    = wach_dout[AWLEN_OFFSET-1:AWSIZE_OFFSET];    
    assign M_AXI_AWBURST   = wach_dout[AWSIZE_OFFSET-1:AWBURST_OFFSET];    
    assign M_AXI_AWLOCK    = wach_dout[AWBURST_OFFSET-1:AWLOCK_OFFSET];    
    assign M_AXI_AWCACHE   = wach_dout[AWLOCK_OFFSET-1:AWCACHE_OFFSET];    
    assign M_AXI_AWPROT    = wach_dout[AWCACHE_OFFSET-1:AWPROT_OFFSET];    
    assign M_AXI_AWQOS     = wach_dout[AWPROT_OFFSET-1:AWQOS_OFFSET];    
    assign wach_din[AWID_OFFSET-1:AWADDR_OFFSET]    = S_AXI_AWADDR;
    assign wach_din[AWADDR_OFFSET-1:AWLEN_OFFSET]   = S_AXI_AWLEN;
    assign wach_din[AWLEN_OFFSET-1:AWSIZE_OFFSET]   = S_AXI_AWSIZE;
    assign wach_din[AWSIZE_OFFSET-1:AWBURST_OFFSET] = S_AXI_AWBURST;
    assign wach_din[AWBURST_OFFSET-1:AWLOCK_OFFSET] = S_AXI_AWLOCK;
    assign wach_din[AWLOCK_OFFSET-1:AWCACHE_OFFSET] = S_AXI_AWCACHE;
    assign wach_din[AWCACHE_OFFSET-1:AWPROT_OFFSET] = S_AXI_AWPROT;
    assign wach_din[AWPROT_OFFSET-1:AWQOS_OFFSET]   = S_AXI_AWQOS;
  end endgenerate // axi_wach_output

  generate if ((IS_AXI_FULL_WACH == 1 || (IS_AXI_FULL == 1 && C_WACH_TYPE == 1)) && C_AXI_TYPE == 1) begin : axi_awregion
    assign M_AXI_AWREGION  = wach_dout[AWQOS_OFFSET-1:AWREGION_OFFSET];    
  end endgenerate // axi_awregion

  generate if ((IS_AXI_FULL_WACH == 1 || (IS_AXI_FULL == 1 && C_WACH_TYPE == 1)) && C_AXI_TYPE != 1) begin : naxi_awregion
    assign M_AXI_AWREGION  = 0;    
  end endgenerate // naxi_awregion

  generate if ((IS_AXI_FULL_WACH == 1 || (IS_AXI_FULL == 1 && C_WACH_TYPE == 1)) && C_HAS_AXI_AWUSER == 1) begin : axi_awuser
    assign M_AXI_AWUSER  = wach_dout[AWREGION_OFFSET-1:AWUSER_OFFSET];    
  end endgenerate // axi_awuser

  generate if ((IS_AXI_FULL_WACH == 1 || (IS_AXI_FULL == 1 && C_WACH_TYPE == 1)) && C_HAS_AXI_AWUSER == 0) begin : naxi_awuser
    assign M_AXI_AWUSER  = 0;    
  end endgenerate // naxi_awuser


  generate if ((IS_AXI_FULL_WACH == 1 || (IS_AXI_FULL == 1 && C_WACH_TYPE == 1)) && C_HAS_AXI_ID == 1) begin : axi_awid
    assign M_AXI_AWID      = wach_dout[C_DIN_WIDTH_WACH-1:AWID_OFFSET];
  end endgenerate //axi_awid

  generate if ((IS_AXI_FULL_WACH == 1 || (IS_AXI_FULL == 1 && C_WACH_TYPE == 1)) && C_HAS_AXI_ID == 0) begin : naxi_awid
    assign M_AXI_AWID      = 0;
  end endgenerate //naxi_awid

  generate if (IS_AXI_FULL_WDCH == 1 || (IS_AXI_FULL == 1 && C_WDCH_TYPE == 1)) begin : axi_wdch_output
    assign M_AXI_WDATA     = wdch_dout[WID_OFFSET-1:WDATA_OFFSET];
    assign M_AXI_WSTRB     = wdch_dout[WDATA_OFFSET-1:WSTRB_OFFSET];
    assign M_AXI_WLAST     = wdch_dout[0];
    assign wdch_din[WID_OFFSET-1:WDATA_OFFSET]   = S_AXI_WDATA;
    assign wdch_din[WDATA_OFFSET-1:WSTRB_OFFSET] = S_AXI_WSTRB;
    assign wdch_din[0]   = S_AXI_WLAST;
  end endgenerate // axi_wdch_output

  generate if ((IS_AXI_FULL_WDCH == 1 || (IS_AXI_FULL == 1 && C_WDCH_TYPE == 1)) && C_HAS_AXI_ID == 1 && C_AXI_TYPE == 3) begin
    assign M_AXI_WID       = wdch_dout[C_DIN_WIDTH_WDCH-1:WID_OFFSET];
  end endgenerate
  generate if ((IS_AXI_FULL_WDCH == 1 || (IS_AXI_FULL == 1 && C_WDCH_TYPE == 1)) && (C_HAS_AXI_ID == 0 || C_AXI_TYPE != 3)) begin
    assign M_AXI_WID       = 0;
  end endgenerate

  generate if ((IS_AXI_FULL_WDCH == 1 || (IS_AXI_FULL == 1 && C_WDCH_TYPE == 1)) && C_HAS_AXI_WUSER == 1 ) begin
    assign M_AXI_WUSER     = wdch_dout[WSTRB_OFFSET-1:WUSER_OFFSET];    
  end endgenerate
  generate if (C_HAS_AXI_WUSER == 0) begin
    assign M_AXI_WUSER       = 0;
  end endgenerate

  generate if (IS_AXI_FULL_WRCH == 1 || (IS_AXI_FULL == 1 && C_WRCH_TYPE == 1)) begin : axi_wrch_output
    assign S_AXI_BRESP = wrch_dout[BID_OFFSET-1:BRESP_OFFSET]; 
    assign wrch_din[BID_OFFSET-1:BRESP_OFFSET]   = M_AXI_BRESP;
  end endgenerate // axi_wrch_output

  generate if ((IS_AXI_FULL_WRCH == 1 || (IS_AXI_FULL == 1 && C_WRCH_TYPE == 1)) && C_HAS_AXI_BUSER == 1) begin : axi_buser
    assign S_AXI_BUSER = wrch_dout[BRESP_OFFSET-1:BUSER_OFFSET];
  end endgenerate // axi_buser

  generate if ((IS_AXI_FULL_WRCH == 1 || (IS_AXI_FULL == 1 && C_WRCH_TYPE == 1)) && C_HAS_AXI_BUSER == 0) begin : naxi_buser
    assign S_AXI_BUSER = 0;
  end endgenerate // naxi_buser

  generate if ((IS_AXI_FULL_WRCH == 1 || (IS_AXI_FULL == 1 && C_WRCH_TYPE == 1)) && C_HAS_AXI_ID == 1) begin : axi_bid
    assign S_AXI_BID   =  wrch_dout[C_DIN_WIDTH_WRCH-1:BID_OFFSET];
  end endgenerate // axi_bid
  
  generate if ((IS_AXI_FULL_WRCH == 1 || (IS_AXI_FULL == 1 && C_WRCH_TYPE == 1)) && C_HAS_AXI_ID == 0) begin : naxi_bid
    assign S_AXI_BID   =  0 ;
  end endgenerate // naxi_bid  


  generate if (IS_AXI_LITE_WACH == 1 || (IS_AXI_LITE == 1 && C_WACH_TYPE == 1)) begin : axi_wach_output1
    assign wach_din        = {S_AXI_AWADDR, S_AXI_AWPROT};
    assign M_AXI_AWADDR    = wach_dout[C_DIN_WIDTH_WACH-1:AWADDR_OFFSET];    
    assign M_AXI_AWPROT    = wach_dout[AWADDR_OFFSET-1:AWPROT_OFFSET];    
  end endgenerate // axi_wach_output1

  generate if (IS_AXI_LITE_WDCH == 1 || (IS_AXI_LITE == 1 && C_WDCH_TYPE == 1)) begin : axi_wdch_output1
    assign wdch_din        = {S_AXI_WDATA, S_AXI_WSTRB};
    assign M_AXI_WDATA     = wdch_dout[C_DIN_WIDTH_WDCH-1:WDATA_OFFSET];
    assign M_AXI_WSTRB     = wdch_dout[WDATA_OFFSET-1:WSTRB_OFFSET];
  end endgenerate // axi_wdch_output1

  generate if (IS_AXI_LITE_WRCH == 1 || (IS_AXI_LITE == 1 && C_WRCH_TYPE == 1)) begin : axi_wrch_output1
    assign wrch_din        = M_AXI_BRESP;
    assign S_AXI_BRESP     = wrch_dout[C_DIN_WIDTH_WRCH-1:BRESP_OFFSET]; 
  end endgenerate // axi_wrch_output1

  generate if ((IS_AXI_FULL_WACH == 1 || (IS_AXI_FULL == 1 && C_WACH_TYPE == 1)) && C_HAS_AXI_AWUSER == 1) begin : gwach_din1
    assign wach_din[AWREGION_OFFSET-1:AWUSER_OFFSET]     = S_AXI_AWUSER;
  end endgenerate // gwach_din1

  generate if ((IS_AXI_FULL_WACH == 1 || (IS_AXI_FULL == 1 && C_WACH_TYPE == 1)) && C_HAS_AXI_ID == 1) begin : gwach_din2
    assign wach_din[C_DIN_WIDTH_WACH-1:AWID_OFFSET]     = S_AXI_AWID;
  end endgenerate // gwach_din2

  generate if ((IS_AXI_FULL_WACH == 1 || (IS_AXI_FULL == 1 && C_WACH_TYPE == 1)) && C_AXI_TYPE == 1) begin : gwach_din3
    assign wach_din[AWQOS_OFFSET-1:AWREGION_OFFSET]     = S_AXI_AWREGION;
  end endgenerate // gwach_din3

  generate if ((IS_AXI_FULL_WDCH == 1 || (IS_AXI_FULL == 1 && C_WDCH_TYPE == 1)) && C_HAS_AXI_WUSER == 1) begin : gwdch_din1
    assign wdch_din[WSTRB_OFFSET-1:WUSER_OFFSET] = S_AXI_WUSER;
  end endgenerate // gwdch_din1

  generate if ((IS_AXI_FULL_WDCH == 1 || (IS_AXI_FULL == 1 && C_WDCH_TYPE == 1)) && C_HAS_AXI_ID == 1 && C_AXI_TYPE == 3) begin : gwdch_din2
    assign wdch_din[C_DIN_WIDTH_WDCH-1:WID_OFFSET] = S_AXI_WID;
  end endgenerate // gwdch_din2

  generate if ((IS_AXI_FULL_WRCH == 1 || (IS_AXI_FULL == 1 && C_WRCH_TYPE == 1)) && C_HAS_AXI_BUSER == 1) begin : gwrch_din1
    assign wrch_din[BRESP_OFFSET-1:BUSER_OFFSET]    = M_AXI_BUSER;
  end endgenerate // gwrch_din1

  generate if ((IS_AXI_FULL_WRCH == 1 || (IS_AXI_FULL == 1 && C_WRCH_TYPE == 1)) && C_HAS_AXI_ID == 1) begin : gwrch_din2
    assign wrch_din[C_DIN_WIDTH_WRCH-1:BID_OFFSET]    = M_AXI_BID;
  end endgenerate // gwrch_din2

  //end of  axi_write_channel

  //###########################################################################
  //  AXI FULL Read Channel (axi_read_channel)
  //###########################################################################
  wire [C_DIN_WIDTH_RACH-1:0]        rach_din            ;
  wire [C_DIN_WIDTH_RACH-1:0]        rach_dout           ;
  wire [C_DIN_WIDTH_RACH-1:0]        rach_dout_pkt       ;
  wire                               rach_full           ;
  wire                               rach_almost_full    ;
  wire                               rach_prog_full      ;
  wire                               rach_empty          ;
  wire                               rach_almost_empty   ;
  wire                               rach_prog_empty     ;
  wire [C_DIN_WIDTH_RDCH-1:0]        rdch_din            ;
  wire [C_DIN_WIDTH_RDCH-1:0]        rdch_dout           ;
  wire                               rdch_full           ;
  wire                               rdch_almost_full    ;
  wire                               rdch_prog_full      ;
  wire                               rdch_empty          ;
  wire                               rdch_almost_empty   ;
  wire                               rdch_prog_empty     ;
  wire                               axi_ar_underflow_i  ;
  wire                               axi_r_underflow_i   ;
  wire                               axi_ar_overflow_i   ;
  wire                               axi_r_overflow_i    ;
  wire                               axi_rd_underflow_i  ;
  wire                               axi_rd_overflow_i   ;
  wire                               rach_s_axi_arready  ;
  wire                               rach_m_axi_arvalid  ;
  wire                               rach_wr_en          ;
  wire                               rach_rd_en          ;
  wire                               rdch_m_axi_rready   ;
  wire                               rdch_s_axi_rvalid   ;
  wire                               rdch_wr_en          ;
  wire                               rdch_rd_en          ;
  wire                               arvalid_pkt         ;
  wire                               arready_pkt         ;
  wire                               arvalid_en          ;
  wire                               rdch_rd_ok          ;
  wire                               accept_next_pkt     ;
  integer                            rdch_free_space     ;
  integer                            rdch_commited_space ;
  wire                               rach_we             ;
  wire                               rach_re             ;
  wire                               rdch_we             ;
  wire                               rdch_re             ;

  localparam ARID_OFFSET       = (C_AXI_TYPE != 2 && C_HAS_AXI_ID == 1) ? C_DIN_WIDTH_RACH - C_AXI_ID_WIDTH : C_DIN_WIDTH_RACH;
  localparam ARADDR_OFFSET     = ARID_OFFSET - C_AXI_ADDR_WIDTH;
  localparam ARLEN_OFFSET      = C_AXI_TYPE != 2 ? ARADDR_OFFSET - C_AXI_LEN_WIDTH : ARADDR_OFFSET;
  localparam ARSIZE_OFFSET     = C_AXI_TYPE != 2 ? ARLEN_OFFSET - C_AXI_SIZE_WIDTH : ARLEN_OFFSET;
  localparam ARBURST_OFFSET    = C_AXI_TYPE != 2 ? ARSIZE_OFFSET - C_AXI_BURST_WIDTH : ARSIZE_OFFSET;
  localparam ARLOCK_OFFSET     = C_AXI_TYPE != 2 ? ARBURST_OFFSET - C_AXI_LOCK_WIDTH : ARBURST_OFFSET;
  localparam ARCACHE_OFFSET    = C_AXI_TYPE != 2 ? ARLOCK_OFFSET - C_AXI_CACHE_WIDTH : ARLOCK_OFFSET;
  localparam ARPROT_OFFSET     = ARCACHE_OFFSET - C_AXI_PROT_WIDTH;
  localparam ARQOS_OFFSET      = ARPROT_OFFSET - C_AXI_QOS_WIDTH;
  localparam ARREGION_OFFSET   = C_AXI_TYPE == 1 ? ARQOS_OFFSET - C_AXI_REGION_WIDTH : ARQOS_OFFSET;
  localparam ARUSER_OFFSET     = C_HAS_AXI_ARUSER == 1 ? ARREGION_OFFSET-C_AXI_ARUSER_WIDTH : ARREGION_OFFSET;

  localparam RID_OFFSET        = (C_AXI_TYPE != 2 && C_HAS_AXI_ID == 1) ? C_DIN_WIDTH_RDCH - C_AXI_ID_WIDTH : C_DIN_WIDTH_RDCH;
  localparam RDATA_OFFSET      = RID_OFFSET - C_AXI_DATA_WIDTH;
  localparam RRESP_OFFSET      = RDATA_OFFSET - C_AXI_RRESP_WIDTH;
  localparam RUSER_OFFSET      = C_HAS_AXI_RUSER == 1 ? RRESP_OFFSET-C_AXI_RUSER_WIDTH : RRESP_OFFSET;


  generate if (IS_RD_ADDR_CH == 1) begin : axi_read_addr_channel

    // Write protection when almost full or prog_full is high
    assign rach_we    = (C_PROG_FULL_TYPE_RACH != 0) ? rach_s_axi_arready & S_AXI_ARVALID : S_AXI_ARVALID;

    // Read protection when almost empty or prog_empty is high
//    assign rach_rd_en = (C_PROG_EMPTY_TYPE_RACH != 5) ? rach_m_axi_arvalid & M_AXI_ARREADY : M_AXI_ARREADY && arvalid_en;
    assign rach_re    = (C_PROG_EMPTY_TYPE_RACH != 0 && C_APPLICATION_TYPE_RACH == 1) ? 
                        rach_m_axi_arvalid & arready_pkt & arvalid_en : 
                        (C_PROG_EMPTY_TYPE_RACH != 0 && C_APPLICATION_TYPE_RACH != 1) ? 
                        M_AXI_ARREADY && rach_m_axi_arvalid :
                        (C_PROG_EMPTY_TYPE_RACH == 0 && C_APPLICATION_TYPE_RACH == 1) ? 
                        arready_pkt & arvalid_en : 
                        (C_PROG_EMPTY_TYPE_RACH == 0 && C_APPLICATION_TYPE_RACH != 1) ? 
                        M_AXI_ARREADY : 1'b0;
    assign rach_wr_en = (C_HAS_SLAVE_CE == 1)  ? rach_we & S_ACLK_EN : rach_we;
    assign rach_rd_en = (C_HAS_MASTER_CE == 1) ? rach_re & M_ACLK_EN : rach_re;


    fifo_generator_v13_1_2_CONV_VER
      #(
        .C_FAMILY			(C_FAMILY),
        .C_COMMON_CLOCK                 (C_COMMON_CLOCK),
        .C_MEMORY_TYPE			((C_IMPLEMENTATION_TYPE_RACH == 1  || C_IMPLEMENTATION_TYPE_RACH == 11) ? 1 :
                                         (C_IMPLEMENTATION_TYPE_RACH == 2  || C_IMPLEMENTATION_TYPE_RACH == 12) ? 2 : 4),
        .C_IMPLEMENTATION_TYPE		((C_IMPLEMENTATION_TYPE_RACH == 1  || C_IMPLEMENTATION_TYPE_RACH == 2) ? 0 :
                                         (C_IMPLEMENTATION_TYPE_RACH == 11 || C_IMPLEMENTATION_TYPE_RACH == 12) ? 2 : 6),
        .C_PRELOAD_REGS			(1), // always FWFT for AXI
        .C_PRELOAD_LATENCY		(0), // always FWFT for AXI
        .C_DIN_WIDTH			(C_DIN_WIDTH_RACH),
        .C_WR_DEPTH			(C_WR_DEPTH_RACH),
        .C_WR_PNTR_WIDTH		(C_WR_PNTR_WIDTH_RACH),
        .C_INTERFACE_TYPE 		(C_INTERFACE_TYPE),
        .C_DOUT_WIDTH			(C_DIN_WIDTH_RACH),
        .C_RD_DEPTH			(C_WR_DEPTH_RACH),
        .C_RD_PNTR_WIDTH		(C_WR_PNTR_WIDTH_RACH),
        .C_PROG_FULL_TYPE		(C_PROG_FULL_TYPE_RACH),
        .C_PROG_FULL_THRESH_ASSERT_VAL	(C_PROG_FULL_THRESH_ASSERT_VAL_RACH),
        .C_PROG_EMPTY_TYPE		(C_PROG_EMPTY_TYPE_RACH),
        .C_PROG_EMPTY_THRESH_ASSERT_VAL	(C_PROG_EMPTY_THRESH_ASSERT_VAL_RACH),
        .C_USE_ECC                      (C_USE_ECC_RACH),
        .C_ERROR_INJECTION_TYPE         (C_ERROR_INJECTION_TYPE_RACH),
        .C_HAS_ALMOST_EMPTY		(0),
        .C_HAS_ALMOST_FULL		(0),
        .C_AXI_TYPE                     (C_INTERFACE_TYPE == 1 ? 0 : C_AXI_TYPE),

        .C_FIFO_TYPE                    ((C_APPLICATION_TYPE_RACH == 1)?0:C_APPLICATION_TYPE_RACH),
        .C_SYNCHRONIZER_STAGE           (C_SYNCHRONIZER_STAGE),

        .C_HAS_WR_RST			(0),
        .C_HAS_RD_RST			(0),
        .C_HAS_RST			(1),
        .C_HAS_SRST			(0),
        .C_DOUT_RST_VAL			(0),

        .C_HAS_VALID			(0),
        .C_VALID_LOW			(C_VALID_LOW),
        .C_HAS_UNDERFLOW		(C_HAS_UNDERFLOW),
        .C_UNDERFLOW_LOW		(C_UNDERFLOW_LOW),
        .C_HAS_WR_ACK			(0),
        .C_WR_ACK_LOW			(C_WR_ACK_LOW),
        .C_HAS_OVERFLOW			(C_HAS_OVERFLOW),
        .C_OVERFLOW_LOW			(C_OVERFLOW_LOW),

        .C_HAS_DATA_COUNT		((C_COMMON_CLOCK == 1 && C_HAS_DATA_COUNTS_RACH == 1) ? 1 : 0),
        .C_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_RACH + 1),
        .C_HAS_RD_DATA_COUNT		((C_COMMON_CLOCK == 0 && C_HAS_DATA_COUNTS_RACH == 1) ? 1 : 0),
        .C_RD_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_RACH + 1),
        .C_USE_FWFT_DATA_COUNT		(1), // use extra logic is always true
        .C_HAS_WR_DATA_COUNT		((C_COMMON_CLOCK == 0 && C_HAS_DATA_COUNTS_RACH == 1) ? 1 : 0),
        .C_WR_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_RACH + 1),
        .C_FULL_FLAGS_RST_VAL           (1),
        .C_USE_EMBEDDED_REG		(0),
        .C_USE_DOUT_RST                 (0),
        .C_MSGON_VAL                    (C_MSGON_VAL),
        .C_ENABLE_RST_SYNC              (1),
        .C_EN_SAFETY_CKT                ((C_IMPLEMENTATION_TYPE_RACH == 1 || C_IMPLEMENTATION_TYPE_RACH == 11) ? 1 : 0),
        .C_COUNT_TYPE			(C_COUNT_TYPE),
        .C_DEFAULT_VALUE		(C_DEFAULT_VALUE),
        .C_ENABLE_RLOCS			(C_ENABLE_RLOCS),
        .C_HAS_BACKUP			(C_HAS_BACKUP),
        .C_HAS_INT_CLK                  (C_HAS_INT_CLK),
        .C_MIF_FILE_NAME		(C_MIF_FILE_NAME),
        .C_HAS_MEMINIT_FILE		(C_HAS_MEMINIT_FILE),
        .C_INIT_WR_PNTR_VAL		(C_INIT_WR_PNTR_VAL),
        .C_OPTIMIZATION_MODE		(C_OPTIMIZATION_MODE),
        .C_PRIM_FIFO_TYPE		(C_PRIM_FIFO_TYPE),
        .C_RD_FREQ			(C_RD_FREQ),
        .C_USE_FIFO16_FLAGS		(C_USE_FIFO16_FLAGS),
        .C_WR_FREQ			(C_WR_FREQ),
        .C_WR_RESPONSE_LATENCY		(C_WR_RESPONSE_LATENCY)
      )
    fifo_generator_v13_1_2_rach_dut
      (
        .CLK                      (S_ACLK),
        .WR_CLK                   (S_ACLK),
        .RD_CLK                   (M_ACLK),
        .RST                      (inverted_reset),
        .SRST                     (1'b0),
        .WR_RST                   (inverted_reset),
        .RD_RST                   (inverted_reset),
        .WR_EN                    (rach_wr_en),
        .RD_EN                    (rach_rd_en),
        .PROG_FULL_THRESH         (AXI_AR_PROG_FULL_THRESH),
        .PROG_FULL_THRESH_ASSERT  ({C_WR_PNTR_WIDTH_RACH{1'b0}}),
        .PROG_FULL_THRESH_NEGATE  ({C_WR_PNTR_WIDTH_RACH{1'b0}}),
        .PROG_EMPTY_THRESH        (AXI_AR_PROG_EMPTY_THRESH),
        .PROG_EMPTY_THRESH_ASSERT ({C_WR_PNTR_WIDTH_RACH{1'b0}}),
        .PROG_EMPTY_THRESH_NEGATE ({C_WR_PNTR_WIDTH_RACH{1'b0}}),
        .INJECTDBITERR            (AXI_AR_INJECTDBITERR), 
        .INJECTSBITERR            (AXI_AR_INJECTSBITERR),
  
        .DIN                      (rach_din),
        .DOUT                     (rach_dout_pkt),
        .FULL                     (rach_full),
        .EMPTY                    (rach_empty),
        .ALMOST_FULL              (),
        .ALMOST_EMPTY             (),
        .PROG_FULL                (AXI_AR_PROG_FULL),
        .PROG_EMPTY               (AXI_AR_PROG_EMPTY),
  
        .WR_ACK                   (),
        .OVERFLOW                 (axi_ar_overflow_i),
        .VALID                    (),
        .UNDERFLOW                (axi_ar_underflow_i),
        .DATA_COUNT               (AXI_AR_DATA_COUNT),
        .RD_DATA_COUNT            (AXI_AR_RD_DATA_COUNT),
        .WR_DATA_COUNT            (AXI_AR_WR_DATA_COUNT),
        .SBITERR                  (AXI_AR_SBITERR),
        .DBITERR                  (AXI_AR_DBITERR),
        .wr_rst_busy              (wr_rst_busy_rach),
        .rd_rst_busy              (rd_rst_busy_rach),
        .wr_rst_i_out             (),
        .rd_rst_i_out             (),
  
        .BACKUP                   (BACKUP),
        .BACKUP_MARKER            (BACKUP_MARKER),
        .INT_CLK                  (INT_CLK)
       );

    assign rach_s_axi_arready    = (IS_8SERIES == 0) ? ~rach_full : (C_IMPLEMENTATION_TYPE_RACH == 5 || C_IMPLEMENTATION_TYPE_RACH == 13) ? ~(rach_full | wr_rst_busy_rach) : ~rach_full;
    assign rach_m_axi_arvalid = ~rach_empty;
    assign S_AXI_ARREADY      = rach_s_axi_arready;

    assign AXI_AR_UNDERFLOW  = C_USE_COMMON_UNDERFLOW == 0 ? axi_ar_underflow_i : 0;
    assign AXI_AR_OVERFLOW   = C_USE_COMMON_OVERFLOW  == 0 ? axi_ar_overflow_i  : 0;

  end endgenerate // axi_read_addr_channel

  // Register Slice for Read Address Channel
  generate if (C_RACH_TYPE == 1) begin : grach_reg_slice

    fifo_generator_v13_1_2_axic_reg_slice
          #(
            .C_FAMILY                (C_FAMILY),
            .C_DATA_WIDTH            (C_DIN_WIDTH_RACH),
            .C_REG_CONFIG            (C_REG_SLICE_MODE_RACH)
            )
    rach_reg_slice_inst
        (
          // System Signals
          .ACLK                      (S_ACLK),
          .ARESET                    (axi_rs_rst),

          // Slave side
          .S_PAYLOAD_DATA            (rach_din),
          .S_VALID                   (S_AXI_ARVALID),
          .S_READY                   (S_AXI_ARREADY),

          // Master side
          .M_PAYLOAD_DATA            (rach_dout),
          .M_VALID                   (M_AXI_ARVALID),
          .M_READY                   (M_AXI_ARREADY)
          );
  end endgenerate // grach_reg_slice

  // Register Slice for Read Address Channel for MM Packet FIFO
  generate if (C_RACH_TYPE == 0 && C_APPLICATION_TYPE_RACH == 1) begin : grach_reg_slice_mm_pkt_fifo

    fifo_generator_v13_1_2_axic_reg_slice
          #(
            .C_FAMILY                (C_FAMILY),
            .C_DATA_WIDTH            (C_DIN_WIDTH_RACH),
            .C_REG_CONFIG            (1)
            )
    reg_slice_mm_pkt_fifo_inst
        (
          // System Signals
          .ACLK                      (S_ACLK),
          .ARESET                    (inverted_reset),

          // Slave side
          .S_PAYLOAD_DATA            (rach_dout_pkt),
          .S_VALID                   (arvalid_pkt),
          .S_READY                   (arready_pkt),

          // Master side
          .M_PAYLOAD_DATA            (rach_dout),
          .M_VALID                   (M_AXI_ARVALID),
          .M_READY                   (M_AXI_ARREADY)
          );
  end endgenerate // grach_reg_slice_mm_pkt_fifo

  
  generate if (C_RACH_TYPE == 0 && C_APPLICATION_TYPE_RACH != 1) begin : grach_m_axi_arvalid
    assign M_AXI_ARVALID      = rach_m_axi_arvalid;
    assign rach_dout          = rach_dout_pkt;
  end endgenerate // grach_m_axi_arvalid
  
  
  generate if (C_APPLICATION_TYPE_RACH == 1 && C_HAS_AXI_RD_CHANNEL == 1) begin : axi_mm_pkt_fifo_rd
    assign rdch_rd_ok = rdch_s_axi_rvalid && rdch_rd_en;
    assign arvalid_pkt = rach_m_axi_arvalid && arvalid_en;
    assign accept_next_pkt  = rach_m_axi_arvalid && arready_pkt && arvalid_en;

    always@(posedge S_ACLK or posedge inverted_reset) begin
      if(inverted_reset) begin
	rdch_commited_space <= 0;
      end else begin
	if(rdch_rd_ok && !accept_next_pkt) begin
	  rdch_commited_space <= rdch_commited_space-1;
	end else if(!rdch_rd_ok && accept_next_pkt) begin
	  rdch_commited_space <= rdch_commited_space+(rach_dout_pkt[ARADDR_OFFSET-1:ARLEN_OFFSET]+1);
	end else if(rdch_rd_ok && accept_next_pkt) begin
	  rdch_commited_space <= rdch_commited_space+(rach_dout_pkt[ARADDR_OFFSET-1:ARLEN_OFFSET]);
	end
      end
    end //Always end

    always@(*) begin
      rdch_free_space <= (C_WR_DEPTH_RDCH-(rdch_commited_space+rach_dout_pkt[ARADDR_OFFSET-1:ARLEN_OFFSET]+1));
    end

    assign arvalid_en = (rdch_free_space >= 0)?1:0;
  end
  endgenerate
  
  generate if (C_APPLICATION_TYPE_RACH != 1) begin : axi_mm_fifo_rd
    assign arvalid_en = 1;    
  end
  endgenerate

  generate if (IS_RD_DATA_CH == 1) begin : axi_read_data_channel

    // Write protection when almost full or prog_full is high
    assign rdch_we    = (C_PROG_FULL_TYPE_RDCH != 0) ? rdch_m_axi_rready  & M_AXI_RVALID : M_AXI_RVALID;

    // Read protection when almost empty or prog_empty is high
    assign rdch_re    = (C_PROG_EMPTY_TYPE_RDCH != 0) ? rdch_s_axi_rvalid  & S_AXI_RREADY : S_AXI_RREADY;
    assign rdch_wr_en = (C_HAS_MASTER_CE == 1)  ? rdch_we & M_ACLK_EN : rdch_we;
    assign rdch_rd_en = (C_HAS_SLAVE_CE == 1) ? rdch_re & S_ACLK_EN : rdch_re;

    fifo_generator_v13_1_2_CONV_VER
      #(
        .C_FAMILY			(C_FAMILY),
        .C_COMMON_CLOCK                 (C_COMMON_CLOCK),
        .C_MEMORY_TYPE			((C_IMPLEMENTATION_TYPE_RDCH == 1  || C_IMPLEMENTATION_TYPE_RDCH == 11) ? 1 :
                                         (C_IMPLEMENTATION_TYPE_RDCH == 2  || C_IMPLEMENTATION_TYPE_RDCH == 12) ? 2 : 4),
        .C_IMPLEMENTATION_TYPE		((C_IMPLEMENTATION_TYPE_RDCH == 1  || C_IMPLEMENTATION_TYPE_RDCH == 2) ? 0 :
                                         (C_IMPLEMENTATION_TYPE_RDCH == 11 || C_IMPLEMENTATION_TYPE_RDCH == 12) ? 2 : 6),
        .C_PRELOAD_REGS			(1), // always FWFT for AXI
        .C_PRELOAD_LATENCY		(0), // always FWFT for AXI
        .C_DIN_WIDTH			(C_DIN_WIDTH_RDCH),
        .C_WR_DEPTH			(C_WR_DEPTH_RDCH),
        .C_WR_PNTR_WIDTH		(C_WR_PNTR_WIDTH_RDCH),
        .C_DOUT_WIDTH			(C_DIN_WIDTH_RDCH),
        .C_RD_DEPTH			(C_WR_DEPTH_RDCH),
        .C_INTERFACE_TYPE 		(C_INTERFACE_TYPE),
        .C_RD_PNTR_WIDTH		(C_WR_PNTR_WIDTH_RDCH),
        .C_PROG_FULL_TYPE		(C_PROG_FULL_TYPE_RDCH),
        .C_PROG_FULL_THRESH_ASSERT_VAL	(C_PROG_FULL_THRESH_ASSERT_VAL_RDCH),
        .C_PROG_EMPTY_TYPE		(C_PROG_EMPTY_TYPE_RDCH),
        .C_PROG_EMPTY_THRESH_ASSERT_VAL	(C_PROG_EMPTY_THRESH_ASSERT_VAL_RDCH),
        .C_USE_ECC                      (C_USE_ECC_RDCH),
        .C_ERROR_INJECTION_TYPE         (C_ERROR_INJECTION_TYPE_RDCH),
        .C_HAS_ALMOST_EMPTY		(0),
        .C_HAS_ALMOST_FULL		(0),
        .C_AXI_TYPE                     (C_INTERFACE_TYPE == 1 ? 0 : C_AXI_TYPE),

        .C_FIFO_TYPE                    (C_APPLICATION_TYPE_RDCH),
        .C_SYNCHRONIZER_STAGE           (C_SYNCHRONIZER_STAGE),

        .C_HAS_WR_RST			(0),
        .C_HAS_RD_RST			(0),
        .C_HAS_RST			(1),
        .C_HAS_SRST			(0),
        .C_DOUT_RST_VAL			(0),

        .C_HAS_VALID			(0),
        .C_VALID_LOW			(C_VALID_LOW),
        .C_HAS_UNDERFLOW		(C_HAS_UNDERFLOW),
        .C_UNDERFLOW_LOW		(C_UNDERFLOW_LOW),
        .C_HAS_WR_ACK			(0),
        .C_WR_ACK_LOW			(C_WR_ACK_LOW),
        .C_HAS_OVERFLOW			(C_HAS_OVERFLOW),
        .C_OVERFLOW_LOW			(C_OVERFLOW_LOW),

        .C_HAS_DATA_COUNT		((C_COMMON_CLOCK == 1 && C_HAS_DATA_COUNTS_RDCH == 1) ? 1 : 0),
        .C_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_RDCH + 1),
        .C_HAS_RD_DATA_COUNT		((C_COMMON_CLOCK == 0 && C_HAS_DATA_COUNTS_RDCH == 1) ? 1 : 0),
        .C_RD_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_RDCH + 1),
        .C_USE_FWFT_DATA_COUNT		(1), // use extra logic is always true
        .C_HAS_WR_DATA_COUNT		((C_COMMON_CLOCK == 0 && C_HAS_DATA_COUNTS_RDCH == 1) ? 1 : 0),
        .C_WR_DATA_COUNT_WIDTH		(C_WR_PNTR_WIDTH_RDCH + 1),
        .C_FULL_FLAGS_RST_VAL           (1),
        .C_USE_EMBEDDED_REG		(0),
        .C_USE_DOUT_RST                 (0),
        .C_MSGON_VAL                    (C_MSGON_VAL),
        .C_ENABLE_RST_SYNC              (1),
        .C_EN_SAFETY_CKT                ((C_IMPLEMENTATION_TYPE_RDCH == 1 || C_IMPLEMENTATION_TYPE_RDCH == 11) ? 1 : 0),
        .C_COUNT_TYPE			(C_COUNT_TYPE),
        .C_DEFAULT_VALUE		(C_DEFAULT_VALUE),
        .C_ENABLE_RLOCS			(C_ENABLE_RLOCS),
        .C_HAS_BACKUP			(C_HAS_BACKUP),
        .C_HAS_INT_CLK                  (C_HAS_INT_CLK),
        .C_MIF_FILE_NAME		(C_MIF_FILE_NAME),
        .C_HAS_MEMINIT_FILE		(C_HAS_MEMINIT_FILE),
        .C_INIT_WR_PNTR_VAL		(C_INIT_WR_PNTR_VAL),
        .C_OPTIMIZATION_MODE		(C_OPTIMIZATION_MODE),
        .C_PRIM_FIFO_TYPE		(C_PRIM_FIFO_TYPE),
        .C_RD_FREQ			(C_RD_FREQ),
        .C_USE_FIFO16_FLAGS		(C_USE_FIFO16_FLAGS),
        .C_WR_FREQ			(C_WR_FREQ),
        .C_WR_RESPONSE_LATENCY		(C_WR_RESPONSE_LATENCY)
      )
    fifo_generator_v13_1_2_rdch_dut
      (
        .CLK                      (S_ACLK),
        .WR_CLK                   (M_ACLK),
        .RD_CLK                   (S_ACLK),
        .RST                      (inverted_reset),
        .SRST                     (1'b0),
        .WR_RST                   (inverted_reset),
        .RD_RST                   (inverted_reset),
        .WR_EN                    (rdch_wr_en),
        .RD_EN                    (rdch_rd_en),
        .PROG_FULL_THRESH         (AXI_R_PROG_FULL_THRESH),
        .PROG_FULL_THRESH_ASSERT  ({C_WR_PNTR_WIDTH_RDCH{1'b0}}),
        .PROG_FULL_THRESH_NEGATE  ({C_WR_PNTR_WIDTH_RDCH{1'b0}}),
        .PROG_EMPTY_THRESH        (AXI_R_PROG_EMPTY_THRESH),
        .PROG_EMPTY_THRESH_ASSERT ({C_WR_PNTR_WIDTH_RDCH{1'b0}}),
        .PROG_EMPTY_THRESH_NEGATE ({C_WR_PNTR_WIDTH_RDCH{1'b0}}),
        .INJECTDBITERR            (AXI_R_INJECTDBITERR), 
        .INJECTSBITERR            (AXI_R_INJECTSBITERR),
  
        .DIN                      (rdch_din),
        .DOUT                     (rdch_dout),
        .FULL                     (rdch_full),
        .EMPTY                    (rdch_empty),
        .ALMOST_FULL              (),
        .ALMOST_EMPTY             (),
        .PROG_FULL                (AXI_R_PROG_FULL),
        .PROG_EMPTY               (AXI_R_PROG_EMPTY),
  
        .WR_ACK                   (),
        .OVERFLOW                 (axi_r_overflow_i),
        .VALID                    (),
        .UNDERFLOW                (axi_r_underflow_i),
        .DATA_COUNT               (AXI_R_DATA_COUNT),
        .RD_DATA_COUNT            (AXI_R_RD_DATA_COUNT),
        .WR_DATA_COUNT            (AXI_R_WR_DATA_COUNT),
        .SBITERR                  (AXI_R_SBITERR),
        .DBITERR                  (AXI_R_DBITERR),
        .wr_rst_busy              (wr_rst_busy_rdch),
        .rd_rst_busy              (rd_rst_busy_rdch),
        .wr_rst_i_out             (),
        .rd_rst_i_out             (),
  
        .BACKUP                   (BACKUP),
        .BACKUP_MARKER            (BACKUP_MARKER),
        .INT_CLK                  (INT_CLK)
       );

    assign rdch_s_axi_rvalid = ~rdch_empty;
    assign rdch_m_axi_rready     = (IS_8SERIES == 0) ? ~rdch_full : (C_IMPLEMENTATION_TYPE_RDCH == 5 || C_IMPLEMENTATION_TYPE_RDCH == 13) ? ~(rdch_full | wr_rst_busy_rdch) : ~rdch_full;
    assign S_AXI_RVALID      = rdch_s_axi_rvalid;
    assign M_AXI_RREADY      = rdch_m_axi_rready;

    assign AXI_R_UNDERFLOW   = C_USE_COMMON_UNDERFLOW == 0 ? axi_r_underflow_i  : 0;
    assign AXI_R_OVERFLOW    = C_USE_COMMON_OVERFLOW  == 0 ? axi_r_overflow_i   : 0;

  end endgenerate //axi_read_data_channel

  // Register Slice for read Data Channel
  generate if (C_RDCH_TYPE == 1) begin : grdch_reg_slice

    fifo_generator_v13_1_2_axic_reg_slice
          #(
            .C_FAMILY                (C_FAMILY),
            .C_DATA_WIDTH            (C_DIN_WIDTH_RDCH),
            .C_REG_CONFIG            (C_REG_SLICE_MODE_RDCH)
            )
    rdch_reg_slice_inst
        (
          // System Signals
          .ACLK                      (S_ACLK),
          .ARESET                    (axi_rs_rst),

          // Slave side
          .S_PAYLOAD_DATA            (rdch_din),
          .S_VALID                   (M_AXI_RVALID),
          .S_READY                   (M_AXI_RREADY),

          // Master side
          .M_PAYLOAD_DATA            (rdch_dout),
          .M_VALID                   (S_AXI_RVALID),
          .M_READY                   (S_AXI_RREADY)
          );
  end endgenerate // grdch_reg_slice


    assign axi_rd_underflow_i = C_USE_COMMON_UNDERFLOW == 1 ? (axi_ar_underflow_i || axi_r_underflow_i) : 0;
    assign axi_rd_overflow_i  = C_USE_COMMON_OVERFLOW  == 1 ? (axi_ar_overflow_i  || axi_r_overflow_i) : 0;


  generate if (IS_AXI_FULL_RACH == 1 || (IS_AXI_FULL == 1 && C_RACH_TYPE == 1)) begin : axi_full_rach_output
    assign M_AXI_ARADDR    = rach_dout[ARID_OFFSET-1:ARADDR_OFFSET];    
    assign M_AXI_ARLEN     = rach_dout[ARADDR_OFFSET-1:ARLEN_OFFSET];    
    assign M_AXI_ARSIZE    = rach_dout[ARLEN_OFFSET-1:ARSIZE_OFFSET];    
    assign M_AXI_ARBURST   = rach_dout[ARSIZE_OFFSET-1:ARBURST_OFFSET];    
    assign M_AXI_ARLOCK    = rach_dout[ARBURST_OFFSET-1:ARLOCK_OFFSET];    
    assign M_AXI_ARCACHE   = rach_dout[ARLOCK_OFFSET-1:ARCACHE_OFFSET];    
    assign M_AXI_ARPROT    = rach_dout[ARCACHE_OFFSET-1:ARPROT_OFFSET];    
    assign M_AXI_ARQOS     = rach_dout[ARPROT_OFFSET-1:ARQOS_OFFSET];    
    assign rach_din[ARID_OFFSET-1:ARADDR_OFFSET]    = S_AXI_ARADDR;
    assign rach_din[ARADDR_OFFSET-1:ARLEN_OFFSET]   = S_AXI_ARLEN;
    assign rach_din[ARLEN_OFFSET-1:ARSIZE_OFFSET]   = S_AXI_ARSIZE;
    assign rach_din[ARSIZE_OFFSET-1:ARBURST_OFFSET] = S_AXI_ARBURST;
    assign rach_din[ARBURST_OFFSET-1:ARLOCK_OFFSET] = S_AXI_ARLOCK;
    assign rach_din[ARLOCK_OFFSET-1:ARCACHE_OFFSET] = S_AXI_ARCACHE;
    assign rach_din[ARCACHE_OFFSET-1:ARPROT_OFFSET] = S_AXI_ARPROT;
    assign rach_din[ARPROT_OFFSET-1:ARQOS_OFFSET]   = S_AXI_ARQOS;
  end endgenerate // axi_full_rach_output

  generate if ((IS_AXI_FULL_RACH == 1 || (IS_AXI_FULL == 1 && C_RACH_TYPE == 1)) && C_AXI_TYPE == 1) begin : axi_arregion
    assign M_AXI_ARREGION  = rach_dout[ARQOS_OFFSET-1:ARREGION_OFFSET];    
  end endgenerate // axi_arregion

  generate if ((IS_AXI_FULL_RACH == 1 || (IS_AXI_FULL == 1 && C_RACH_TYPE == 1)) && C_AXI_TYPE != 1) begin : naxi_arregion
    assign M_AXI_ARREGION  = 0;    
  end endgenerate // naxi_arregion

  generate if ((IS_AXI_FULL_RACH == 1 || (IS_AXI_FULL == 1 && C_RACH_TYPE == 1)) && C_HAS_AXI_ARUSER == 1) begin : axi_aruser
    assign M_AXI_ARUSER = rach_dout[ARREGION_OFFSET-1:ARUSER_OFFSET];    
  end endgenerate // axi_aruser

  generate if ((IS_AXI_FULL_RACH == 1 || (IS_AXI_FULL == 1 && C_RACH_TYPE == 1)) && C_HAS_AXI_ARUSER == 0) begin : naxi_aruser
    assign M_AXI_ARUSER = 0;    
  end endgenerate // naxi_aruser

  generate if ((IS_AXI_FULL_RACH == 1 || (IS_AXI_FULL == 1 && C_RACH_TYPE == 1)) && C_HAS_AXI_ID == 1) begin : axi_arid
    assign M_AXI_ARID      = rach_dout[C_DIN_WIDTH_RACH-1:ARID_OFFSET];
  end endgenerate // axi_arid

  generate if ((IS_AXI_FULL_RACH == 1 || (IS_AXI_FULL == 1 && C_RACH_TYPE == 1)) && C_HAS_AXI_ID == 0) begin : naxi_arid
    assign M_AXI_ARID      = 0;
  end endgenerate // naxi_arid

  generate if (IS_AXI_FULL_RDCH == 1 || (IS_AXI_FULL == 1 && C_RDCH_TYPE == 1)) begin : axi_full_rdch_output
    assign S_AXI_RDATA     = rdch_dout[RID_OFFSET-1:RDATA_OFFSET];
    assign S_AXI_RRESP     = rdch_dout[RDATA_OFFSET-1:RRESP_OFFSET];
    assign S_AXI_RLAST     = rdch_dout[0];
    assign rdch_din[RID_OFFSET-1:RDATA_OFFSET]   = M_AXI_RDATA;
    assign rdch_din[RDATA_OFFSET-1:RRESP_OFFSET] = M_AXI_RRESP;
    assign rdch_din[0] = M_AXI_RLAST;
  end endgenerate // axi_full_rdch_output
  
  generate if ((IS_AXI_FULL_RDCH == 1 || (IS_AXI_FULL == 1 && C_RDCH_TYPE == 1)) && C_HAS_AXI_RUSER == 1) begin : axi_full_ruser_output
    assign S_AXI_RUSER     = rdch_dout[RRESP_OFFSET-1:RUSER_OFFSET];
  end endgenerate // axi_full_ruser_output

  generate if ((IS_AXI_FULL_RDCH == 1 || (IS_AXI_FULL == 1 && C_RDCH_TYPE == 1)) && C_HAS_AXI_RUSER == 0) begin : axi_full_nruser_output
    assign S_AXI_RUSER     =  0;
  end endgenerate // axi_full_nruser_output
  
  generate if ((IS_AXI_FULL_RDCH == 1 || (IS_AXI_FULL == 1 && C_RDCH_TYPE == 1)) && C_HAS_AXI_ID == 1) begin : axi_rid
    assign S_AXI_RID       = rdch_dout[C_DIN_WIDTH_RDCH-1:RID_OFFSET];
  end endgenerate // axi_rid

  generate if ((IS_AXI_FULL_RDCH == 1 || (IS_AXI_FULL == 1 && C_RDCH_TYPE == 1)) && C_HAS_AXI_ID == 0) begin : naxi_rid
    assign S_AXI_RID       = 0;
  end endgenerate // naxi_rid

  generate if (IS_AXI_LITE_RACH == 1 || (IS_AXI_LITE == 1 && C_RACH_TYPE == 1)) begin : axi_lite_rach_output1
    assign rach_din      = {S_AXI_ARADDR, S_AXI_ARPROT};
    assign M_AXI_ARADDR  = rach_dout[C_DIN_WIDTH_RACH-1:ARADDR_OFFSET];
    assign M_AXI_ARPROT  = rach_dout[ARADDR_OFFSET-1:ARPROT_OFFSET];
  end endgenerate // axi_lite_rach_output

  generate if (IS_AXI_LITE_RDCH == 1 || (IS_AXI_LITE == 1 && C_RDCH_TYPE == 1)) begin : axi_lite_rdch_output1
    assign rdch_din      = {M_AXI_RDATA, M_AXI_RRESP};
    assign S_AXI_RDATA   = rdch_dout[C_DIN_WIDTH_RDCH-1:RDATA_OFFSET];
    assign S_AXI_RRESP   = rdch_dout[RDATA_OFFSET-1:RRESP_OFFSET];
  end endgenerate // axi_lite_rdch_output

  generate if ((IS_AXI_FULL_RACH == 1 || (IS_AXI_FULL == 1 && C_RACH_TYPE == 1)) && C_HAS_AXI_ARUSER == 1) begin : grach_din1
    assign rach_din[ARREGION_OFFSET-1:ARUSER_OFFSET]     = S_AXI_ARUSER;
  end endgenerate // grach_din1

  generate if ((IS_AXI_FULL_RACH == 1 || (IS_AXI_FULL == 1 && C_RACH_TYPE == 1)) && C_HAS_AXI_ID == 1) begin : grach_din2
    assign rach_din[C_DIN_WIDTH_RACH-1:ARID_OFFSET]     = S_AXI_ARID;
  end endgenerate // grach_din2

  generate if ((IS_AXI_FULL_RACH == 1 || (IS_AXI_FULL == 1 && C_RACH_TYPE == 1)) && C_AXI_TYPE == 1) begin
    assign rach_din[ARQOS_OFFSET-1:ARREGION_OFFSET] = S_AXI_ARREGION;
  end endgenerate

  generate if ((IS_AXI_FULL_RDCH == 1 || (IS_AXI_FULL == 1 && C_RDCH_TYPE == 1)) && C_HAS_AXI_RUSER == 1) begin : grdch_din1
    assign rdch_din[RRESP_OFFSET-1:RUSER_OFFSET]     = M_AXI_RUSER;
  end endgenerate // grdch_din1

  generate if ((IS_AXI_FULL_RDCH == 1 || (IS_AXI_FULL == 1 && C_RDCH_TYPE == 1)) && C_HAS_AXI_ID == 1) begin : grdch_din2
    assign rdch_din[C_DIN_WIDTH_RDCH-1:RID_OFFSET] = M_AXI_RID;
  end endgenerate // grdch_din2

  //end of axi_read_channel

  generate if (C_INTERFACE_TYPE == 1 && C_USE_COMMON_UNDERFLOW == 1) begin : gaxi_comm_uf
    assign UNDERFLOW = (C_HAS_AXI_WR_CHANNEL == 1 && C_HAS_AXI_RD_CHANNEL == 1) ? (axi_wr_underflow_i || axi_rd_underflow_i) :
                       (C_HAS_AXI_WR_CHANNEL == 1 && C_HAS_AXI_RD_CHANNEL == 0) ? axi_wr_underflow_i :
                       (C_HAS_AXI_WR_CHANNEL == 0 && C_HAS_AXI_RD_CHANNEL == 1) ? axi_rd_underflow_i : 0;
  end endgenerate // gaxi_comm_uf

  generate if (C_INTERFACE_TYPE == 1 && C_USE_COMMON_OVERFLOW == 1) begin : gaxi_comm_of
    assign OVERFLOW = (C_HAS_AXI_WR_CHANNEL == 1 && C_HAS_AXI_RD_CHANNEL == 1) ? (axi_wr_overflow_i || axi_rd_overflow_i) :
                      (C_HAS_AXI_WR_CHANNEL == 1 && C_HAS_AXI_RD_CHANNEL == 0) ? axi_wr_overflow_i :
                      (C_HAS_AXI_WR_CHANNEL == 0 && C_HAS_AXI_RD_CHANNEL == 1) ? axi_rd_overflow_i : 0;
  end endgenerate // gaxi_comm_of
  
  //-------------------------------------------------------------------------
  //-------------------------------------------------------------------------
  //-------------------------------------------------------------------------
  // Pass Through Logic or Wiring Logic
  //-------------------------------------------------------------------------
  //-------------------------------------------------------------------------
  //-------------------------------------------------------------------------
  
  //-------------------------------------------------------------------------
  // Pass Through Logic for Read Channel
  //-------------------------------------------------------------------------

  // Wiring logic for Write Address Channel
  generate if (C_WACH_TYPE == 2) begin : gwach_pass_through
    assign M_AXI_AWID      = S_AXI_AWID;
    assign M_AXI_AWADDR    = S_AXI_AWADDR;
    assign M_AXI_AWLEN     = S_AXI_AWLEN;
    assign M_AXI_AWSIZE    = S_AXI_AWSIZE;
    assign M_AXI_AWBURST   = S_AXI_AWBURST;
    assign M_AXI_AWLOCK    = S_AXI_AWLOCK;
    assign M_AXI_AWCACHE   = S_AXI_AWCACHE;
    assign M_AXI_AWPROT    = S_AXI_AWPROT;
    assign M_AXI_AWQOS     = S_AXI_AWQOS;
    assign M_AXI_AWREGION  = S_AXI_AWREGION;
    assign M_AXI_AWUSER    = S_AXI_AWUSER;
    assign S_AXI_AWREADY   = M_AXI_AWREADY;
    assign M_AXI_AWVALID   = S_AXI_AWVALID;
  end endgenerate // gwach_pass_through;

  // Wiring logic for Write Data Channel
  generate if (C_WDCH_TYPE == 2) begin : gwdch_pass_through
    assign M_AXI_WID       = S_AXI_WID;
    assign M_AXI_WDATA     = S_AXI_WDATA;
    assign M_AXI_WSTRB     = S_AXI_WSTRB;
    assign M_AXI_WLAST     = S_AXI_WLAST;
    assign M_AXI_WUSER     = S_AXI_WUSER;
    assign S_AXI_WREADY    = M_AXI_WREADY;
    assign M_AXI_WVALID    = S_AXI_WVALID;
  end endgenerate // gwdch_pass_through;

  // Wiring logic for Write Response Channel
  generate if (C_WRCH_TYPE == 2) begin : gwrch_pass_through
    assign S_AXI_BID       = M_AXI_BID;
    assign S_AXI_BRESP     = M_AXI_BRESP;
    assign S_AXI_BUSER     = M_AXI_BUSER;
    assign M_AXI_BREADY    = S_AXI_BREADY;
    assign S_AXI_BVALID    = M_AXI_BVALID;
  end endgenerate // gwrch_pass_through;

  //-------------------------------------------------------------------------
  // Pass Through Logic for Read Channel
  //-------------------------------------------------------------------------

  // Wiring logic for Read Address Channel
  generate if (C_RACH_TYPE == 2) begin : grach_pass_through
    assign M_AXI_ARID      = S_AXI_ARID;
    assign M_AXI_ARADDR    = S_AXI_ARADDR;
    assign M_AXI_ARLEN     = S_AXI_ARLEN;
    assign M_AXI_ARSIZE    = S_AXI_ARSIZE;
    assign M_AXI_ARBURST   = S_AXI_ARBURST;
    assign M_AXI_ARLOCK    = S_AXI_ARLOCK;
    assign M_AXI_ARCACHE   = S_AXI_ARCACHE;
    assign M_AXI_ARPROT    = S_AXI_ARPROT;
    assign M_AXI_ARQOS     = S_AXI_ARQOS;
    assign M_AXI_ARREGION  = S_AXI_ARREGION;
    assign M_AXI_ARUSER    = S_AXI_ARUSER;
    assign S_AXI_ARREADY   = M_AXI_ARREADY;
    assign M_AXI_ARVALID   = S_AXI_ARVALID;
  end endgenerate // grach_pass_through;

  // Wiring logic for Read Data Channel 
  generate if (C_RDCH_TYPE == 2) begin : grdch_pass_through
    assign S_AXI_RID      = M_AXI_RID;
    assign S_AXI_RLAST    = M_AXI_RLAST;
    assign S_AXI_RUSER    = M_AXI_RUSER;
    assign S_AXI_RDATA    = M_AXI_RDATA;
    assign S_AXI_RRESP    = M_AXI_RRESP;
    assign S_AXI_RVALID   = M_AXI_RVALID;
    assign M_AXI_RREADY   = S_AXI_RREADY;
  end endgenerate // grdch_pass_through;

  // Wiring logic for AXI Streaming
  generate if (C_AXIS_TYPE == 2) begin : gaxis_pass_through
    assign M_AXIS_TDATA   = S_AXIS_TDATA;
    assign M_AXIS_TSTRB   = S_AXIS_TSTRB;
    assign M_AXIS_TKEEP   = S_AXIS_TKEEP;
    assign M_AXIS_TID     = S_AXIS_TID;
    assign M_AXIS_TDEST   = S_AXIS_TDEST;
    assign M_AXIS_TUSER   = S_AXIS_TUSER;
    assign M_AXIS_TLAST   = S_AXIS_TLAST;
    assign S_AXIS_TREADY  = M_AXIS_TREADY;
    assign M_AXIS_TVALID  = S_AXIS_TVALID;
  end endgenerate // gaxis_pass_through;


endmodule //fifo_generator_v13_1_2



/*******************************************************************************
 * Declaration of top-level module for Conventional FIFO
 ******************************************************************************/
module fifo_generator_v13_1_2_CONV_VER
  #(
    parameter  C_COMMON_CLOCK                 = 0,
    parameter  C_INTERFACE_TYPE               = 0,
    parameter  C_EN_SAFETY_CKT                = 0,
    parameter  C_COUNT_TYPE                   = 0,
    parameter  C_DATA_COUNT_WIDTH             = 2,
    parameter  C_DEFAULT_VALUE                = "",
    parameter  C_DIN_WIDTH                    = 8,
    parameter  C_DOUT_RST_VAL                 = "",
    parameter  C_DOUT_WIDTH                   = 8,
    parameter  C_ENABLE_RLOCS                 = 0,
    parameter  C_FAMILY                       = "virtex7", //Not allowed in Verilog model
    parameter  C_FULL_FLAGS_RST_VAL           = 1,
    parameter  C_HAS_ALMOST_EMPTY             = 0,
    parameter  C_HAS_ALMOST_FULL              = 0,
    parameter  C_HAS_BACKUP                   = 0,
    parameter  C_HAS_DATA_COUNT               = 0,
    parameter  C_HAS_INT_CLK                  = 0,
    parameter  C_HAS_MEMINIT_FILE             = 0,
    parameter  C_HAS_OVERFLOW                 = 0,
    parameter  C_HAS_RD_DATA_COUNT            = 0,
    parameter  C_HAS_RD_RST                   = 0,
    parameter  C_HAS_RST                      = 0,
    parameter  C_HAS_SRST                     = 0,
    parameter  C_HAS_UNDERFLOW                = 0,
    parameter  C_HAS_VALID                    = 0,
    parameter  C_HAS_WR_ACK                   = 0,
    parameter  C_HAS_WR_DATA_COUNT            = 0,
    parameter  C_HAS_WR_RST                   = 0,
    parameter  C_IMPLEMENTATION_TYPE          = 0,
    parameter  C_INIT_WR_PNTR_VAL             = 0,
    parameter  C_MEMORY_TYPE                  = 1,
    parameter  C_MIF_FILE_NAME                = "",
    parameter  C_OPTIMIZATION_MODE            = 0,
    parameter  C_OVERFLOW_LOW                 = 0,
    parameter  C_PRELOAD_LATENCY              = 1,
    parameter  C_PRELOAD_REGS                 = 0,
    parameter  C_PRIM_FIFO_TYPE               = "",
    parameter  C_PROG_EMPTY_THRESH_ASSERT_VAL = 0,
    parameter  C_PROG_EMPTY_THRESH_NEGATE_VAL = 0,
    parameter  C_PROG_EMPTY_TYPE              = 0,
    parameter  C_PROG_FULL_THRESH_ASSERT_VAL  = 0,
    parameter  C_PROG_FULL_THRESH_NEGATE_VAL  = 0,
    parameter  C_PROG_FULL_TYPE               = 0,
    parameter  C_RD_DATA_COUNT_WIDTH          = 2,
    parameter  C_RD_DEPTH                     = 256,
    parameter  C_RD_FREQ                      = 1,
    parameter  C_RD_PNTR_WIDTH                = 8,
    parameter  C_UNDERFLOW_LOW                = 0,
    parameter  C_USE_DOUT_RST                 = 0,
    parameter  C_USE_ECC                      = 0,
    parameter  C_USE_EMBEDDED_REG             = 0,
    parameter  C_USE_FIFO16_FLAGS             = 0,
    parameter  C_USE_FWFT_DATA_COUNT          = 0,
    parameter  C_VALID_LOW                    = 0,
    parameter  C_WR_ACK_LOW                   = 0,
    parameter  C_WR_DATA_COUNT_WIDTH          = 2,
    parameter  C_WR_DEPTH                     = 256,
    parameter  C_WR_FREQ                      = 1,
    parameter  C_WR_PNTR_WIDTH                = 8,
    parameter  C_WR_RESPONSE_LATENCY          = 1,
    parameter  C_MSGON_VAL                    = 1,
    parameter  C_ENABLE_RST_SYNC              = 1,
    parameter  C_ERROR_INJECTION_TYPE         = 0,
    parameter  C_FIFO_TYPE                    = 0,
    parameter  C_SYNCHRONIZER_STAGE           = 2,
    parameter  C_AXI_TYPE                     = 0
   )

  (
   input                               BACKUP,
   input                               BACKUP_MARKER,
   input                               CLK,
   input                               RST,
   input                               SRST,
   input                               WR_CLK,
   input                               WR_RST,
   input                               RD_CLK,
   input                               RD_RST,
   input [C_DIN_WIDTH-1:0]             DIN,
   input                               WR_EN,
   input                               RD_EN,
   input [C_RD_PNTR_WIDTH-1:0]         PROG_EMPTY_THRESH,
   input [C_RD_PNTR_WIDTH-1:0]         PROG_EMPTY_THRESH_ASSERT,
   input [C_RD_PNTR_WIDTH-1:0]         PROG_EMPTY_THRESH_NEGATE,
   input [C_WR_PNTR_WIDTH-1:0]         PROG_FULL_THRESH,
   input [C_WR_PNTR_WIDTH-1:0]         PROG_FULL_THRESH_ASSERT,
   input [C_WR_PNTR_WIDTH-1:0]         PROG_FULL_THRESH_NEGATE,
   input                               INT_CLK,
   input                               INJECTDBITERR,
   input                               INJECTSBITERR,
  
   output [C_DOUT_WIDTH-1:0]           DOUT,
   output                              FULL,
   output                              ALMOST_FULL,
   output                              WR_ACK,
   output                              OVERFLOW,
   output                              EMPTY,
   output                              ALMOST_EMPTY,
   output                              VALID,
   output                              UNDERFLOW,
   output [C_DATA_COUNT_WIDTH-1:0]     DATA_COUNT,
   output [C_RD_DATA_COUNT_WIDTH-1:0]  RD_DATA_COUNT,
   output [C_WR_DATA_COUNT_WIDTH-1:0]  WR_DATA_COUNT,
   output                              PROG_FULL,
   output                              PROG_EMPTY,
   output                              SBITERR,
   output                              DBITERR,
   output                              wr_rst_busy_o,
   output                              wr_rst_busy,
   output                              rd_rst_busy,
   output                              wr_rst_i_out,
   output                              rd_rst_i_out
  );

/*
 ******************************************************************************
 * Definition of Parameters
 ******************************************************************************
 *     C_COMMON_CLOCK                : Common Clock (1), Independent Clocks (0)
 *     C_COUNT_TYPE                  :    *not used
 *     C_DATA_COUNT_WIDTH            : Width of DATA_COUNT bus
 *     C_DEFAULT_VALUE               :    *not used
 *     C_DIN_WIDTH                   : Width of DIN bus
 *     C_DOUT_RST_VAL                : Reset value of DOUT
 *     C_DOUT_WIDTH                  : Width of DOUT bus
 *     C_ENABLE_RLOCS                :    *not used
 *     C_FAMILY                      : not used in bhv model
 *     C_FULL_FLAGS_RST_VAL          : Full flags rst val (0 or 1)
 *     C_HAS_ALMOST_EMPTY            : 1=Core has ALMOST_EMPTY flag
 *     C_HAS_ALMOST_FULL             : 1=Core has ALMOST_FULL flag
 *     C_HAS_BACKUP                  :    *not used
 *     C_HAS_DATA_COUNT              : 1=Core has DATA_COUNT bus
 *     C_HAS_INT_CLK                 : not used in bhv model
 *     C_HAS_MEMINIT_FILE            :    *not used
 *     C_HAS_OVERFLOW                : 1=Core has OVERFLOW flag
 *     C_HAS_RD_DATA_COUNT           : 1=Core has RD_DATA_COUNT bus
 *     C_HAS_RD_RST                  :    *not used
 *     C_HAS_RST                     : 1=Core has Async Rst
 *     C_HAS_SRST                    : 1=Core has Sync Rst
 *     C_HAS_UNDERFLOW               : 1=Core has UNDERFLOW flag
 *     C_HAS_VALID                   : 1=Core has VALID flag
 *     C_HAS_WR_ACK                  : 1=Core has WR_ACK flag
 *     C_HAS_WR_DATA_COUNT           : 1=Core has WR_DATA_COUNT bus
 *     C_HAS_WR_RST                  :    *not used
 *     C_IMPLEMENTATION_TYPE         : 0=Common-Clock Bram/Dram
 *                                     1=Common-Clock ShiftRam
 *                                     2=Indep. Clocks Bram/Dram
 *                                     3=Virtex-4 Built-in
 *                                     4=Virtex-5 Built-in
 *     C_INIT_WR_PNTR_VAL            :   *not used
 *     C_MEMORY_TYPE                 : 1=Block RAM
 *                                     2=Distributed RAM
 *                                     3=Shift RAM
 *                                     4=Built-in FIFO
 *     C_MIF_FILE_NAME               :   *not used
 *     C_OPTIMIZATION_MODE           :   *not used
 *     C_OVERFLOW_LOW                : 1=OVERFLOW active low
 *     C_PRELOAD_LATENCY             : Latency of read: 0, 1, 2
 *     C_PRELOAD_REGS                : 1=Use output registers
 *     C_PRIM_FIFO_TYPE              : not used in bhv model
 *     C_PROG_EMPTY_THRESH_ASSERT_VAL: PROG_EMPTY assert threshold
 *     C_PROG_EMPTY_THRESH_NEGATE_VAL: PROG_EMPTY negate threshold
 *     C_PROG_EMPTY_TYPE             : 0=No programmable empty
 *                                     1=Single prog empty thresh constant
 *                                     2=Multiple prog empty thresh constants
 *                                     3=Single prog empty thresh input
 *                                     4=Multiple prog empty thresh inputs
 *     C_PROG_FULL_THRESH_ASSERT_VAL : PROG_FULL assert threshold
 *     C_PROG_FULL_THRESH_NEGATE_VAL : PROG_FULL negate threshold
 *     C_PROG_FULL_TYPE              : 0=No prog full
 *                                     1=Single prog full thresh constant
 *                                     2=Multiple prog full thresh constants
 *                                     3=Single prog full thresh input
 *                                     4=Multiple prog full thresh inputs
 *     C_RD_DATA_COUNT_WIDTH         : Width of RD_DATA_COUNT bus
 *     C_RD_DEPTH                    : Depth of read interface (2^N)
 *     C_RD_FREQ                     : not used in bhv model
 *     C_RD_PNTR_WIDTH               : always log2(C_RD_DEPTH)
 *     C_UNDERFLOW_LOW               : 1=UNDERFLOW active low
 *     C_USE_DOUT_RST                : 1=Resets DOUT on RST
 *     C_USE_ECC                     : Used for error injection purpose
 *     C_USE_EMBEDDED_REG            : 1=Use BRAM embedded output register
 *     C_USE_FIFO16_FLAGS            : not used in bhv model
 *     C_USE_FWFT_DATA_COUNT         : 1=Use extra logic for FWFT data count
 *     C_VALID_LOW                   : 1=VALID active low
 *     C_WR_ACK_LOW                  : 1=WR_ACK active low
 *     C_WR_DATA_COUNT_WIDTH         : Width of WR_DATA_COUNT bus
 *     C_WR_DEPTH                    : Depth of write interface (2^N)
 *     C_WR_FREQ                     : not used in bhv model
 *     C_WR_PNTR_WIDTH               : always log2(C_WR_DEPTH)
 *     C_WR_RESPONSE_LATENCY         :    *not used
 *     C_MSGON_VAL                   :    *not used by bhv model
 *     C_ENABLE_RST_SYNC             : 0 = Use WR_RST & RD_RST
 *                                     1 = Use RST
 *     C_ERROR_INJECTION_TYPE        : 0 = No error injection
 *                                     1 = Single bit error injection only
 *                                     2 = Double bit error injection only
 *                                     3 = Single and double bit error injection
 ******************************************************************************
 * Definition of Ports
 ******************************************************************************
 *   BACKUP       : Not used
 *   BACKUP_MARKER: Not used
 *   CLK          : Clock
 *   DIN          : Input data bus
 *   PROG_EMPTY_THRESH       : Threshold for Programmable Empty Flag
 *   PROG_EMPTY_THRESH_ASSERT: Threshold for Programmable Empty Flag
 *   PROG_EMPTY_THRESH_NEGATE: Threshold for Programmable Empty Flag
 *   PROG_FULL_THRESH        : Threshold for Programmable Full Flag
 *   PROG_FULL_THRESH_ASSERT : Threshold for Programmable Full Flag
 *   PROG_FULL_THRESH_NEGATE : Threshold for Programmable Full Flag
 *   RD_CLK       : Read Domain Clock
 *   RD_EN        : Read enable
 *   RD_RST       : Read Reset
 *   RST          : Asynchronous Reset
 *   SRST         : Synchronous Reset
 *   WR_CLK       : Write Domain Clock
 *   WR_EN        : Write enable
 *   WR_RST       : Write Reset
 *   INT_CLK      : Internal Clock
 *   INJECTSBITERR: Inject Signle bit error
 *   INJECTDBITERR: Inject Double bit error
 *   ALMOST_EMPTY : One word remaining in FIFO
 *   ALMOST_FULL  : One empty space remaining in FIFO
 *   DATA_COUNT   : Number of data words in fifo( synchronous to CLK)
 *   DOUT         : Output data bus
 *   EMPTY        : Empty flag
 *   FULL         : Full flag
 *   OVERFLOW     : Last write rejected
 *   PROG_EMPTY   : Programmable Empty Flag
 *   PROG_FULL    : Programmable Full Flag
 *   RD_DATA_COUNT: Number of data words in fifo (synchronous to RD_CLK)
 *   UNDERFLOW    : Last read rejected
 *   VALID        : Last read acknowledged, DOUT bus VALID
 *   WR_ACK       : Last write acknowledged
 *   WR_DATA_COUNT: Number of data words in fifo (synchronous to WR_CLK)
 *   SBITERR      : Single Bit ECC Error Detected
 *   DBITERR      : Double Bit ECC Error Detected
 ******************************************************************************
 */

  //----------------------------------------------------------------------------
  //- Internal Signals for delayed input signals
  //- All the input signals except Clock are delayed by 100 ps and then given to
  //- the models.
  //----------------------------------------------------------------------------
 
  reg                         rst_delayed                       ;
  reg                         empty_fb                       ;
  reg                         srst_delayed                      ;
  reg                         wr_rst_delayed                    ;
  reg                         rd_rst_delayed                    ;
  reg                         wr_en_delayed                     ;
  reg                         rd_en_delayed                     ;
  reg  [C_DIN_WIDTH-1:0]      din_delayed                       ;
  reg  [C_RD_PNTR_WIDTH-1:0]  prog_empty_thresh_delayed         ;
  reg  [C_RD_PNTR_WIDTH-1:0]  prog_empty_thresh_assert_delayed  ;
  reg  [C_RD_PNTR_WIDTH-1:0]  prog_empty_thresh_negate_delayed  ;
  reg  [C_WR_PNTR_WIDTH-1:0]  prog_full_thresh_delayed          ;
  reg  [C_WR_PNTR_WIDTH-1:0]  prog_full_thresh_assert_delayed   ;
  reg  [C_WR_PNTR_WIDTH-1:0]  prog_full_thresh_negate_delayed   ;
  reg                         injectdbiterr_delayed             ;
  reg                         injectsbiterr_delayed             ;
   wire                        empty_p0_out;

  always @* rst_delayed                       <= #`TCQ RST                      ;
  always @* empty_fb                       <= #`TCQ empty_p0_out                      ;
  always @* srst_delayed                      <= #`TCQ SRST                     ; 
  always @* wr_rst_delayed                    <= #`TCQ WR_RST                   ; 
  always @* rd_rst_delayed                    <= #`TCQ RD_RST                   ; 
  always @* din_delayed                       <= #`TCQ DIN                      ; 
  always @* wr_en_delayed                     <= #`TCQ WR_EN                    ; 
  always @* rd_en_delayed                     <= #`TCQ RD_EN                    ; 
  always @* prog_empty_thresh_delayed         <= #`TCQ PROG_EMPTY_THRESH        ; 
  always @* prog_empty_thresh_assert_delayed  <= #`TCQ PROG_EMPTY_THRESH_ASSERT ; 
  always @* prog_empty_thresh_negate_delayed  <= #`TCQ PROG_EMPTY_THRESH_NEGATE ; 
  always @* prog_full_thresh_delayed          <= #`TCQ PROG_FULL_THRESH         ; 
  always @* prog_full_thresh_assert_delayed   <= #`TCQ PROG_FULL_THRESH_ASSERT  ; 
  always @* prog_full_thresh_negate_delayed   <= #`TCQ PROG_FULL_THRESH_NEGATE  ; 
  always @* injectdbiterr_delayed             <= #`TCQ INJECTDBITERR            ; 
  always @* injectsbiterr_delayed             <= #`TCQ INJECTSBITERR            ; 

  /*****************************************************************************
   * Derived parameters
   ****************************************************************************/
  //There are 2 Verilog behavioral models
  // 0 = Common-Clock FIFO/ShiftRam FIFO
  // 1 = Independent Clocks FIFO
  // 2 = Low Latency Synchronous FIFO
  // 3 = Low Latency Asynchronous FIFO
  localparam C_VERILOG_IMPL = (C_FIFO_TYPE == 3) ? 2 :
                              (C_IMPLEMENTATION_TYPE == 2) ? 1 : 0;
  localparam IS_8SERIES         = (C_FAMILY == "virtexu" || C_FAMILY == "kintexu" || C_FAMILY == "artixu" || C_FAMILY == "virtexuplus" || C_FAMILY == "zynquplus" || C_FAMILY == "kintexuplus") ? 1 : 0;

  //Internal reset signals
  reg                                rd_rst_asreg    = 0;
  wire                               rd_rst_asreg_d1;
  wire                               rd_rst_asreg_d2;
  reg                                rd_rst_asreg_d3 = 0;
  reg                                rd_rst_reg      = 0;
  wire                               rd_rst_comb;
  reg                                wr_rst_d0       = 0;
  reg                                wr_rst_d1       = 0;
  reg                                wr_rst_d2       = 0;
  reg                                rd_rst_d0       = 0;
  reg                                rd_rst_d1       = 0;
  reg                                rd_rst_d2       = 0;
  reg                                rd_rst_d3       = 0;
  reg                                wrrst_done      = 0;
  reg                                rdrst_done      = 0;
  reg                                wr_rst_asreg    = 0;
  wire                               wr_rst_asreg_d1;
  wire                               wr_rst_asreg_d2;
  reg                                wr_rst_asreg_d3 = 0;
  reg                                rd_rst_wr_d0    = 0;
  reg                                rd_rst_wr_d1    = 0;
  reg                                rd_rst_wr_d2    = 0;
  reg                                wr_rst_reg      = 0;
  reg                                rst_active_i    = 1'b1;
  reg                                rst_delayed_d1  = 1'b1;
  reg                                rst_delayed_d2  = 1'b1;
  wire                               wr_rst_comb;
  wire                               wr_rst_i;
  wire                               rd_rst_i;
  wire                               rst_i;

  //Internal reset signals
  reg                                rst_asreg    = 0;
  reg                                srst_asreg    = 0;
  wire                               rst_asreg_d1;
  wire                               rst_asreg_d2;
  reg                                srst_asreg_d1 = 0;
  reg                                srst_asreg_d2 = 0;
  reg                                rst_reg      = 0;
  reg                                srst_reg      = 0;
  wire                               rst_comb;
  wire                               srst_comb;
  reg                                rst_full_gen_i = 0;
  reg                                rst_full_ff_i = 0;
  reg  [2:0]                         sckt_ff0_bsy_o_i = {3{1'b0}};
                                     
  wire                               RD_CLK_P0_IN;
  wire                               RST_P0_IN;
  wire                               RD_EN_FIFO_IN;
  wire                               RD_EN_P0_IN;

  wire                               ALMOST_EMPTY_FIFO_OUT;
  wire                               ALMOST_FULL_FIFO_OUT;
  wire [C_DATA_COUNT_WIDTH-1:0]      DATA_COUNT_FIFO_OUT;
  wire [C_DOUT_WIDTH-1:0]            DOUT_FIFO_OUT;
  wire                               EMPTY_FIFO_OUT;
  wire                               fifo_empty_fb;
  wire                               FULL_FIFO_OUT;
  wire                               OVERFLOW_FIFO_OUT;
  wire                               PROG_EMPTY_FIFO_OUT;
  wire                               PROG_FULL_FIFO_OUT;
  wire                               VALID_FIFO_OUT;
  wire [C_RD_DATA_COUNT_WIDTH-1:0]   RD_DATA_COUNT_FIFO_OUT;
  wire                               UNDERFLOW_FIFO_OUT;
  wire                               WR_ACK_FIFO_OUT;
  wire [C_WR_DATA_COUNT_WIDTH-1:0]   WR_DATA_COUNT_FIFO_OUT;


  //***************************************************************************
  // Internal Signals
  //   The core uses either the internal_ wires or the preload0_ wires depending
  //     on whether the core uses Preload0 or not.
  //   When using preload0, the internal signals connect the internal core to
  //     the preload logic, and the external core's interfaces are tied to the
  //     preload0 signals from the preload logic.
  //***************************************************************************
  wire [C_DOUT_WIDTH-1:0]            DATA_P0_OUT;
  wire                               VALID_P0_OUT;
  wire                               EMPTY_P0_OUT;
  wire                               ALMOSTEMPTY_P0_OUT;
  reg                                EMPTY_P0_OUT_Q;
  reg                                ALMOSTEMPTY_P0_OUT_Q;
  wire                               UNDERFLOW_P0_OUT;
  wire                               RDEN_P0_OUT;
  wire [C_DOUT_WIDTH-1:0]            DATA_P0_IN;
  wire                               EMPTY_P0_IN;
  reg  [31:0]                        DATA_COUNT_FWFT;
  reg                                SS_FWFT_WR  ;
  reg                                SS_FWFT_RD ;

  wire                               sbiterr_fifo_out;
  wire                               dbiterr_fifo_out;
  wire                               inject_sbit_err;
  wire                               inject_dbit_err;
  wire                               safety_ckt_wr_rst;
  wire                               safety_ckt_rd_rst;
  reg                                sckt_wr_rst_i_q = 1'b0;
 
  wire                               w_fab_read_data_valid_i;
  wire                               w_read_data_valid_i;
  wire                               w_ram_valid_i;
  // Assign 0 if not selected to avoid 'X' propogation to S/DBITERR.
  assign inject_sbit_err = ((C_ERROR_INJECTION_TYPE == 1) || (C_ERROR_INJECTION_TYPE == 3)) ?
                           injectsbiterr_delayed : 0;
  assign inject_dbit_err = ((C_ERROR_INJECTION_TYPE == 2) || (C_ERROR_INJECTION_TYPE == 3)) ?
                           injectdbiterr_delayed : 0;
                           
  assign wr_rst_i_out = wr_rst_i;
  assign rd_rst_i_out = rd_rst_i;
  assign wr_rst_busy_o = wr_rst_busy | rst_full_gen_i | sckt_ff0_bsy_o_i[2];
  generate if (C_FULL_FLAGS_RST_VAL == 0 && C_EN_SAFETY_CKT == 1) begin : gsckt_bsy_o
    wire clk_i = C_COMMON_CLOCK ? CLK : WR_CLK;
    always @ (posedge clk_i)
      sckt_ff0_bsy_o_i <= {sckt_ff0_bsy_o_i[1:0],wr_rst_busy}; 
  end endgenerate 
// Choose the behavioral model to instantiate based on the C_VERILOG_IMPL
// parameter (1=Independent Clocks, 0=Common Clock)

  localparam FULL_FLAGS_RST_VAL = (C_HAS_SRST == 1) ? 0 : C_FULL_FLAGS_RST_VAL;
generate
case (C_VERILOG_IMPL)
0 : begin : block1
  //Common Clock Behavioral Model
  fifo_generator_v13_1_2_bhv_ver_ss
  #(
    .C_FAMILY                            (C_FAMILY),
    .C_DATA_COUNT_WIDTH                  (C_DATA_COUNT_WIDTH),            
    .C_DIN_WIDTH                         (C_DIN_WIDTH),                   
    .C_DOUT_RST_VAL                      (C_DOUT_RST_VAL),                
    .C_DOUT_WIDTH                        (C_DOUT_WIDTH),                  
    .C_FULL_FLAGS_RST_VAL                (FULL_FLAGS_RST_VAL),            
    .C_HAS_ALMOST_EMPTY                  (C_HAS_ALMOST_EMPTY),            
    .C_HAS_ALMOST_FULL                   ((C_AXI_TYPE == 0 && C_FIFO_TYPE == 1) ? 1 : C_HAS_ALMOST_FULL),             
    .C_HAS_DATA_COUNT                    (C_HAS_DATA_COUNT),              
    .C_HAS_OVERFLOW                      (C_HAS_OVERFLOW),                
    .C_HAS_RD_DATA_COUNT                 (C_HAS_RD_DATA_COUNT),           
    .C_HAS_RST                           (C_HAS_RST),                     
    .C_HAS_SRST                          (C_HAS_SRST),                    
    .C_HAS_UNDERFLOW                     (C_HAS_UNDERFLOW),               
    .C_HAS_VALID                         (C_HAS_VALID),                   
    .C_HAS_WR_ACK                        (C_HAS_WR_ACK),                  
    .C_HAS_WR_DATA_COUNT                 (C_HAS_WR_DATA_COUNT),           
    .C_IMPLEMENTATION_TYPE               (C_IMPLEMENTATION_TYPE),         
    .C_MEMORY_TYPE                       (C_MEMORY_TYPE),                 
    .C_OVERFLOW_LOW                      (C_OVERFLOW_LOW),                
    .C_PRELOAD_LATENCY                   (C_PRELOAD_LATENCY),             
    .C_PRELOAD_REGS                      (C_PRELOAD_REGS),                
    .C_PROG_EMPTY_THRESH_ASSERT_VAL      (C_PROG_EMPTY_THRESH_ASSERT_VAL),
    .C_PROG_EMPTY_THRESH_NEGATE_VAL      (C_PROG_EMPTY_THRESH_NEGATE_VAL),
    .C_PROG_EMPTY_TYPE                   (C_PROG_EMPTY_TYPE),             
    .C_PROG_FULL_THRESH_ASSERT_VAL       (C_PROG_FULL_THRESH_ASSERT_VAL), 
    .C_PROG_FULL_THRESH_NEGATE_VAL       (C_PROG_FULL_THRESH_NEGATE_VAL), 
    .C_PROG_FULL_TYPE                    (C_PROG_FULL_TYPE),              
    .C_RD_DATA_COUNT_WIDTH               (C_RD_DATA_COUNT_WIDTH),         
    .C_RD_DEPTH                          (C_RD_DEPTH),                    
    .C_RD_PNTR_WIDTH                     (C_RD_PNTR_WIDTH),               
    .C_UNDERFLOW_LOW                     (C_UNDERFLOW_LOW),               
    .C_USE_DOUT_RST                      (C_USE_DOUT_RST),                
    .C_USE_EMBEDDED_REG                  (C_USE_EMBEDDED_REG),
    .C_EN_SAFETY_CKT                     (C_EN_SAFETY_CKT),            
    .C_USE_FWFT_DATA_COUNT               (C_USE_FWFT_DATA_COUNT),         
    .C_VALID_LOW                         (C_VALID_LOW),                   
    .C_WR_ACK_LOW                        (C_WR_ACK_LOW),                  
    .C_WR_DATA_COUNT_WIDTH               (C_WR_DATA_COUNT_WIDTH),         
    .C_WR_DEPTH                          (C_WR_DEPTH),                    
    .C_WR_PNTR_WIDTH                     (C_WR_PNTR_WIDTH),               
    .C_USE_ECC                           (C_USE_ECC),                     
    .C_ENABLE_RST_SYNC                   (C_ENABLE_RST_SYNC),             
    .C_ERROR_INJECTION_TYPE              (C_ERROR_INJECTION_TYPE),
    .C_FIFO_TYPE                         (C_FIFO_TYPE)                     
  )
  gen_ss
  (
    .SAFETY_CKT_WR_RST        (safety_ckt_wr_rst),
    .CLK                      (CLK),
    .RST                      (rst_i),
    .SRST                     (srst_delayed),
    .RST_FULL_GEN             (rst_full_gen_i),
    .RST_FULL_FF              (rst_full_ff_i),
    .DIN                      (din_delayed),
    .WR_EN                    (wr_en_delayed),
    .RD_EN                    (RD_EN_FIFO_IN),
    .RD_EN_USER               (rd_en_delayed),
    .USER_EMPTY_FB            (empty_fb),
    .PROG_EMPTY_THRESH        (prog_empty_thresh_delayed),
    .PROG_EMPTY_THRESH_ASSERT (prog_empty_thresh_assert_delayed),
    .PROG_EMPTY_THRESH_NEGATE (prog_empty_thresh_negate_delayed),
    .PROG_FULL_THRESH         (prog_full_thresh_delayed),
    .PROG_FULL_THRESH_ASSERT  (prog_full_thresh_assert_delayed),
    .PROG_FULL_THRESH_NEGATE  (prog_full_thresh_negate_delayed),
    .INJECTSBITERR            (inject_sbit_err),
    .INJECTDBITERR            (inject_dbit_err),
    .DOUT                     (DOUT_FIFO_OUT),
    .FULL                     (FULL_FIFO_OUT),
    .ALMOST_FULL              (ALMOST_FULL_FIFO_OUT),
    .WR_ACK                   (WR_ACK_FIFO_OUT),
    .OVERFLOW                 (OVERFLOW_FIFO_OUT),
    .EMPTY                    (EMPTY_FIFO_OUT),
    .EMPTY_FB                 (fifo_empty_fb),
    .ALMOST_EMPTY             (ALMOST_EMPTY_FIFO_OUT),
    .VALID                    (VALID_FIFO_OUT),
    .UNDERFLOW                (UNDERFLOW_FIFO_OUT),
    .DATA_COUNT               (DATA_COUNT_FIFO_OUT),
    .RD_DATA_COUNT            (RD_DATA_COUNT_FIFO_OUT),
    .WR_DATA_COUNT            (WR_DATA_COUNT_FIFO_OUT),
    .PROG_FULL                (PROG_FULL_FIFO_OUT),
    .PROG_EMPTY               (PROG_EMPTY_FIFO_OUT),
    .WR_RST_BUSY              (wr_rst_busy),
    .RD_RST_BUSY              (rd_rst_busy),
    .SBITERR                  (sbiterr_fifo_out),
    .DBITERR                  (dbiterr_fifo_out)
   );
end
1 : begin : block1
  //Independent Clocks Behavioral Model
  fifo_generator_v13_1_2_bhv_ver_as
  #(
    .C_FAMILY                          (C_FAMILY),
    .C_DATA_COUNT_WIDTH                (C_DATA_COUNT_WIDTH),
    .C_DIN_WIDTH                       (C_DIN_WIDTH),
    .C_DOUT_RST_VAL                    (C_DOUT_RST_VAL),
    .C_DOUT_WIDTH                      (C_DOUT_WIDTH),
    .C_FULL_FLAGS_RST_VAL              (C_FULL_FLAGS_RST_VAL),
    .C_HAS_ALMOST_EMPTY                (C_HAS_ALMOST_EMPTY),
    .C_HAS_ALMOST_FULL                 (C_HAS_ALMOST_FULL),
    .C_HAS_DATA_COUNT                  (C_HAS_DATA_COUNT),
    .C_HAS_OVERFLOW                    (C_HAS_OVERFLOW),
    .C_HAS_RD_DATA_COUNT               (C_HAS_RD_DATA_COUNT),
    .C_HAS_RST                         (C_HAS_RST),
    .C_HAS_UNDERFLOW                   (C_HAS_UNDERFLOW),
    .C_HAS_VALID                       (C_HAS_VALID),
    .C_HAS_WR_ACK                      (C_HAS_WR_ACK),
    .C_HAS_WR_DATA_COUNT               (C_HAS_WR_DATA_COUNT),
    .C_IMPLEMENTATION_TYPE             (C_IMPLEMENTATION_TYPE),
    .C_MEMORY_TYPE                     (C_MEMORY_TYPE),
    .C_OVERFLOW_LOW                    (C_OVERFLOW_LOW),
    .C_PRELOAD_LATENCY                 (C_PRELOAD_LATENCY),
    .C_PRELOAD_REGS                    (C_PRELOAD_REGS),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL    (C_PROG_EMPTY_THRESH_ASSERT_VAL),
    .C_PROG_EMPTY_THRESH_NEGATE_VAL    (C_PROG_EMPTY_THRESH_NEGATE_VAL),
    .C_PROG_EMPTY_TYPE                 (C_PROG_EMPTY_TYPE),
    .C_PROG_FULL_THRESH_ASSERT_VAL     (C_PROG_FULL_THRESH_ASSERT_VAL),
    .C_PROG_FULL_THRESH_NEGATE_VAL     (C_PROG_FULL_THRESH_NEGATE_VAL),
    .C_PROG_FULL_TYPE                  (C_PROG_FULL_TYPE),
    .C_RD_DATA_COUNT_WIDTH             (C_RD_DATA_COUNT_WIDTH),
    .C_RD_DEPTH                        (C_RD_DEPTH),
    .C_RD_PNTR_WIDTH                   (C_RD_PNTR_WIDTH),
    .C_UNDERFLOW_LOW                   (C_UNDERFLOW_LOW),
    .C_USE_DOUT_RST                    (C_USE_DOUT_RST),
    .C_USE_EMBEDDED_REG                (C_USE_EMBEDDED_REG),
    .C_EN_SAFETY_CKT                   (C_EN_SAFETY_CKT), 
    .C_USE_FWFT_DATA_COUNT             (C_USE_FWFT_DATA_COUNT),
    .C_VALID_LOW                       (C_VALID_LOW),
    .C_WR_ACK_LOW                      (C_WR_ACK_LOW),
    .C_WR_DATA_COUNT_WIDTH             (C_WR_DATA_COUNT_WIDTH),
    .C_WR_DEPTH                        (C_WR_DEPTH),
    .C_WR_PNTR_WIDTH                   (C_WR_PNTR_WIDTH),
    .C_USE_ECC                         (C_USE_ECC),
    .C_SYNCHRONIZER_STAGE              (C_SYNCHRONIZER_STAGE),
    .C_ENABLE_RST_SYNC                 (C_ENABLE_RST_SYNC),
    .C_ERROR_INJECTION_TYPE            (C_ERROR_INJECTION_TYPE)
  )
  gen_as
  (
    .SAFETY_CKT_WR_RST        (safety_ckt_wr_rst),
    .SAFETY_CKT_RD_RST        (safety_ckt_rd_rst),
    .WR_CLK                   (WR_CLK),
    .RD_CLK                   (RD_CLK),
    .RST                      (rst_i),
    .RST_FULL_GEN             (rst_full_gen_i),
    .RST_FULL_FF              (rst_full_ff_i),
    .WR_RST                   (wr_rst_i),
    .RD_RST                   (rd_rst_i),
    .DIN                      (din_delayed),
    .WR_EN                    (wr_en_delayed),
    .RD_EN                    (RD_EN_FIFO_IN),
    .RD_EN_USER               (rd_en_delayed),
    .PROG_EMPTY_THRESH        (prog_empty_thresh_delayed),
    .PROG_EMPTY_THRESH_ASSERT (prog_empty_thresh_assert_delayed),
    .PROG_EMPTY_THRESH_NEGATE (prog_empty_thresh_negate_delayed),
    .PROG_FULL_THRESH         (prog_full_thresh_delayed),
    .PROG_FULL_THRESH_ASSERT  (prog_full_thresh_assert_delayed),
    .PROG_FULL_THRESH_NEGATE  (prog_full_thresh_negate_delayed),
    .INJECTSBITERR            (inject_sbit_err),
    .INJECTDBITERR            (inject_dbit_err),
    .USER_EMPTY_FB            (EMPTY_P0_OUT),
    .DOUT                     (DOUT_FIFO_OUT),
    .FULL                     (FULL_FIFO_OUT),
    .ALMOST_FULL              (ALMOST_FULL_FIFO_OUT),
    .WR_ACK                   (WR_ACK_FIFO_OUT),
    .OVERFLOW                 (OVERFLOW_FIFO_OUT),
    .EMPTY                    (EMPTY_FIFO_OUT),
    .EMPTY_FB                 (fifo_empty_fb),
    .ALMOST_EMPTY             (ALMOST_EMPTY_FIFO_OUT),
    .VALID                    (VALID_FIFO_OUT),
    .UNDERFLOW                (UNDERFLOW_FIFO_OUT),
    .RD_DATA_COUNT            (RD_DATA_COUNT_FIFO_OUT),
    .WR_DATA_COUNT            (WR_DATA_COUNT_FIFO_OUT),
    .PROG_FULL                (PROG_FULL_FIFO_OUT),
    .PROG_EMPTY               (PROG_EMPTY_FIFO_OUT),
    .SBITERR                  (sbiterr_fifo_out),
    .fab_read_data_valid_i    (w_fab_read_data_valid_i),
    .read_data_valid_i        (w_read_data_valid_i),
    .ram_valid_i              (w_ram_valid_i),
    .DBITERR                  (dbiterr_fifo_out)
   );
end

2 : begin : ll_afifo_inst
  fifo_generator_v13_1_2_beh_ver_ll_afifo
  #(
    .C_DIN_WIDTH                    (C_DIN_WIDTH),
    .C_DOUT_RST_VAL                 (C_DOUT_RST_VAL),
    .C_DOUT_WIDTH                   (C_DOUT_WIDTH),
    .C_FULL_FLAGS_RST_VAL           (C_FULL_FLAGS_RST_VAL),
    .C_HAS_RD_DATA_COUNT            (C_HAS_RD_DATA_COUNT),
    .C_HAS_WR_DATA_COUNT            (C_HAS_WR_DATA_COUNT),
    .C_RD_DEPTH                     (C_RD_DEPTH),
    .C_RD_PNTR_WIDTH                (C_RD_PNTR_WIDTH),
    .C_USE_DOUT_RST                 (C_USE_DOUT_RST),
    .C_WR_DATA_COUNT_WIDTH          (C_WR_DATA_COUNT_WIDTH),
    .C_WR_DEPTH                     (C_WR_DEPTH),
    .C_WR_PNTR_WIDTH                (C_WR_PNTR_WIDTH),
    .C_FIFO_TYPE                    (C_FIFO_TYPE)
   )
  gen_ll_afifo
  (
    .DIN                        (din_delayed),
    .RD_CLK                     (RD_CLK),
    .RD_EN                      (rd_en_delayed),
    .WR_RST                     (wr_rst_i),
    .RD_RST                     (rd_rst_i),
    .WR_CLK                     (WR_CLK),
    .WR_EN                      (wr_en_delayed),
    .DOUT                       (DOUT),
    .EMPTY                      (EMPTY),
    .FULL                       (FULL)
  );
end
default : begin : block1
  //Independent Clocks Behavioral Model
  fifo_generator_v13_1_2_bhv_ver_as
  #(
    .C_FAMILY                          (C_FAMILY),
    .C_DATA_COUNT_WIDTH                (C_DATA_COUNT_WIDTH),
    .C_DIN_WIDTH                       (C_DIN_WIDTH),
    .C_DOUT_RST_VAL                    (C_DOUT_RST_VAL),
    .C_DOUT_WIDTH                      (C_DOUT_WIDTH),
    .C_FULL_FLAGS_RST_VAL              (C_FULL_FLAGS_RST_VAL),
    .C_HAS_ALMOST_EMPTY                (C_HAS_ALMOST_EMPTY),
    .C_HAS_ALMOST_FULL                 (C_HAS_ALMOST_FULL),
    .C_HAS_DATA_COUNT                  (C_HAS_DATA_COUNT),
    .C_HAS_OVERFLOW                    (C_HAS_OVERFLOW),
    .C_HAS_RD_DATA_COUNT               (C_HAS_RD_DATA_COUNT),
    .C_HAS_RST                         (C_HAS_RST),
    .C_HAS_UNDERFLOW                   (C_HAS_UNDERFLOW),
    .C_HAS_VALID                       (C_HAS_VALID),
    .C_HAS_WR_ACK                      (C_HAS_WR_ACK),
    .C_HAS_WR_DATA_COUNT               (C_HAS_WR_DATA_COUNT),
    .C_IMPLEMENTATION_TYPE             (C_IMPLEMENTATION_TYPE),
    .C_MEMORY_TYPE                     (C_MEMORY_TYPE),
    .C_OVERFLOW_LOW                    (C_OVERFLOW_LOW),
    .C_PRELOAD_LATENCY                 (C_PRELOAD_LATENCY),
    .C_PRELOAD_REGS                    (C_PRELOAD_REGS),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL    (C_PROG_EMPTY_THRESH_ASSERT_VAL),
    .C_PROG_EMPTY_THRESH_NEGATE_VAL    (C_PROG_EMPTY_THRESH_NEGATE_VAL),
    .C_PROG_EMPTY_TYPE                 (C_PROG_EMPTY_TYPE),
    .C_PROG_FULL_THRESH_ASSERT_VAL     (C_PROG_FULL_THRESH_ASSERT_VAL),
    .C_PROG_FULL_THRESH_NEGATE_VAL     (C_PROG_FULL_THRESH_NEGATE_VAL),
    .C_PROG_FULL_TYPE                  (C_PROG_FULL_TYPE),
    .C_RD_DATA_COUNT_WIDTH             (C_RD_DATA_COUNT_WIDTH),
    .C_RD_DEPTH                        (C_RD_DEPTH),
    .C_RD_PNTR_WIDTH                   (C_RD_PNTR_WIDTH),
    .C_UNDERFLOW_LOW                   (C_UNDERFLOW_LOW),
    .C_USE_DOUT_RST                    (C_USE_DOUT_RST),
    .C_USE_EMBEDDED_REG                (C_USE_EMBEDDED_REG),
    .C_EN_SAFETY_CKT                   (C_EN_SAFETY_CKT),
    .C_USE_FWFT_DATA_COUNT             (C_USE_FWFT_DATA_COUNT),
    .C_VALID_LOW                       (C_VALID_LOW),
    .C_WR_ACK_LOW                      (C_WR_ACK_LOW),
    .C_WR_DATA_COUNT_WIDTH             (C_WR_DATA_COUNT_WIDTH),
    .C_WR_DEPTH                        (C_WR_DEPTH),
    .C_WR_PNTR_WIDTH                   (C_WR_PNTR_WIDTH),
    .C_USE_ECC                         (C_USE_ECC),
    .C_SYNCHRONIZER_STAGE              (C_SYNCHRONIZER_STAGE),
    .C_ENABLE_RST_SYNC                 (C_ENABLE_RST_SYNC),
    .C_ERROR_INJECTION_TYPE            (C_ERROR_INJECTION_TYPE)
  )
  gen_as
  (
    .SAFETY_CKT_WR_RST        (safety_ckt_wr_rst),
    .SAFETY_CKT_RD_RST        (safety_ckt_rd_rst),
    .WR_CLK                   (WR_CLK),
    .RD_CLK                   (RD_CLK),
    .RST                      (rst_i),
    .RST_FULL_GEN             (rst_full_gen_i),
    .RST_FULL_FF              (rst_full_ff_i),
    .WR_RST                   (wr_rst_i),
    .RD_RST                   (rd_rst_i),
    .DIN                      (din_delayed),
    .WR_EN                    (wr_en_delayed),
    .RD_EN                    (RD_EN_FIFO_IN),
    .RD_EN_USER               (rd_en_delayed),
    .PROG_EMPTY_THRESH        (prog_empty_thresh_delayed),
    .PROG_EMPTY_THRESH_ASSERT (prog_empty_thresh_assert_delayed),
    .PROG_EMPTY_THRESH_NEGATE (prog_empty_thresh_negate_delayed),
    .PROG_FULL_THRESH         (prog_full_thresh_delayed),
    .PROG_FULL_THRESH_ASSERT  (prog_full_thresh_assert_delayed),
    .PROG_FULL_THRESH_NEGATE  (prog_full_thresh_negate_delayed),
    .INJECTSBITERR            (inject_sbit_err),
    .INJECTDBITERR            (inject_dbit_err),
    .USER_EMPTY_FB            (EMPTY_P0_OUT),
    .DOUT                     (DOUT_FIFO_OUT),
    .FULL                     (FULL_FIFO_OUT),
    .ALMOST_FULL              (ALMOST_FULL_FIFO_OUT),
    .WR_ACK                   (WR_ACK_FIFO_OUT),
    .OVERFLOW                 (OVERFLOW_FIFO_OUT),
    .EMPTY                    (EMPTY_FIFO_OUT),
    .EMPTY_FB                 (fifo_empty_fb),
    .ALMOST_EMPTY             (ALMOST_EMPTY_FIFO_OUT),
    .VALID                    (VALID_FIFO_OUT),
    .UNDERFLOW                (UNDERFLOW_FIFO_OUT),
    .RD_DATA_COUNT            (RD_DATA_COUNT_FIFO_OUT),
    .WR_DATA_COUNT            (WR_DATA_COUNT_FIFO_OUT),
    .PROG_FULL                (PROG_FULL_FIFO_OUT),
    .PROG_EMPTY               (PROG_EMPTY_FIFO_OUT),
    .SBITERR                  (sbiterr_fifo_out),
    .DBITERR                  (dbiterr_fifo_out)
   );
end

endcase
endgenerate


   //**************************************************************************
   // Connect Internal Signals
   //   (Signals labeled internal_*)
   //  In the normal case, these signals tie directly to the FIFO's inputs and
   //    outputs.
   //  In the case of Preload Latency 0 or 1, there are intermediate
   //    signals between the internal FIFO and the preload logic.
   //**************************************************************************
   
   
   //***********************************************
   // If First-Word Fall-Through, instantiate
   // the preload0 (FWFT) module
   //***********************************************
   wire                        rd_en_to_fwft_fifo;
   wire                        sbiterr_fwft;
   wire                        dbiterr_fwft;
   wire [C_DOUT_WIDTH-1:0]     dout_fwft;
   wire                        empty_fwft;
   wire                        rd_en_fifo_in;
   wire                        stage2_reg_en_i;
   wire [1:0]                  valid_stages_i;
   wire                        rst_fwft;
   //wire                        empty_p0_out;
   reg  [C_SYNCHRONIZER_STAGE-1:0] pkt_empty_sync = 'b1;

   localparam IS_FWFT          = (C_PRELOAD_REGS == 1 && C_PRELOAD_LATENCY == 0) ? 1 : 0;
   localparam IS_PKT_FIFO      = (C_FIFO_TYPE == 1) ? 1 : 0;
   localparam IS_AXIS_PKT_FIFO = (C_FIFO_TYPE == 1 && C_AXI_TYPE == 0) ? 1 : 0;
   assign rst_fwft = (C_COMMON_CLOCK == 0) ? rd_rst_i : (C_HAS_RST == 1) ? rst_i : 1'b0;

   generate if (IS_FWFT == 1 && C_FIFO_TYPE != 3) begin : block2


         fifo_generator_v13_1_2_bhv_ver_preload0
           #(
             .C_DOUT_RST_VAL      (C_DOUT_RST_VAL),
             .C_DOUT_WIDTH        (C_DOUT_WIDTH),
             .C_HAS_RST           (C_HAS_RST),
             .C_ENABLE_RST_SYNC   (C_ENABLE_RST_SYNC),
             .C_HAS_SRST          (C_HAS_SRST),
             .C_USE_DOUT_RST      (C_USE_DOUT_RST),
             .C_USE_EMBEDDED_REG  (C_USE_EMBEDDED_REG),
             .C_USE_ECC           (C_USE_ECC),
             .C_USERVALID_LOW     (C_VALID_LOW),
             .C_USERUNDERFLOW_LOW (C_UNDERFLOW_LOW),
             .C_EN_SAFETY_CKT     (C_EN_SAFETY_CKT),
             .C_MEMORY_TYPE       (C_MEMORY_TYPE),
             .C_FIFO_TYPE         (C_FIFO_TYPE)
             )
             fgpl0
               (
                .SAFETY_CKT_RD_RST(safety_ckt_rd_rst),
                .RD_CLK           (RD_CLK_P0_IN),
                .RD_RST           (RST_P0_IN),
                .SRST             (srst_delayed),
                .WR_RST_BUSY      (wr_rst_busy),
                .RD_RST_BUSY      (rd_rst_busy),
                .RD_EN            (RD_EN_P0_IN),
                .FIFOEMPTY        (EMPTY_P0_IN),
                .FIFODATA         (DATA_P0_IN),
                .FIFOSBITERR      (sbiterr_fifo_out),
                .FIFODBITERR      (dbiterr_fifo_out),
                // Output
                .USERDATA         (dout_fwft),
                .USERVALID        (VALID_P0_OUT),
                .USEREMPTY        (empty_fwft),
                .USERALMOSTEMPTY  (ALMOSTEMPTY_P0_OUT),
                .USERUNDERFLOW    (UNDERFLOW_P0_OUT),
                .RAMVALID         (),
                .FIFORDEN         (rd_en_fifo_in),
                .USERSBITERR      (sbiterr_fwft),
                .USERDBITERR      (dbiterr_fwft),
                .STAGE2_REG_EN    (stage2_reg_en_i),
                .fab_read_data_valid_i_o    (w_fab_read_data_valid_i),
                .read_data_valid_i_o        (w_read_data_valid_i),
                .ram_valid_i_o              (w_ram_valid_i),
                .VALID_STAGES                (valid_stages_i)
                );

         
         //***********************************************
         // Connect inputs to preload (FWFT) module
         //***********************************************
         //Connect the RD_CLK of the Preload (FWFT) module to CLK if we 
         // have a common-clock FIFO, or RD_CLK if we have an 
         // independent clock FIFO
         assign RD_CLK_P0_IN       = ((C_VERILOG_IMPL == 0) ? CLK : RD_CLK);
         assign RST_P0_IN          = (C_COMMON_CLOCK == 0) ? rd_rst_i : (C_HAS_RST == 1) ? rst_i : 0;
         assign RD_EN_P0_IN        = (C_FIFO_TYPE != 1) ? rd_en_delayed : rd_en_to_fwft_fifo;
         assign EMPTY_P0_IN        = C_EN_SAFETY_CKT ? fifo_empty_fb : EMPTY_FIFO_OUT;
         assign DATA_P0_IN         = DOUT_FIFO_OUT;
         
         //***********************************************
         // Connect outputs from preload (FWFT) module
         //***********************************************
         assign VALID              = VALID_P0_OUT ;
         assign ALMOST_EMPTY       = ALMOSTEMPTY_P0_OUT;
         assign UNDERFLOW          = UNDERFLOW_P0_OUT ;
         
         assign RD_EN_FIFO_IN      = rd_en_fifo_in;
         
         
         //***********************************************
         // Create DATA_COUNT from First-Word Fall-Through
         // data count
         //***********************************************
         assign DATA_COUNT = (C_USE_FWFT_DATA_COUNT == 0)? DATA_COUNT_FIFO_OUT:
           (C_DATA_COUNT_WIDTH>C_RD_PNTR_WIDTH) ? DATA_COUNT_FWFT[C_RD_PNTR_WIDTH:0] : 
           DATA_COUNT_FWFT[C_RD_PNTR_WIDTH:C_RD_PNTR_WIDTH-C_DATA_COUNT_WIDTH+1];  
         
         //***********************************************
         // Create DATA_COUNT from First-Word Fall-Through
         // data count
         //***********************************************
         always @ (posedge RD_CLK_P0_IN or posedge RST_P0_IN) begin
            if (RST_P0_IN) begin
               EMPTY_P0_OUT_Q       <= 1;
               ALMOSTEMPTY_P0_OUT_Q <= 1;
            end else begin
               EMPTY_P0_OUT_Q       <= #`TCQ empty_p0_out;
//               EMPTY_P0_OUT_Q       <= #`TCQ EMPTY_FIFO_OUT;
               ALMOSTEMPTY_P0_OUT_Q <= #`TCQ ALMOSTEMPTY_P0_OUT;
            end
         end //always
         
         
         //***********************************************
         // logic for common-clock data count when FWFT is selected
         //***********************************************
         initial begin
            SS_FWFT_RD = 1'b0;
            DATA_COUNT_FWFT = 0 ;
            SS_FWFT_WR   = 1'b0 ;
         end //initial
         
         
         //***********************************************
         // common-clock data count is implemented as an
         // up-down counter. SS_FWFT_WR and SS_FWFT_RD
         // are the up/down enables for the counter.
         //***********************************************
         always @ (RD_EN or VALID_P0_OUT or WR_EN or FULL_FIFO_OUT or empty_p0_out) begin
            if (C_VALID_LOW == 1) begin
              SS_FWFT_RD = (C_FIFO_TYPE != 1) ? (RD_EN && ~VALID_P0_OUT) : (~empty_p0_out && RD_EN && ~VALID_P0_OUT) ;
            end else begin
              SS_FWFT_RD = (C_FIFO_TYPE != 1) ? (RD_EN && VALID_P0_OUT) : (~empty_p0_out && RD_EN && VALID_P0_OUT) ;
            end
            SS_FWFT_WR = (WR_EN && (~FULL_FIFO_OUT))  ;
         end 

         //***********************************************
         // common-clock data count is implemented as an
         // up-down counter for FWFT. This always block 
         // calculates the counter.
         //***********************************************
         always @ (posedge RD_CLK_P0_IN or posedge RST_P0_IN) begin
            if (RST_P0_IN) begin
               DATA_COUNT_FWFT      <= 0;
            end else begin
               //if (srst_delayed && (C_HAS_SRST == 1) ) begin
               if ((srst_delayed | wr_rst_busy | rd_rst_busy) && (C_HAS_SRST == 1) ) begin
                  DATA_COUNT_FWFT      <= #`TCQ 0;
               end else begin
                  case ( {SS_FWFT_WR, SS_FWFT_RD})
                    2'b00: DATA_COUNT_FWFT <= #`TCQ DATA_COUNT_FWFT ;
                    2'b01: DATA_COUNT_FWFT <= #`TCQ DATA_COUNT_FWFT - 1 ;
                    2'b10: DATA_COUNT_FWFT <= #`TCQ DATA_COUNT_FWFT + 1 ;
                    2'b11: DATA_COUNT_FWFT <= #`TCQ DATA_COUNT_FWFT ;
                  endcase  
               end //if SRST
            end //IF RST
         end //always

      end endgenerate // : block2

    // AXI Streaming Packet FIFO
    reg  [C_WR_PNTR_WIDTH-1:0]  wr_pkt_count       = 0;
    reg  [C_RD_PNTR_WIDTH-1:0]  rd_pkt_count       = 0;
    reg  [C_RD_PNTR_WIDTH-1:0]  rd_pkt_count_plus1 = 0;
    reg  [C_RD_PNTR_WIDTH-1:0]  rd_pkt_count_reg   = 0;
    reg                         partial_packet     = 0;
    reg                         stage1_eop_d1      = 0;
    reg                         rd_en_fifo_in_d1   = 0;
    reg                         eop_at_stage2      = 0;
    reg                         ram_pkt_empty      = 0;
    reg                         ram_pkt_empty_d1   = 0;

    wire [C_DOUT_WIDTH-1:0]     dout_p0_out;
    wire                        packet_empty_wr;
    wire                        wr_rst_fwft_pkt_fifo;
    wire                        dummy_wr_eop;
    wire                        ram_wr_en_pkt_fifo;
    wire                        wr_eop;
    wire                        ram_rd_en_compare;
    wire                        stage1_eop;
    wire                        pkt_ready_to_read;
    wire                        rd_en_2_stage2;

    // Generate Dummy WR_EOP for partial packet (Only for AXI Streaming)
    // When Packet EMPTY is high, and FIFO is full, then generate the dummy WR_EOP
    // When dummy WR_EOP is high, mask the actual EOP to avoid double increment of
    // write packet count
    generate if (IS_FWFT == 1 && IS_AXIS_PKT_FIFO == 1) begin // gdummy_wr_eop
       always @ (posedge wr_rst_fwft_pkt_fifo or posedge WR_CLK) begin 
          if (wr_rst_fwft_pkt_fifo)
             partial_packet   <= 1'b0;
          else begin
             if (srst_delayed | wr_rst_busy | rd_rst_busy)
                partial_packet <= #`TCQ 1'b0;
             else if (ALMOST_FULL_FIFO_OUT && ram_wr_en_pkt_fifo && packet_empty_wr && (~din_delayed[0]))
                partial_packet <= #`TCQ 1'b1;
             else if (partial_packet && din_delayed[0] && ram_wr_en_pkt_fifo)
                partial_packet <= #`TCQ 1'b0;
          end
        end
    end endgenerate // gdummy_wr_eop

    generate if (IS_FWFT == 1 && IS_PKT_FIFO == 1) begin // gpkt_fifo_fwft
      assign wr_rst_fwft_pkt_fifo = (C_COMMON_CLOCK == 0) ? wr_rst_i : (C_HAS_RST == 1) ? rst_i:1'b0;
      assign dummy_wr_eop = ALMOST_FULL_FIFO_OUT && ram_wr_en_pkt_fifo && packet_empty_wr && (~din_delayed[0]) && (~partial_packet);
      assign packet_empty_wr = (C_COMMON_CLOCK == 1) ? empty_p0_out : pkt_empty_sync[C_SYNCHRONIZER_STAGE-1];
  
      always @ (posedge rst_fwft or posedge RD_CLK_P0_IN) begin 
        if (rst_fwft) begin
          stage1_eop_d1    <= 1'b0;
          rd_en_fifo_in_d1 <= 1'b0;
        end else begin
          if (srst_delayed | wr_rst_busy | rd_rst_busy) begin
            stage1_eop_d1    <= #`TCQ 1'b0;
            rd_en_fifo_in_d1 <= #`TCQ 1'b0;
          end else begin
            stage1_eop_d1    <= #`TCQ stage1_eop;
            rd_en_fifo_in_d1 <= #`TCQ rd_en_fifo_in;
          end
        end
      end
      assign stage1_eop = (rd_en_fifo_in_d1) ? DOUT_FIFO_OUT[0] : stage1_eop_d1;
      assign ram_wr_en_pkt_fifo = wr_en_delayed && (~FULL_FIFO_OUT);
      assign wr_eop = ram_wr_en_pkt_fifo && ((din_delayed[0] && (~partial_packet)) || dummy_wr_eop);
      assign ram_rd_en_compare = stage2_reg_en_i && stage1_eop;


         fifo_generator_v13_1_2_bhv_ver_preload0
           #(
             .C_DOUT_RST_VAL      (C_DOUT_RST_VAL),
             .C_DOUT_WIDTH        (C_DOUT_WIDTH),
             .C_HAS_RST           (C_HAS_RST),
             .C_HAS_SRST          (C_HAS_SRST),
             .C_USE_DOUT_RST      (C_USE_DOUT_RST),
             .C_USE_ECC           (C_USE_ECC),
             .C_USERVALID_LOW     (C_VALID_LOW),
             .C_EN_SAFETY_CKT     (C_EN_SAFETY_CKT),
             .C_USERUNDERFLOW_LOW (C_UNDERFLOW_LOW),
             .C_ENABLE_RST_SYNC   (C_ENABLE_RST_SYNC),
             .C_MEMORY_TYPE       (C_MEMORY_TYPE),
             .C_FIFO_TYPE         (2) // Enable low latency fwft logic
             )
         pkt_fifo_fwft
               (
                .SAFETY_CKT_RD_RST(safety_ckt_rd_rst),
                .RD_CLK           (RD_CLK_P0_IN),
                .RD_RST           (rst_fwft),
                .SRST             (srst_delayed),
                .WR_RST_BUSY      (wr_rst_busy),
                .RD_RST_BUSY      (rd_rst_busy),
                .RD_EN            (rd_en_delayed),
                .FIFOEMPTY        (pkt_ready_to_read),
                .FIFODATA         (dout_fwft),
                .FIFOSBITERR      (sbiterr_fwft),
                .FIFODBITERR      (dbiterr_fwft),
                // Output
                .USERDATA         (dout_p0_out),
                .USERVALID        (),
                .USEREMPTY        (empty_p0_out),
                .USERALMOSTEMPTY  (),
                .USERUNDERFLOW    (),
                .RAMVALID         (),
                .FIFORDEN         (rd_en_2_stage2),
                .USERSBITERR      (SBITERR),
                .USERDBITERR      (DBITERR),
                .STAGE2_REG_EN    (),
                .VALID_STAGES     ()
                );

      assign pkt_ready_to_read  = ~(!(ram_pkt_empty || empty_fwft) && ((valid_stages_i[0] && valid_stages_i[1]) || eop_at_stage2));
      assign rd_en_to_fwft_fifo = ~empty_fwft && rd_en_2_stage2;

      always @ (posedge rst_fwft or posedge RD_CLK_P0_IN) begin 
        if (rst_fwft)
          eop_at_stage2 <= 1'b0;
        else if (stage2_reg_en_i)
          eop_at_stage2 <= #`TCQ stage1_eop;
      end

      //---------------------------------------------------------------------------
      // Write and Read Packet Count
      //---------------------------------------------------------------------------
      always @ (posedge wr_rst_fwft_pkt_fifo or posedge WR_CLK) begin 
         if (wr_rst_fwft_pkt_fifo)
            wr_pkt_count  <= 0;
         else if (srst_delayed  | wr_rst_busy | rd_rst_busy)
            wr_pkt_count  <= #`TCQ 0;
         else if (wr_eop)
            wr_pkt_count  <= #`TCQ wr_pkt_count + 1;
      end
    
    end endgenerate // gpkt_fifo_fwft

    assign DOUT               = (C_FIFO_TYPE != 1) ? dout_fwft : dout_p0_out;
    assign EMPTY              = (C_FIFO_TYPE != 1) ? empty_fwft : empty_p0_out;

    generate if (IS_FWFT == 1 && IS_PKT_FIFO == 1 && C_COMMON_CLOCK == 1) begin // grss_pkt_cnt
      always @ (posedge rst_fwft or posedge RD_CLK_P0_IN) begin 
         if (rst_fwft) begin
            rd_pkt_count       <= 0;
            rd_pkt_count_plus1 <= 1;
         end else if (srst_delayed | wr_rst_busy | rd_rst_busy) begin
            rd_pkt_count       <= #`TCQ 0;
            rd_pkt_count_plus1 <= #`TCQ 1;
         end else if (stage2_reg_en_i && stage1_eop) begin
            rd_pkt_count       <= #`TCQ rd_pkt_count + 1;
            rd_pkt_count_plus1 <= #`TCQ rd_pkt_count_plus1 + 1;
         end
      end

      always @ (posedge rst_fwft or posedge RD_CLK_P0_IN) begin 
         if (rst_fwft) begin
            ram_pkt_empty    <= 1'b1;
            ram_pkt_empty_d1 <= 1'b1;
         end else if (SRST | wr_rst_busy | rd_rst_busy) begin
            ram_pkt_empty    <= #`TCQ 1'b1;
            ram_pkt_empty_d1 <= #`TCQ 1'b1;
         end else if ((rd_pkt_count == wr_pkt_count) && wr_eop) begin
            ram_pkt_empty    <= #`TCQ 1'b0;
            ram_pkt_empty_d1 <= #`TCQ 1'b0;
         end else if (ram_pkt_empty_d1 && rd_en_to_fwft_fifo) begin
            ram_pkt_empty    <= #`TCQ 1'b1;
         end else if ((rd_pkt_count_plus1 == wr_pkt_count) && ~wr_eop && ~ALMOST_FULL_FIFO_OUT && ram_rd_en_compare) begin
            ram_pkt_empty_d1 <= #`TCQ 1'b1;
         end
      end
    end endgenerate //grss_pkt_cnt
    
    localparam SYNC_STAGE_WIDTH = (C_SYNCHRONIZER_STAGE+1)*C_WR_PNTR_WIDTH;
    reg  [SYNC_STAGE_WIDTH-1:0] wr_pkt_count_q = 0;
    reg  [C_WR_PNTR_WIDTH-1:0]  wr_pkt_count_b2g = 0;
    wire [C_WR_PNTR_WIDTH-1:0]  wr_pkt_count_rd;
    generate if (IS_FWFT == 1 && IS_PKT_FIFO == 1 && C_COMMON_CLOCK == 0) begin // gras_pkt_cnt
      // Delay the write packet count in write clock domain to accomodate the binary to gray conversion delay
      always @ (posedge wr_rst_fwft_pkt_fifo or posedge WR_CLK) begin
         if (wr_rst_fwft_pkt_fifo)
            wr_pkt_count_b2g  <= 0;
         else
            wr_pkt_count_b2g  <= #`TCQ wr_pkt_count;
      end

      // Synchronize the delayed write packet count in read domain, and also compensate the gray to binay conversion delay
      always @ (posedge rst_fwft or posedge RD_CLK_P0_IN) begin 
         if (rst_fwft)
            wr_pkt_count_q       <= 0;
         else
            wr_pkt_count_q       <= #`TCQ {wr_pkt_count_q[SYNC_STAGE_WIDTH-C_WR_PNTR_WIDTH-1:0],wr_pkt_count_b2g};
      end

      always @* begin
        if (stage1_eop)
           rd_pkt_count    <= rd_pkt_count_reg + 1;
        else
           rd_pkt_count    <= rd_pkt_count_reg;
      end

      assign wr_pkt_count_rd    = wr_pkt_count_q[SYNC_STAGE_WIDTH-1:SYNC_STAGE_WIDTH-C_WR_PNTR_WIDTH];

      always @ (posedge rst_fwft or posedge RD_CLK_P0_IN) begin 
         if (rst_fwft)
            rd_pkt_count_reg       <= 0;
         else if (rd_en_fifo_in)
            rd_pkt_count_reg       <= #`TCQ rd_pkt_count;
      end

      always @ (posedge rst_fwft or posedge RD_CLK_P0_IN) begin 
         if (rst_fwft) begin
            ram_pkt_empty    <= 1'b1;
            ram_pkt_empty_d1 <= 1'b1;
         end else if (rd_pkt_count != wr_pkt_count_rd) begin
            ram_pkt_empty    <= #`TCQ 1'b0;
            ram_pkt_empty_d1 <= #`TCQ 1'b0;
         end else if (ram_pkt_empty_d1 && rd_en_to_fwft_fifo) begin
            ram_pkt_empty    <= #`TCQ 1'b1;
         end else if ((rd_pkt_count == wr_pkt_count_rd) && stage2_reg_en_i) begin
            ram_pkt_empty_d1 <= #`TCQ 1'b1;
         end
      end

      // Synchronize the empty in write domain
      always @ (posedge wr_rst_fwft_pkt_fifo or posedge WR_CLK) begin
         if (wr_rst_fwft_pkt_fifo)
            pkt_empty_sync  <= 'b1;
         else
            pkt_empty_sync  <= #`TCQ {pkt_empty_sync[C_SYNCHRONIZER_STAGE-2:0], empty_p0_out};
      end

    end endgenerate //gras_pkt_cnt

   generate if (IS_FWFT == 0 || C_FIFO_TYPE == 3) begin : STD_FIFO

     //***********************************************
     // If NOT First-Word Fall-Through, wire the outputs
     // of the internal _ss or _as FIFO directly to the
     // output, and do not instantiate the preload0
     // module.
     //***********************************************

     assign RD_CLK_P0_IN       = 0;
     assign RST_P0_IN          = 0;
     assign RD_EN_P0_IN        = 0;

     assign RD_EN_FIFO_IN      = rd_en_delayed;

     assign DOUT               = DOUT_FIFO_OUT;
     assign DATA_P0_IN         = 0;
     assign VALID              = VALID_FIFO_OUT;
     assign EMPTY              = EMPTY_FIFO_OUT;
     assign ALMOST_EMPTY       = ALMOST_EMPTY_FIFO_OUT;
     assign EMPTY_P0_IN        = 0;
     assign UNDERFLOW          = UNDERFLOW_FIFO_OUT;
     assign DATA_COUNT         = DATA_COUNT_FIFO_OUT;
     assign SBITERR            = sbiterr_fifo_out;
     assign DBITERR            = dbiterr_fifo_out;

   end endgenerate // STD_FIFO

   generate if (IS_FWFT == 1 && C_FIFO_TYPE != 1) begin : NO_PKT_FIFO
     assign empty_p0_out       = empty_fwft;
     assign SBITERR            = sbiterr_fwft;
     assign DBITERR            = dbiterr_fwft;
     assign DOUT               = dout_fwft;
     assign RD_EN_P0_IN        = (C_FIFO_TYPE != 1) ? rd_en_delayed : rd_en_to_fwft_fifo;

   end endgenerate // NO_PKT_FIFO

   //***********************************************
   // Connect user flags to internal signals
   //***********************************************
   
   //If we are using extra logic for the FWFT data count, then override the
   //RD_DATA_COUNT output when we are EMPTY or ALMOST_EMPTY.
   //RD_DATA_COUNT is 0 when EMPTY and 1 when ALMOST_EMPTY.
   generate
      if (C_USE_FWFT_DATA_COUNT==1 && (C_RD_DATA_COUNT_WIDTH>C_RD_PNTR_WIDTH) && (C_USE_EMBEDDED_REG < 3) ) begin : block3
      if (C_COMMON_CLOCK == 0) begin : block_ic
         assign RD_DATA_COUNT = (EMPTY_P0_OUT_Q | RST_P0_IN) ? 0 : (ALMOSTEMPTY_P0_OUT_Q ? 1 : RD_DATA_COUNT_FIFO_OUT);
      end //block_ic
      else begin
         assign RD_DATA_COUNT = RD_DATA_COUNT_FIFO_OUT;
      end 
      end //block3
   endgenerate
   
   //If we are using extra logic for the FWFT data count, then override the
   //RD_DATA_COUNT output when we are EMPTY or ALMOST_EMPTY.
   //Due to asymmetric ports, RD_DATA_COUNT is 0 when EMPTY or ALMOST_EMPTY.
   generate
      if (C_USE_FWFT_DATA_COUNT==1 && (C_RD_DATA_COUNT_WIDTH <=C_RD_PNTR_WIDTH) && (C_USE_EMBEDDED_REG < 3) ) begin : block30
       if (C_COMMON_CLOCK == 0) begin : block_ic
         assign RD_DATA_COUNT = (EMPTY_P0_OUT_Q | RST_P0_IN) ? 0 : (ALMOSTEMPTY_P0_OUT_Q ? 0 : RD_DATA_COUNT_FIFO_OUT);
       end 
       else begin
         assign RD_DATA_COUNT = RD_DATA_COUNT_FIFO_OUT;
        end 
      end //block30
   endgenerate


    
   //If we are using extra logic for the FWFT data count, then override the
   //RD_DATA_COUNT output when we are EMPTY or ALMOST_EMPTY.
   //Due to asymmetric ports, RD_DATA_COUNT is 0 when EMPTY or ALMOST_EMPTY.
   generate
      if (C_USE_FWFT_DATA_COUNT==1 && (C_RD_DATA_COUNT_WIDTH <=C_RD_PNTR_WIDTH) && (C_USE_EMBEDDED_REG == 3) ) begin : block30_both
       if (C_COMMON_CLOCK == 0) begin : block_ic_both
         assign RD_DATA_COUNT = (EMPTY_P0_OUT_Q | RST_P0_IN) ? 0 : (ALMOSTEMPTY_P0_OUT_Q ? 0 : (RD_DATA_COUNT_FIFO_OUT));
       end 
       else begin
         assign RD_DATA_COUNT = RD_DATA_COUNT_FIFO_OUT;
        end 
      end //block30_both
   endgenerate

 generate
      if (C_USE_FWFT_DATA_COUNT==1 && (C_RD_DATA_COUNT_WIDTH>C_RD_PNTR_WIDTH) && (C_USE_EMBEDDED_REG == 3) ) begin : block3_both
      if (C_COMMON_CLOCK == 0) begin : block_ic_both
         assign RD_DATA_COUNT = (EMPTY_P0_OUT_Q | RST_P0_IN) ? 0 : (ALMOSTEMPTY_P0_OUT_Q ? 1 : (RD_DATA_COUNT_FIFO_OUT));
      end //block_ic_both
      else begin
         assign RD_DATA_COUNT = RD_DATA_COUNT_FIFO_OUT;
      end 
      end //block3_both
   endgenerate


   //If we are not using extra logic for the FWFT data count,
   //then connect RD_DATA_COUNT to the RD_DATA_COUNT from the
   //internal FIFO instance  
   generate
      if (C_USE_FWFT_DATA_COUNT==0 ) begin : block31
         assign RD_DATA_COUNT = RD_DATA_COUNT_FIFO_OUT;
      end
   endgenerate

   //Always connect WR_DATA_COUNT to the WR_DATA_COUNT from the internal
   //FIFO instance
   generate
      if (C_USE_FWFT_DATA_COUNT==1) begin : block4
         assign WR_DATA_COUNT = WR_DATA_COUNT_FIFO_OUT;
      end
      else begin : block4
         assign WR_DATA_COUNT = WR_DATA_COUNT_FIFO_OUT;
      end
   endgenerate


   //Connect other flags to the internal FIFO instance
   assign       FULL        = FULL_FIFO_OUT;
   assign       ALMOST_FULL = ALMOST_FULL_FIFO_OUT;
   assign       WR_ACK      = WR_ACK_FIFO_OUT;
   assign       OVERFLOW    = OVERFLOW_FIFO_OUT;
   assign       PROG_FULL   = PROG_FULL_FIFO_OUT;
   assign       PROG_EMPTY  = PROG_EMPTY_FIFO_OUT;


  /**************************************************************************
  * find_log2
  *   Returns the 'log2' value for the input value for the supported ratios
  ***************************************************************************/
  function integer find_log2;
    input integer int_val;
    integer i,j;
    begin
      i = 1;
      j = 0;
      for (i = 1; i < int_val; i = i*2) begin
        j = j + 1;
      end
      find_log2 = j;
    end
  endfunction

   // if an asynchronous FIFO has been selected, display a message that the FIFO
   //   will not be cycle-accurate in simulation
   initial begin
      if (C_IMPLEMENTATION_TYPE == 2) begin
         $display("WARNING: Behavioral models for independent clock FIFO configurations do not model synchronization delays. The behavioral models are functionally correct, and will represent the behavior of the configured FIFO. See the FIFO Generator User Guide for more information.");
      end else if (C_MEMORY_TYPE == 4) begin
         $display("FAILURE : Behavioral models do not support built-in FIFO configurations. Please use post-synthesis or post-implement simulation in Vivado.");
         $finish;
      end

      if (C_WR_PNTR_WIDTH != find_log2(C_WR_DEPTH)) begin
         $display("FAILURE : C_WR_PNTR_WIDTH is not log2 of C_WR_DEPTH.");
         $finish;
      end

      if (C_RD_PNTR_WIDTH != find_log2(C_RD_DEPTH)) begin
         $display("FAILURE : C_RD_PNTR_WIDTH is not log2 of C_RD_DEPTH.");
         $finish;
      end

      if (C_USE_ECC == 1) begin
         if (C_DIN_WIDTH != C_DOUT_WIDTH) begin
            $display("FAILURE : C_DIN_WIDTH and C_DOUT_WIDTH must be equal for ECC configuration.");
            $finish;
         end
         if (C_DIN_WIDTH == 1 && C_ERROR_INJECTION_TYPE > 1) begin
            $display("FAILURE : C_DIN_WIDTH and C_DOUT_WIDTH must be > 1 for double bit error injection.");
            $finish;
         end
      end

   end //initial

  /**************************************************************************
  * Internal reset logic
  **************************************************************************/
  assign wr_rst_i         = (C_HAS_RST == 1 || C_ENABLE_RST_SYNC == 0) ? wr_rst_reg : 0;
  assign rd_rst_i         = (C_HAS_RST == 1 || C_ENABLE_RST_SYNC == 0) ? rd_rst_reg : 0;
  assign rst_i            = C_HAS_RST ? rst_reg : 0;

  wire rst_2_sync;
  wire rst_2_sync_safety = (C_ENABLE_RST_SYNC == 1) ? rst_delayed : RD_RST; 
  wire clk_2_sync = (C_COMMON_CLOCK == 1) ? CLK : WR_CLK;
  wire clk_2_sync_safety = (C_COMMON_CLOCK == 1) ? CLK : RD_CLK;
  localparam RST_SYNC_STAGES = (C_EN_SAFETY_CKT == 0) ? C_SYNCHRONIZER_STAGE :
                               (C_COMMON_CLOCK == 1) ? 3 : C_SYNCHRONIZER_STAGE+2;
  reg  [RST_SYNC_STAGES-1:0] wrst_reg    = {RST_SYNC_STAGES{1'b0}};
  reg  [RST_SYNC_STAGES-1:0] rrst_reg    = {RST_SYNC_STAGES{1'b0}};
  reg  [RST_SYNC_STAGES-1:0] arst_sync_q = {RST_SYNC_STAGES{1'b0}};
  reg  [RST_SYNC_STAGES-1:0] wrst_q      = {RST_SYNC_STAGES{1'b0}};
  reg  [RST_SYNC_STAGES-1:0] rrst_q      = {RST_SYNC_STAGES{1'b0}};
  reg  [RST_SYNC_STAGES-1:0] rrst_wr     = {RST_SYNC_STAGES{1'b0}};
  reg  [RST_SYNC_STAGES-1:0] wrst_ext    = {RST_SYNC_STAGES{1'b0}};
  reg  [1:0] wrst_cc  = {2{1'b0}};
  reg  [1:0] rrst_cc  = {2{1'b0}};

  generate 
      if (C_EN_SAFETY_CKT == 1 && C_INTERFACE_TYPE == 0) begin : grst_safety_ckt
         reg[1:0] rst_d1_safety                  =1;
         reg[1:0] rst_d2_safety                  =1;
         reg[1:0] rst_d3_safety                  =1;
         reg[1:0] rst_d4_safety                  =1;
         reg[1:0] rst_d5_safety                  =1;
         reg[1:0] rst_d6_safety                  =1;
         reg[1:0] rst_d7_safety                  =1;
       always@(posedge rst_2_sync_safety or posedge clk_2_sync_safety) begin : prst
             if (rst_2_sync_safety == 1'b1) begin
                 rst_d1_safety <= 1'b1;
                 rst_d2_safety <= 1'b1;
                 rst_d3_safety <= 1'b1;
                 rst_d4_safety <= 1'b1;
                 rst_d5_safety <= 1'b1;
                 rst_d6_safety <= 1'b1;
                 rst_d7_safety <= 1'b1;
              end
              else begin
                 rst_d1_safety <= #`TCQ 1'b0;
                 rst_d2_safety <= #`TCQ rst_d1_safety;
                 rst_d3_safety <= #`TCQ rst_d2_safety;
                 rst_d4_safety <= #`TCQ rst_d3_safety;
                 rst_d5_safety <= #`TCQ rst_d4_safety;
                 rst_d6_safety <= #`TCQ rst_d5_safety;
                 rst_d7_safety <= #`TCQ rst_d6_safety;
              end //if
              end //prst
        always@(posedge rst_d7_safety or posedge WR_EN) begin : assert_safety
              if(rst_d7_safety == 1 && WR_EN == 1) begin 
              $display("WARNING:A write attempt has been made within the 7 clock cycles of reset de-assertion. This can lead to data discrepancy when safety circuit is enabled."); 
              
              end //if
              end //always
        end // grst_safety_ckt
  endgenerate     
     
// if (C_EN_SAFET_CKT == 1)
// assertion:the reset shud be atleast 3 cycles wide. 

  generate
    reg  safety_ckt_wr_rst_i  = 1'b0;
      if (C_ENABLE_RST_SYNC == 0) begin : gnrst_sync
        always @* begin
          wr_rst_reg <= wr_rst_delayed;
          rd_rst_reg <= rd_rst_delayed;
          rst_reg    <= 1'b0;
          srst_reg    <= 1'b0;
        end
        assign rst_2_sync  = wr_rst_delayed;
        assign wr_rst_busy = C_EN_SAFETY_CKT ? wr_rst_delayed : 1'b0;
        assign rd_rst_busy = C_EN_SAFETY_CKT ? rd_rst_delayed : 1'b0;
        assign safety_ckt_wr_rst = C_EN_SAFETY_CKT ? wr_rst_delayed : 1'b0;
        assign safety_ckt_rd_rst = C_EN_SAFETY_CKT ? rd_rst_delayed : 1'b0;
      // end : gnrst_sync
      end else if (C_HAS_RST == 1 && C_COMMON_CLOCK == 0) begin : g7s_ic_rst
        reg  fifo_wrst_done = 1'b0;
        reg  fifo_rrst_done = 1'b0;
        reg  sckt_wrst_i    = 1'b0;
        reg  sckt_wrst_i_q  = 1'b0;
        reg  rd_rst_active   = 1'b0;
        reg  rd_rst_middle   = 1'b0;
        reg  sckt_rd_rst_d1  = 1'b0;
        reg  [1:0] rst_delayed_ic_w = 2'h0;
        wire rst_delayed_ic_w_i;
        reg  [1:0] rst_delayed_ic_r = 2'h0;
        wire rst_delayed_ic_r_i;
        wire arst_sync_rst;
        wire fifo_rst_done;
        wire fifo_rst_active;
        assign wr_rst_comb      = !wr_rst_asreg_d2 && wr_rst_asreg;
        assign rd_rst_comb      = C_EN_SAFETY_CKT ? (!rd_rst_asreg_d2 && rd_rst_asreg) || rd_rst_active : !rd_rst_asreg_d2 && rd_rst_asreg;
        assign rst_2_sync       = rst_delayed_ic_w_i;
        assign arst_sync_rst    = arst_sync_q[RST_SYNC_STAGES-1];
        assign wr_rst_busy      = C_EN_SAFETY_CKT ? |arst_sync_q[RST_SYNC_STAGES-1:1] | fifo_rst_active : 1'b0;
        assign rd_rst_busy      = C_EN_SAFETY_CKT ? safety_ckt_rd_rst : 1'b0;
        assign fifo_rst_done    = fifo_wrst_done & fifo_rrst_done;
        assign fifo_rst_active  = sckt_wrst_i | wrst_ext[RST_SYNC_STAGES-1] | rrst_wr[RST_SYNC_STAGES-1];

        always @(posedge WR_CLK or posedge rst_delayed) begin
          if (rst_delayed == 1'b1 && C_HAS_RST)
            rst_delayed_ic_w <= 2'b11;
          else
            rst_delayed_ic_w <= #`TCQ {rst_delayed_ic_w[0],1'b0};
        end
        assign rst_delayed_ic_w_i = rst_delayed_ic_w[1];

        always @(posedge RD_CLK or posedge rst_delayed) begin
          if (rst_delayed == 1'b1 && C_HAS_RST)
            rst_delayed_ic_r <= 2'b11;
          else
            rst_delayed_ic_r <= #`TCQ {rst_delayed_ic_r[0],1'b0};
        end
        assign rst_delayed_ic_r_i = rst_delayed_ic_r[1];

        always @(posedge WR_CLK) begin
          sckt_wrst_i_q       <= #`TCQ sckt_wrst_i;
          sckt_wr_rst_i_q     <= #`TCQ wr_rst_busy;
          safety_ckt_wr_rst_i <= #`TCQ sckt_wrst_i | wr_rst_busy | sckt_wr_rst_i_q;
          if (arst_sync_rst && ~fifo_rst_active)
            sckt_wrst_i <= #`TCQ 1'b1;
          else if (sckt_wrst_i && fifo_rst_done)
              sckt_wrst_i <= #`TCQ 1'b0;
          else
            sckt_wrst_i <= #`TCQ sckt_wrst_i;

          if (rrst_wr[RST_SYNC_STAGES-2] & ~rrst_wr[RST_SYNC_STAGES-1])
            fifo_rrst_done <= #`TCQ 1'b1;
          else if (fifo_rst_done)
            fifo_rrst_done <= #`TCQ 1'b0;
          else
            fifo_rrst_done <= #`TCQ fifo_rrst_done;

          if (wrst_ext[RST_SYNC_STAGES-2] & ~wrst_ext[RST_SYNC_STAGES-1])
            fifo_wrst_done <= #`TCQ 1'b1;
          else if (fifo_rst_done)
            fifo_wrst_done <= #`TCQ 1'b0;
          else
            fifo_wrst_done <= #`TCQ fifo_wrst_done;
        end   

        always @(posedge WR_CLK or posedge rst_delayed_ic_w_i) begin
          if (rst_delayed_ic_w_i == 1'b1) begin
            wr_rst_asreg <= 1'b1;
          end else begin
            if (wr_rst_asreg_d1 == 1'b1) begin
              wr_rst_asreg <= #`TCQ 1'b0;
            end else begin
              wr_rst_asreg <= #`TCQ wr_rst_asreg;
            end
          end    
        end   

        always @(posedge WR_CLK or posedge rst_delayed) begin
          if (rst_delayed == 1'b1) begin
            wr_rst_asreg <= 1'b1;
          end else begin
            if (wr_rst_asreg_d1 == 1'b1) begin
              wr_rst_asreg <= #`TCQ 1'b0;
            end else begin
              wr_rst_asreg <= #`TCQ wr_rst_asreg;
            end
          end    
        end   

        always @(posedge WR_CLK) begin
          wrst_reg    <= #`TCQ {wrst_reg[RST_SYNC_STAGES-2:0],wr_rst_asreg};
          wrst_ext    <= #`TCQ {wrst_ext[RST_SYNC_STAGES-2:0],sckt_wrst_i};
          rrst_wr     <= #`TCQ {rrst_wr[RST_SYNC_STAGES-2:0],safety_ckt_rd_rst};
          arst_sync_q <= #`TCQ {arst_sync_q[RST_SYNC_STAGES-2:0],rst_delayed_ic_w_i};
        end

        assign wr_rst_asreg_d1 = wrst_reg[RST_SYNC_STAGES-2];
        assign wr_rst_asreg_d2 = C_EN_SAFETY_CKT ? wrst_reg[RST_SYNC_STAGES-1] : wrst_reg[1];
        assign safety_ckt_wr_rst = C_EN_SAFETY_CKT ? safety_ckt_wr_rst_i : 1'b0;

        always @(posedge WR_CLK or posedge wr_rst_comb) begin
          if (wr_rst_comb == 1'b1) begin
            wr_rst_reg <= 1'b1;
          end else begin
            wr_rst_reg <= #`TCQ 1'b0;
          end    
        end   

        always @(posedge RD_CLK or posedge rst_delayed_ic_r_i) begin
          if (rst_delayed_ic_r_i == 1'b1) begin
            rd_rst_asreg  <= 1'b1;
          end else begin
            if (rd_rst_asreg_d1 == 1'b1) begin
              rd_rst_asreg <= #`TCQ 1'b0;
            end else begin
              rd_rst_asreg <= #`TCQ rd_rst_asreg;
            end
          end    
        end   

        always @(posedge RD_CLK) begin
          rrst_reg        <= #`TCQ {rrst_reg[RST_SYNC_STAGES-2:0],rd_rst_asreg};
          rrst_q          <= #`TCQ {rrst_q[RST_SYNC_STAGES-2:0],sckt_wrst_i};
          rrst_cc         <= #`TCQ {rrst_cc[0],rd_rst_asreg_d2};
          sckt_rd_rst_d1  <= #`TCQ safety_ckt_rd_rst;
          if (!rd_rst_middle && rrst_reg[1] && !rrst_reg[2]) begin
            rd_rst_active <= #`TCQ 1'b1;
            rd_rst_middle <= #`TCQ 1'b1;
          end else if (safety_ckt_rd_rst)
            rd_rst_active <= #`TCQ 1'b0;
          else if (sckt_rd_rst_d1 && !safety_ckt_rd_rst)
            rd_rst_middle <= #`TCQ 1'b0;
        end
        assign rd_rst_asreg_d1 = rrst_reg[RST_SYNC_STAGES-2];
        assign rd_rst_asreg_d2 = C_EN_SAFETY_CKT ? rrst_reg[RST_SYNC_STAGES-1] : rrst_reg[1];
        assign safety_ckt_rd_rst = C_EN_SAFETY_CKT ? rrst_q[2] : 1'b0;

        always @(posedge RD_CLK or posedge rd_rst_comb) begin
          if (rd_rst_comb == 1'b1) begin
            rd_rst_reg <= 1'b1;
          end else begin
            rd_rst_reg <= #`TCQ 1'b0;
          end    
        end   
      // end : g7s_ic_rst
      end else if (C_HAS_RST == 1 && C_COMMON_CLOCK == 1) begin : g7s_cc_rst
        reg  [1:0] rst_delayed_cc   = 2'h0;
        wire rst_delayed_cc_i;
        assign rst_comb    = !rst_asreg_d2 && rst_asreg;     
        assign rst_2_sync  = rst_delayed_cc_i;
        assign wr_rst_busy = C_EN_SAFETY_CKT ? |arst_sync_q[RST_SYNC_STAGES-1:1] | wrst_cc[1] : 1'b0;
        assign rd_rst_busy = C_EN_SAFETY_CKT ? arst_sync_q[1] | arst_sync_q[RST_SYNC_STAGES-1] | wrst_cc[1] : 1'b0;
 
        always @(posedge CLK or posedge rst_delayed) begin
          if (rst_delayed == 1'b1)
            rst_delayed_cc <= 2'b11;
          else
            rst_delayed_cc <= #`TCQ {rst_delayed_cc,1'b0};
        end   
        assign rst_delayed_cc_i = rst_delayed_cc[1];
 
        always @(posedge CLK or posedge rst_delayed_cc_i) begin
          if (rst_delayed_cc_i == 1'b1) begin
            rst_asreg <= 1'b1;
          end else begin
            if (rst_asreg_d1 == 1'b1) begin
              rst_asreg <= #`TCQ 1'b0;
            end else begin
              rst_asreg <= #`TCQ rst_asreg;
            end
          end    
        end   
        
        always @(posedge CLK) begin
          wrst_reg <= #`TCQ {wrst_reg[RST_SYNC_STAGES-2:0],rst_asreg};
          wrst_cc  <= #`TCQ {wrst_cc[0],arst_sync_q[RST_SYNC_STAGES-1]};
          sckt_wr_rst_i_q     <= #`TCQ wr_rst_busy;
          safety_ckt_wr_rst_i <= #`TCQ wrst_cc[1] | wr_rst_busy | sckt_wr_rst_i_q;
          arst_sync_q <= #`TCQ {arst_sync_q[RST_SYNC_STAGES-2:0],rst_delayed_cc_i};
        end
        assign rst_asreg_d1 = wrst_reg[RST_SYNC_STAGES-2];
        assign rst_asreg_d2 = C_EN_SAFETY_CKT ? wrst_reg[RST_SYNC_STAGES-1] : wrst_reg[1];
        assign safety_ckt_wr_rst = C_EN_SAFETY_CKT ? safety_ckt_wr_rst_i : 1'b0;
        assign safety_ckt_rd_rst = C_EN_SAFETY_CKT ? safety_ckt_wr_rst_i : 1'b0;

        always @(posedge CLK or posedge rst_comb) begin
          if (rst_comb == 1'b1) begin
            rst_reg <= 1'b1;
          end else begin
            rst_reg <= #`TCQ 1'b0;
          end    
        end   
      // end : g7s_cc_rst
      end else if (IS_8SERIES == 1 && C_HAS_SRST == 1 && C_COMMON_CLOCK == 1) begin : g8s_cc_rst
        assign wr_rst_busy = (C_MEMORY_TYPE != 4) ? rst_reg : rst_active_i;
        assign rd_rst_busy = rst_reg;
        assign rst_2_sync = srst_delayed;
        always @* rst_full_ff_i  <= rst_reg;
        always @* rst_full_gen_i <= C_FULL_FLAGS_RST_VAL == 1 ? rst_active_i : 0;
        assign safety_ckt_wr_rst = C_EN_SAFETY_CKT ? rst_reg | wr_rst_busy | sckt_wr_rst_i_q : 1'b0;
        assign safety_ckt_rd_rst = C_EN_SAFETY_CKT ? rst_reg | wr_rst_busy | sckt_wr_rst_i_q : 1'b0;

        always @(posedge CLK) begin
          rst_delayed_d1 <= #`TCQ srst_delayed;
          rst_delayed_d2 <= #`TCQ rst_delayed_d1;
          sckt_wr_rst_i_q <= #`TCQ wr_rst_busy;
          if (rst_reg || rst_delayed_d2) begin
            rst_active_i <= #`TCQ 1'b1;
          end else begin
            rst_active_i <= #`TCQ rst_reg;
          end    
        end   
        always @(posedge CLK) begin
          if (~rst_reg && srst_delayed) begin
             rst_reg <= #`TCQ 1'b1;
           end else if (rst_reg) begin
             rst_reg <= #`TCQ 1'b0;
           end else begin
             rst_reg <= #`TCQ rst_reg;
           end    
        end   
      // end : g8s_cc_rst
      end else begin 
        assign wr_rst_busy = 1'b0;
        assign rd_rst_busy = 1'b0;
        assign safety_ckt_wr_rst = 1'b0;
        assign safety_ckt_rd_rst = 1'b0;
      end
  endgenerate 

  generate
    if ((C_HAS_RST == 1 || C_HAS_SRST == 1 || C_ENABLE_RST_SYNC == 0) && C_FULL_FLAGS_RST_VAL == 1) begin : grstd1
    // RST_FULL_GEN replaces the reset falling edge detection used to de-assert
    // FULL, ALMOST_FULL & PROG_FULL flags if C_FULL_FLAGS_RST_VAL = 1.

    // RST_FULL_FF goes to the reset pin of the final flop of FULL, ALMOST_FULL &
    // PROG_FULL
      reg rst_d1 = 1'b0;
      reg rst_d2 = 1'b0;
      reg rst_d3 = 1'b0;
      reg rst_d4 = 1'b0;
      reg rst_d5 = 1'b0;

      always @ (posedge rst_2_sync or posedge clk_2_sync) begin
        if (rst_2_sync) begin
          rst_d1         <= 1'b1;
          rst_d2         <= 1'b1;
          rst_d3         <= 1'b1;
          rst_d4         <= 1'b1;
        end else begin
          if (srst_delayed) begin
            rst_d1         <= #`TCQ 1'b1;
            rst_d2         <= #`TCQ 1'b1;
            rst_d3         <= #`TCQ 1'b1;
            rst_d4         <= #`TCQ 1'b1;
          end else begin
            rst_d1         <= #`TCQ wr_rst_busy;
            rst_d2         <= #`TCQ rst_d1;
            rst_d3         <= #`TCQ rst_d2 | safety_ckt_wr_rst;
            rst_d4         <= #`TCQ rst_d3;
          end
        end
      end

      always @* rst_full_ff_i  <= (C_HAS_SRST == 0) ? rst_d2 : 1'b0 ;
      always @* rst_full_gen_i <= rst_d3;

    end else if ((C_HAS_RST == 1 || C_HAS_SRST == 1 || C_ENABLE_RST_SYNC == 0) && C_FULL_FLAGS_RST_VAL == 0) begin : gnrst_full
      always @* rst_full_ff_i  <= (C_COMMON_CLOCK == 0) ? wr_rst_i : rst_i;
    end
  endgenerate // grstd1

endmodule //fifo_generator_v13_1_2_conv_ver


module fifo_generator_v13_1_2_sync_stage
  #(
    parameter  C_WIDTH          = 10
   )
   (
    input                     RST,
    input                     CLK,
    input       [C_WIDTH-1:0] DIN,
    output reg  [C_WIDTH-1:0] DOUT = 0
   );
   always @ (posedge RST or posedge CLK) begin
     if (RST)
       DOUT <= 0;
     else
       DOUT <= #`TCQ DIN;
   end
endmodule // fifo_generator_v13_1_2_sync_stage

/*******************************************************************************
 * Declaration of Independent-Clocks FIFO Module
 ******************************************************************************/
module fifo_generator_v13_1_2_bhv_ver_as
   
  /***************************************************************************
   * Declare user parameters and their defaults
   ***************************************************************************/
  #(
    parameter  C_FAMILY                       = "virtex7",
    parameter  C_DATA_COUNT_WIDTH             = 2,
    parameter  C_DIN_WIDTH                    = 8,
    parameter  C_DOUT_RST_VAL                 = "",
    parameter  C_DOUT_WIDTH                   = 8,
    parameter  C_FULL_FLAGS_RST_VAL           = 1,
    parameter  C_HAS_ALMOST_EMPTY             = 0,
    parameter  C_HAS_ALMOST_FULL              = 0,
    parameter  C_HAS_DATA_COUNT               = 0,
    parameter  C_HAS_OVERFLOW                 = 0,
    parameter  C_HAS_RD_DATA_COUNT            = 0,
    parameter  C_HAS_RST                      = 0,
    parameter  C_HAS_UNDERFLOW                = 0,
    parameter  C_HAS_VALID                    = 0,
    parameter  C_HAS_WR_ACK                   = 0,
    parameter  C_HAS_WR_DATA_COUNT            = 0,
    parameter  C_IMPLEMENTATION_TYPE          = 0,
    parameter  C_MEMORY_TYPE                  = 1,
    parameter  C_OVERFLOW_LOW                 = 0,
    parameter  C_PRELOAD_LATENCY              = 1,
    parameter  C_PRELOAD_REGS                 = 0,
    parameter  C_PROG_EMPTY_THRESH_ASSERT_VAL = 0,
    parameter  C_PROG_EMPTY_THRESH_NEGATE_VAL = 0,
    parameter  C_PROG_EMPTY_TYPE              = 0,
    parameter  C_PROG_FULL_THRESH_ASSERT_VAL  = 0,
    parameter  C_PROG_FULL_THRESH_NEGATE_VAL  = 0,
    parameter  C_PROG_FULL_TYPE               = 0,
    parameter  C_RD_DATA_COUNT_WIDTH          = 2,
    parameter  C_RD_DEPTH                     = 256,
    parameter  C_RD_PNTR_WIDTH                = 8,
    parameter  C_UNDERFLOW_LOW                = 0,
    parameter  C_USE_DOUT_RST                 = 0,
    parameter  C_USE_EMBEDDED_REG             = 0,
    parameter  C_EN_SAFETY_CKT                = 0,
    parameter  C_USE_FWFT_DATA_COUNT          = 0,
    parameter  C_VALID_LOW                    = 0,
    parameter  C_WR_ACK_LOW                   = 0,
    parameter  C_WR_DATA_COUNT_WIDTH          = 2,
    parameter  C_WR_DEPTH                     = 256,
    parameter  C_WR_PNTR_WIDTH                = 8,
    parameter  C_USE_ECC                      = 0, 
    parameter  C_ENABLE_RST_SYNC              = 1,
    parameter  C_ERROR_INJECTION_TYPE         = 0,
    parameter  C_SYNCHRONIZER_STAGE           = 2 
   )

  /***************************************************************************
   * Declare Input and Output Ports
   ***************************************************************************/
  (
   input                                         SAFETY_CKT_WR_RST,
   input                                         SAFETY_CKT_RD_RST,
   input       [C_DIN_WIDTH-1:0]                 DIN,
   input       [C_RD_PNTR_WIDTH-1:0]             PROG_EMPTY_THRESH,
   input       [C_RD_PNTR_WIDTH-1:0]             PROG_EMPTY_THRESH_ASSERT,
   input       [C_RD_PNTR_WIDTH-1:0]             PROG_EMPTY_THRESH_NEGATE,
   input       [C_WR_PNTR_WIDTH-1:0]             PROG_FULL_THRESH,
   input       [C_WR_PNTR_WIDTH-1:0]             PROG_FULL_THRESH_ASSERT,
   input       [C_WR_PNTR_WIDTH-1:0]             PROG_FULL_THRESH_NEGATE,
   input                                         RD_CLK,
   input                                         RD_EN,
   input                                         RD_EN_USER,
   input                                         RST,
   input                                         RST_FULL_GEN,
   input                                         RST_FULL_FF,
   input                                         WR_RST,
   input                                         RD_RST,
   input                                         WR_CLK,
   input                                         WR_EN,
   input                                         INJECTDBITERR,
   input                                         INJECTSBITERR,
   input                                         USER_EMPTY_FB,
   input                                         fab_read_data_valid_i,
   input                                         read_data_valid_i,
   input                                         ram_valid_i,
   output reg                                    ALMOST_EMPTY = 1'b1,
   output reg                                    ALMOST_FULL = C_FULL_FLAGS_RST_VAL,
   output      [C_DOUT_WIDTH-1:0]                DOUT,
   output reg                                    EMPTY = 1'b1,
   output reg                                    EMPTY_FB = 1'b1,
   output reg                                    FULL = C_FULL_FLAGS_RST_VAL,
   output                                        OVERFLOW,
   output                                        PROG_EMPTY,
   output                                        PROG_FULL,
   output                                        VALID,
   output      [C_RD_DATA_COUNT_WIDTH-1:0]       RD_DATA_COUNT,
   output                                        UNDERFLOW,
   output                                        WR_ACK,
   output      [C_WR_DATA_COUNT_WIDTH-1:0]       WR_DATA_COUNT,
   output                                        SBITERR,
   output                                        DBITERR
  );


   reg  [C_RD_PNTR_WIDTH:0] rd_data_count_int = 0;
   reg  [C_WR_PNTR_WIDTH:0] wr_data_count_int = 0;
   reg  [C_WR_PNTR_WIDTH:0] wdc_fwft_ext_as = 0;
   
  
   /***************************************************************************
    * Parameters used as constants
    **************************************************************************/
  localparam IS_8SERIES         = (C_FAMILY == "virtexu" || C_FAMILY == "kintexu" || C_FAMILY == "artixu" || C_FAMILY == "virtexuplus" || C_FAMILY == "zynquplus" || C_FAMILY == "kintexuplus") ? 1 : 0;
   //When RST is present, set FULL reset value to '1'.
   //If core has no RST, make sure FULL powers-on as '0'.
   localparam C_DEPTH_RATIO_WR =  
      (C_WR_DEPTH>C_RD_DEPTH) ? (C_WR_DEPTH/C_RD_DEPTH) : 1;
   localparam C_DEPTH_RATIO_RD =  
      (C_RD_DEPTH>C_WR_DEPTH) ? (C_RD_DEPTH/C_WR_DEPTH) : 1;
   localparam C_FIFO_WR_DEPTH = C_WR_DEPTH - 1;
   localparam C_FIFO_RD_DEPTH = C_RD_DEPTH - 1;

   //  C_DEPTH_RATIO_WR | C_DEPTH_RATIO_RD | C_PNTR_WIDTH    | EXTRA_WORDS_DC
   //  -----------------|------------------|-----------------|---------------
   //  1                | 8                | C_RD_PNTR_WIDTH | 2
   //  1                | 4                | C_RD_PNTR_WIDTH | 2
   //  1                | 2                | C_RD_PNTR_WIDTH | 2
   //  1                | 1                | C_WR_PNTR_WIDTH | 2
   //  2                | 1                | C_WR_PNTR_WIDTH | 4
   //  4                | 1                | C_WR_PNTR_WIDTH | 8
   //  8                | 1                | C_WR_PNTR_WIDTH | 16
   
   localparam C_PNTR_WIDTH  = (C_WR_PNTR_WIDTH>=C_RD_PNTR_WIDTH) ? C_WR_PNTR_WIDTH : C_RD_PNTR_WIDTH;
   wire [C_PNTR_WIDTH:0] EXTRA_WORDS_DC = (C_DEPTH_RATIO_WR == 1) ? 2 : (2 * C_DEPTH_RATIO_WR/C_DEPTH_RATIO_RD);

   localparam [31:0] reads_per_write = C_DIN_WIDTH/C_DOUT_WIDTH;
   
   localparam [31:0] log2_reads_per_write = log2_val(reads_per_write);
   
   localparam [31:0] writes_per_read = C_DOUT_WIDTH/C_DIN_WIDTH;
   
   localparam [31:0] log2_writes_per_read = log2_val(writes_per_read);



   /**************************************************************************
    * FIFO Contents Tracking and Data Count Calculations
    *************************************************************************/
   
   // Memory which will be used to simulate a FIFO
   reg [C_DIN_WIDTH-1:0] memory[C_WR_DEPTH-1:0];
   // Local parameters used to determine whether to inject ECC error or not
   localparam SYMMETRIC_PORT = (C_DIN_WIDTH == C_DOUT_WIDTH) ? 1 : 0;
   localparam ERR_INJECTION = (C_ERROR_INJECTION_TYPE != 0) ? 1 : 0;
   localparam C_USE_ECC_1 = (C_USE_ECC == 1 || C_USE_ECC ==2) ? 1:0;
   localparam ENABLE_ERR_INJECTION = C_USE_ECC_1 && SYMMETRIC_PORT && ERR_INJECTION;
   // Array that holds the error injection type (single/double bit error) on 
   // a specific write operation, which is returned on read to corrupt the
   // output data.
   reg [1:0] ecc_err[C_WR_DEPTH-1:0];

   //The amount of data stored in the FIFO at any time is given
   // by num_wr_bits (in the WR_CLK domain) and num_rd_bits (in the RD_CLK
   // domain.
   //num_wr_bits is calculated by considering the total words in the FIFO,
   // and the state of the read pointer (which may not have yet crossed clock
   // domains.)
   //num_rd_bits is calculated by considering the total words in the FIFO,
   // and the state of the write pointer (which may not have yet crossed clock
   // domains.)
   reg [31:0]  num_wr_bits;
   reg [31:0]  num_rd_bits;
   reg [31:0]  next_num_wr_bits;
   reg [31:0]  next_num_rd_bits;

   //The write pointer - tracks write operations
   // (Works opposite to core: wr_ptr is a DOWN counter)
   reg  [31:0]                 wr_ptr;
   reg  [C_WR_PNTR_WIDTH-1:0]  wr_pntr = 0; // UP counter: Rolls back to 0 when reaches to max value.
   reg  [C_WR_PNTR_WIDTH-1:0]  wr_pntr_rd1    = 0;
   reg  [C_WR_PNTR_WIDTH-1:0]  wr_pntr_rd2    = 0;
   reg  [C_WR_PNTR_WIDTH-1:0]  wr_pntr_rd3    = 0;
   wire [C_RD_PNTR_WIDTH-1:0]  adj_wr_pntr_rd;
   reg  [C_WR_PNTR_WIDTH-1:0]  wr_pntr_rd     = 0;
   wire                        wr_rst_i = WR_RST;
   reg                         wr_rst_d1      =0;

   //The read pointer - tracks read operations
   // (rd_ptr Works opposite to core: rd_ptr is a DOWN counter)
   reg  [31:0]                 rd_ptr;
   reg  [C_RD_PNTR_WIDTH-1:0]  rd_pntr = 0; // UP counter: Rolls back to 0 when reaches to max value.
   reg  [C_RD_PNTR_WIDTH-1:0]  rd_pntr_wr1 = 0;
   reg  [C_RD_PNTR_WIDTH-1:0]  rd_pntr_wr2 = 0;
   reg  [C_RD_PNTR_WIDTH-1:0]  rd_pntr_wr3 = 0;
   reg  [C_RD_PNTR_WIDTH-1:0]  rd_pntr_wr4 = 0;
   wire [C_WR_PNTR_WIDTH-1:0]  adj_rd_pntr_wr;
   reg  [C_RD_PNTR_WIDTH-1:0]  rd_pntr_wr  = 0;
   wire                        rd_rst_i = RD_RST;
   wire                        ram_rd_en;
   wire                        empty_int;
   wire                        almost_empty_int;
   wire                        ram_wr_en;
   wire                        full_int;
   wire                        almost_full_int;
   reg                         ram_rd_en_d1 = 1'b0;
   reg                         fab_rd_en_d1 = 1'b0;



   // Delayed ram_rd_en is needed only for STD Embedded register option
   generate
     if (C_PRELOAD_LATENCY == 2) begin : grd_d
       always @ (posedge RD_CLK or posedge rd_rst_i) begin
         if (rd_rst_i)
           ram_rd_en_d1 <= 1'b0;
         else
           ram_rd_en_d1 <= #`TCQ ram_rd_en;
       end
     end
   endgenerate
   
    generate
     if (C_PRELOAD_LATENCY == 2 && C_USE_EMBEDDED_REG == 3) begin : grd_d1
       always @ (posedge RD_CLK or posedge rd_rst_i) begin
         if (rd_rst_i)
           ram_rd_en_d1 <= 1'b0;
         else
           ram_rd_en_d1 <= #`TCQ ram_rd_en;
           fab_rd_en_d1 <= #`TCQ ram_rd_en_d1;
       end
     end
   endgenerate

  

   // Write pointer adjustment based on pointers width for EMPTY/ALMOST_EMPTY generation
   generate
     if (C_RD_PNTR_WIDTH > C_WR_PNTR_WIDTH) begin : rdg // Read depth greater than write depth
       assign adj_wr_pntr_rd[C_RD_PNTR_WIDTH-1:C_RD_PNTR_WIDTH-C_WR_PNTR_WIDTH] = wr_pntr_rd;
       assign adj_wr_pntr_rd[C_RD_PNTR_WIDTH-C_WR_PNTR_WIDTH-1:0] = 0;
     end else begin : rdl // Read depth lesser than or equal to write depth
       assign adj_wr_pntr_rd = wr_pntr_rd[C_WR_PNTR_WIDTH-1:C_WR_PNTR_WIDTH-C_RD_PNTR_WIDTH];
     end
   endgenerate

   // Generate Empty and Almost Empty
  // ram_rd_en used to determine EMPTY should depend on the EMPTY.
   assign ram_rd_en        = RD_EN & !EMPTY;
   assign empty_int        = ((adj_wr_pntr_rd == rd_pntr) || (ram_rd_en && (adj_wr_pntr_rd == (rd_pntr+1'h1))));
   assign almost_empty_int = ((adj_wr_pntr_rd == (rd_pntr+1'h1)) || (ram_rd_en && (adj_wr_pntr_rd == (rd_pntr+2'h2))));

   // Register Empty and Almost Empty
   always @ (posedge RD_CLK or posedge rd_rst_i)
     begin
       if (rd_rst_i) begin
         EMPTY             <= 1'b1;
         ALMOST_EMPTY      <= 1'b1;
         rd_data_count_int <= {C_RD_PNTR_WIDTH{1'b0}};
       end else begin
         rd_data_count_int <= #`TCQ {(adj_wr_pntr_rd[C_RD_PNTR_WIDTH-1:0] - rd_pntr[C_RD_PNTR_WIDTH-1:0]), 1'b0};

         if (empty_int)
           EMPTY           <= #`TCQ 1'b1;
         else
           EMPTY           <= #`TCQ 1'b0;

         if (!EMPTY) begin
           if (almost_empty_int)
             ALMOST_EMPTY  <= #`TCQ 1'b1;
           else
             ALMOST_EMPTY  <= #`TCQ 1'b0;
         end
       end // rd_rst_i
     end // always
   always @ (posedge RD_CLK or posedge rd_rst_i)
     begin
       if (rd_rst_i && C_EN_SAFETY_CKT == 0) begin
         EMPTY_FB     <= 1'b1;
       end else begin
         if (SAFETY_CKT_RD_RST && C_EN_SAFETY_CKT)
           EMPTY_FB   <= #`TCQ 1'b1;
         else if (empty_int)
           EMPTY_FB   <= #`TCQ 1'b1;
         else
           EMPTY_FB   <= #`TCQ 1'b0;
       end // rd_rst_i
     end // always

   // Read pointer adjustment based on pointers width for EMPTY/ALMOST_EMPTY generation
   generate
     if (C_WR_PNTR_WIDTH > C_RD_PNTR_WIDTH) begin : wdg // Write depth greater than read depth
       assign adj_rd_pntr_wr[C_WR_PNTR_WIDTH-1:C_WR_PNTR_WIDTH-C_RD_PNTR_WIDTH] = rd_pntr_wr;
       assign adj_rd_pntr_wr[C_WR_PNTR_WIDTH-C_RD_PNTR_WIDTH-1:0] = 0;
     end else begin : wdl // Write depth lesser than or equal to read depth
       assign adj_rd_pntr_wr = rd_pntr_wr[C_RD_PNTR_WIDTH-1:C_RD_PNTR_WIDTH-C_WR_PNTR_WIDTH];
     end
   endgenerate

  // Generate FULL and ALMOST_FULL
  // ram_wr_en used to determine FULL should depend on the FULL.
  assign ram_wr_en       = WR_EN & !FULL;
  assign full_int        = ((adj_rd_pntr_wr == (wr_pntr+1'h1)) || (ram_wr_en && (adj_rd_pntr_wr == (wr_pntr+2'h2))));
  assign almost_full_int = ((adj_rd_pntr_wr == (wr_pntr+2'h2)) || (ram_wr_en && (adj_rd_pntr_wr == (wr_pntr+3'h3))));

   // Register FULL and ALMOST_FULL Empty
   always @ (posedge WR_CLK or posedge RST_FULL_FF)
     begin
       if (RST_FULL_FF) begin
         FULL             <= C_FULL_FLAGS_RST_VAL;
         ALMOST_FULL      <= C_FULL_FLAGS_RST_VAL;
       end else begin
         if (full_int) begin
           FULL           <= #`TCQ 1'b1;
         end else begin
           FULL           <= #`TCQ 1'b0;
         end

         if (RST_FULL_GEN) begin
           ALMOST_FULL    <= #`TCQ 1'b0;
         end else if (!FULL) begin
           if (almost_full_int)
             ALMOST_FULL  <= #`TCQ 1'b1;
           else
             ALMOST_FULL  <= #`TCQ 1'b0;
         end
       end // wr_rst_i
     end // always
   always @ (posedge WR_CLK or posedge wr_rst_i)
     begin
       if (wr_rst_i) begin
         wr_data_count_int <= {C_WR_DATA_COUNT_WIDTH{1'b0}};
       end else begin
         wr_data_count_int <= #`TCQ {(wr_pntr[C_WR_PNTR_WIDTH-1:0] - adj_rd_pntr_wr[C_WR_PNTR_WIDTH-1:0]), 1'b0};
       end // wr_rst_i
     end // always

   // Determine which stage in FWFT registers are valid
   reg stage1_valid = 0;
   reg stage2_valid = 0;
   generate
     if (C_PRELOAD_LATENCY == 0) begin : grd_fwft_proc
       always @ (posedge RD_CLK or posedge rd_rst_i) begin
         if (rd_rst_i) begin
           stage1_valid     <= 0;
           stage2_valid     <= 0;
         end else begin

           if (!stage1_valid && !stage2_valid) begin
             if (!EMPTY)
               stage1_valid    <= #`TCQ 1'b1;
             else
               stage1_valid    <= #`TCQ 1'b0;
           end else if (stage1_valid && !stage2_valid) begin
             if (EMPTY) begin
               stage1_valid    <= #`TCQ 1'b0;
               stage2_valid    <= #`TCQ 1'b1;
             end else begin
               stage1_valid    <= #`TCQ 1'b1;
               stage2_valid    <= #`TCQ 1'b1;
             end
           end else if (!stage1_valid && stage2_valid) begin
             if (EMPTY && RD_EN_USER) begin
               stage1_valid    <= #`TCQ 1'b0;
               stage2_valid    <= #`TCQ 1'b0;
             end else if (!EMPTY && RD_EN_USER) begin
               stage1_valid    <= #`TCQ 1'b1;
               stage2_valid    <= #`TCQ 1'b0;
             end else if (!EMPTY && !RD_EN_USER) begin
               stage1_valid    <= #`TCQ 1'b1;
               stage2_valid    <= #`TCQ 1'b1;
             end else begin
               stage1_valid    <= #`TCQ 1'b0;
               stage2_valid    <= #`TCQ 1'b1;
             end
           end else if (stage1_valid && stage2_valid) begin
             if (EMPTY && RD_EN_USER) begin
               stage1_valid    <= #`TCQ 1'b0;
               stage2_valid    <= #`TCQ 1'b1;
             end else begin
               stage1_valid    <= #`TCQ 1'b1;
               stage2_valid    <= #`TCQ 1'b1;
             end
           end else begin
             stage1_valid    <= #`TCQ 1'b0;
             stage2_valid    <= #`TCQ 1'b0;
           end
         end // rd_rst_i
       end // always
     end
   endgenerate

   //Pointers passed into opposite clock domain
   reg [31:0]  wr_ptr_rdclk;
   reg [31:0]  wr_ptr_rdclk_next;
   reg [31:0]  rd_ptr_wrclk;
   reg [31:0]  rd_ptr_wrclk_next;

   //Amount of data stored in the FIFO scaled to the narrowest (deepest) port
   // (Do not include data in FWFT stages)
   //Used to calculate PROG_EMPTY.
   wire [31:0] num_read_words_pe = 
     num_rd_bits/(C_DOUT_WIDTH/C_DEPTH_RATIO_WR);

   //Amount of data stored in the FIFO scaled to the narrowest (deepest) port
   // (Do not include data in FWFT stages)
   //Used to calculate PROG_FULL.
   wire [31:0] num_write_words_pf =
     num_wr_bits/(C_DIN_WIDTH/C_DEPTH_RATIO_RD);

   /**************************
    * Read Data Count
    *************************/

   reg [31:0] num_read_words_dc;
   reg [C_RD_DATA_COUNT_WIDTH-1:0] num_read_words_sized_i;
   
   always @(num_rd_bits) begin
     if (C_USE_FWFT_DATA_COUNT) begin
        
        //If using extra logic for FWFT Data Counts, 
        // then scale FIFO contents to read domain, 
        // and add two read words for FWFT stages
        //This value is only a temporary value and not used in the code.
        num_read_words_dc = (num_rd_bits/C_DOUT_WIDTH+2);
        
        //Trim the read words for use with RD_DATA_COUNT
        num_read_words_sized_i = 
          num_read_words_dc[C_RD_PNTR_WIDTH : C_RD_PNTR_WIDTH-C_RD_DATA_COUNT_WIDTH+1];
        
     end else begin
        
        //If not using extra logic for FWFT Data Counts, 
        // then scale FIFO contents to read domain.
        //This value is only a temporary value and not used in the code.
        num_read_words_dc = num_rd_bits/C_DOUT_WIDTH;
        
        //Trim the read words for use with RD_DATA_COUNT
        num_read_words_sized_i = 
          num_read_words_dc[C_RD_PNTR_WIDTH-1 : C_RD_PNTR_WIDTH-C_RD_DATA_COUNT_WIDTH];
        
     end //if (C_USE_FWFT_DATA_COUNT)
   end //always

   
   /**************************
    * Write Data Count
    *************************/

   reg [31:0] num_write_words_dc;
   reg [C_WR_DATA_COUNT_WIDTH-1:0] num_write_words_sized_i;
   
   always @(num_wr_bits) begin
     if (C_USE_FWFT_DATA_COUNT) begin
        
        //Calculate the Data Count value for the number of write words, 
        // when using First-Word Fall-Through with extra logic for Data 
        // Counts. This takes into consideration the number of words that 
        // are expected to be stored in the FWFT register stages (it always 
        // assumes they are filled).
        //This value is scaled to the Write Domain.
        //The expression (((A-1)/B))+1 divides A/B, but takes the 
        // ceiling of the result.
        //When num_wr_bits==0, set the result manually to prevent 
        // division errors.
        //EXTRA_WORDS_DC is the number of words added to write_words 
        // due to FWFT.
        //This value is only a temporary value and not used in the code.
        num_write_words_dc = (num_wr_bits==0) ? EXTRA_WORDS_DC :  (((num_wr_bits-1)/C_DIN_WIDTH)+1) + EXTRA_WORDS_DC ;
        
        //Trim the write words for use with WR_DATA_COUNT
        num_write_words_sized_i = 
          num_write_words_dc[C_WR_PNTR_WIDTH : C_WR_PNTR_WIDTH-C_WR_DATA_COUNT_WIDTH+1];
        
     end else begin
        
        //Calculate the Data Count value for the number of write words, when NOT
        // using First-Word Fall-Through with extra logic for Data Counts. This 
        // calculates only the number of words in the internal FIFO.
        //The expression (((A-1)/B))+1 divides A/B, but takes the 
        // ceiling of the result.
        //This value is scaled to the Write Domain.
        //When num_wr_bits==0, set the result manually to prevent 
        // division errors.
        //This value is only a temporary value and not used in the code.
        num_write_words_dc = (num_wr_bits==0) ? 0 : ((num_wr_bits-1)/C_DIN_WIDTH)+1;
        
        //Trim the read words for use with RD_DATA_COUNT
        num_write_words_sized_i = 
          num_write_words_dc[C_WR_PNTR_WIDTH-1 : C_WR_PNTR_WIDTH-C_WR_DATA_COUNT_WIDTH];
        
     end //if (C_USE_FWFT_DATA_COUNT)
   end //always

    
    
   /***************************************************************************
    * Internal registers and wires
    **************************************************************************/

   //Temporary signals used for calculating the model's outputs. These
   //are only used in the assign statements immediately following wire,
   //parameter, and function declarations.
   wire [C_DOUT_WIDTH-1:0] ideal_dout_out;      
   wire valid_i;
   wire valid_out1;
   wire valid_out2;
   wire valid_out;  
   wire underflow_i;

   //Ideal FIFO signals. These are the raw output of the behavioral model,
   //which behaves like an ideal FIFO.
   reg [1:0]               err_type                 = 0;
   reg [1:0]               err_type_d1              = 0;
   reg [1:0]               err_type_both              = 0;
   reg [C_DOUT_WIDTH-1:0]  ideal_dout               = 0;
   reg [C_DOUT_WIDTH-1:0]  ideal_dout_d1            = 0;
   reg [C_DOUT_WIDTH-1:0]  ideal_dout_both            = 0;
   reg                     ideal_wr_ack             = 0;
   reg                     ideal_valid              = 0;
   reg                     ideal_overflow           = C_OVERFLOW_LOW;
   reg                     ideal_underflow          = C_UNDERFLOW_LOW;
   reg                     ideal_prog_full          = 0;
   reg                     ideal_prog_empty         = 1;
   reg [C_WR_DATA_COUNT_WIDTH-1 : 0] ideal_wr_count = 0;
   reg [C_RD_DATA_COUNT_WIDTH-1 : 0] ideal_rd_count = 0;

   //Assorted reg values for delayed versions of signals   
   reg         valid_d1     = 0;
   reg         valid_d2     = 0; 
   
   //user specified value for reseting the size of the fifo
   reg [C_DOUT_WIDTH-1:0]            dout_reset_val = 0;
   
   //temporary registers for WR_RESPONSE_LATENCY feature
   
   integer                           tmp_wr_listsize;
   integer                           tmp_rd_listsize;
   
   //Signal for registered version of prog full and empty
   
   //Threshold values for Programmable Flags
   integer                           prog_empty_actual_thresh_assert;
   integer                           prog_empty_actual_thresh_negate;
   integer                           prog_full_actual_thresh_assert;
   integer                           prog_full_actual_thresh_negate;
   

  /****************************************************************************
   * Function Declarations
   ***************************************************************************/

  /**************************************************************************
   * write_fifo
   *   This task writes a word to the FIFO memory and updates the 
   * write pointer.
   *   FIFO size is relative to write domain.
  ***************************************************************************/
  task write_fifo;
    begin
      memory[wr_ptr]     <= DIN;
      wr_pntr <= #`TCQ wr_pntr + 1;
      // Store the type of error injection (double/single) on write
      case (C_ERROR_INJECTION_TYPE)
        3:       ecc_err[wr_ptr]    <= {INJECTDBITERR,INJECTSBITERR};
        2:       ecc_err[wr_ptr]    <= {INJECTDBITERR,1'b0};
        1:       ecc_err[wr_ptr]    <= {1'b0,INJECTSBITERR};
        default: ecc_err[wr_ptr]    <= 0;
      endcase
      // (Works opposite to core: wr_ptr is a DOWN counter)
      if (wr_ptr == 0) begin
        wr_ptr          <= C_WR_DEPTH - 1;
      end else begin
        wr_ptr          <= wr_ptr - 1;
      end
    end
  endtask // write_fifo

  /**************************************************************************
   * read_fifo
   *   This task reads a word from the FIFO memory and updates the read 
   * pointer. It's output is the ideal_dout bus.
   *   FIFO size is relative to write domain.
   ***************************************************************************/
  task read_fifo;
    integer i;
    reg [C_DOUT_WIDTH-1:0]      tmp_dout;
    reg [C_DIN_WIDTH-1:0]       memory_read;
    reg [31:0]                  tmp_rd_ptr;
    reg [31:0]                  rd_ptr_high;
    reg [31:0]                  rd_ptr_low;
    reg [1:0]                   tmp_ecc_err;
    begin
      rd_pntr <= #`TCQ rd_pntr + 1;
      // output is wider than input
      if (reads_per_write == 0) begin
        tmp_dout = 0;
        tmp_rd_ptr = (rd_ptr << log2_writes_per_read)+(writes_per_read-1);
        for (i = writes_per_read - 1; i >= 0; i = i - 1) begin
          tmp_dout = tmp_dout << C_DIN_WIDTH;
          tmp_dout = tmp_dout | memory[tmp_rd_ptr];
           
          // (Works opposite to core: rd_ptr is a DOWN counter)
          if (tmp_rd_ptr == 0) begin
            tmp_rd_ptr = C_WR_DEPTH - 1;
          end else begin
            tmp_rd_ptr = tmp_rd_ptr - 1;
          end
        end

      // output is symmetric
      end else if (reads_per_write == 1) begin
        tmp_dout = memory[rd_ptr][C_DIN_WIDTH-1:0];
        // Retreive the error injection type. Based on the error injection type
        // corrupt the output data.
        tmp_ecc_err = ecc_err[rd_ptr];
        if (ENABLE_ERR_INJECTION && C_DIN_WIDTH == C_DOUT_WIDTH) begin
          if (tmp_ecc_err[1]) begin // Corrupt the output data only for double bit error
            if (C_DOUT_WIDTH == 1) begin
              $display("FAILURE : Data width must be >= 2 for double bit error injection.");
              $finish;
            end else if (C_DOUT_WIDTH == 2)
              tmp_dout = {~tmp_dout[C_DOUT_WIDTH-1],~tmp_dout[C_DOUT_WIDTH-2]};
            else
              tmp_dout = {~tmp_dout[C_DOUT_WIDTH-1],~tmp_dout[C_DOUT_WIDTH-2],(tmp_dout << 2)};
          end else begin
            tmp_dout = tmp_dout[C_DOUT_WIDTH-1:0];
          end
          err_type <= {tmp_ecc_err[1], tmp_ecc_err[0] & !tmp_ecc_err[1]};
        end else begin
          err_type <= 0;
        end

      // input is wider than output
      end else begin
        rd_ptr_high = rd_ptr >> log2_reads_per_write;
        rd_ptr_low  = rd_ptr & (reads_per_write - 1);
        memory_read = memory[rd_ptr_high];
        tmp_dout    = memory_read >> (rd_ptr_low*C_DOUT_WIDTH);
      end
      ideal_dout <= tmp_dout;
       
      // (Works opposite to core: rd_ptr is a DOWN counter)
      if (rd_ptr == 0) begin
        rd_ptr <= C_RD_DEPTH - 1;
      end else begin
        rd_ptr <= rd_ptr - 1;
      end
    end
  endtask

  /**************************************************************************
  * log2_val
  *   Returns the 'log2' value for the input value for the supported ratios
  ***************************************************************************/
  function [31:0] log2_val;
    input [31:0] binary_val;

    begin
      if (binary_val == 8) begin
        log2_val = 3;
      end else if (binary_val == 4) begin
        log2_val = 2;
      end else begin
        log2_val = 1;
      end
    end
  endfunction

  /***********************************************************************
  * hexstr_conv
  *   Converts a string of type hex to a binary value (for C_DOUT_RST_VAL)
  ***********************************************************************/
  function [C_DOUT_WIDTH-1:0] hexstr_conv;
    input [(C_DOUT_WIDTH*8)-1:0] def_data;

    integer index,i,j;
    reg [3:0] bin;

    begin
      index = 0;
      hexstr_conv = 'b0;
      for( i=C_DOUT_WIDTH-1; i>=0; i=i-1 )
      begin
        case (def_data[7:0])
          8'b00000000 :
          begin
            bin = 4'b0000;
            i = -1;
          end
          8'b00110000 : bin = 4'b0000;
          8'b00110001 : bin = 4'b0001;
          8'b00110010 : bin = 4'b0010;
          8'b00110011 : bin = 4'b0011;
          8'b00110100 : bin = 4'b0100;
          8'b00110101 : bin = 4'b0101;
          8'b00110110 : bin = 4'b0110;
          8'b00110111 : bin = 4'b0111;
          8'b00111000 : bin = 4'b1000;
          8'b00111001 : bin = 4'b1001;
          8'b01000001 : bin = 4'b1010;
          8'b01000010 : bin = 4'b1011;
          8'b01000011 : bin = 4'b1100;
          8'b01000100 : bin = 4'b1101;
          8'b01000101 : bin = 4'b1110;
          8'b01000110 : bin = 4'b1111;
          8'b01100001 : bin = 4'b1010;
          8'b01100010 : bin = 4'b1011;
          8'b01100011 : bin = 4'b1100;
          8'b01100100 : bin = 4'b1101;
          8'b01100101 : bin = 4'b1110;
          8'b01100110 : bin = 4'b1111;
          default :
          begin
            bin = 4'bx;
          end
        endcase
        for( j=0; j<4; j=j+1)
        begin
          if ((index*4)+j < C_DOUT_WIDTH)
          begin
            hexstr_conv[(index*4)+j] = bin[j];
          end
        end
        index = index + 1;
        def_data = def_data >> 8;
      end
    end
  endfunction

  /*************************************************************************
  * Initialize Signals for clean power-on simulation
  *************************************************************************/
   initial begin
      num_wr_bits        = 0;
      num_rd_bits        = 0;
      next_num_wr_bits   = 0;
      next_num_rd_bits   = 0;
      rd_ptr             = C_RD_DEPTH - 1;
      wr_ptr             = C_WR_DEPTH - 1;
      wr_pntr            = 0;
      rd_pntr            = 0;
      rd_ptr_wrclk       = rd_ptr;
      wr_ptr_rdclk       = wr_ptr;
      dout_reset_val     = hexstr_conv(C_DOUT_RST_VAL);
      ideal_dout         = dout_reset_val;
      err_type           = 0;
      err_type_d1        = 0;
      err_type_both      = 0;
      ideal_dout_d1      = dout_reset_val;
      ideal_wr_ack       = 1'b0;
      ideal_valid        = 1'b0;
      valid_d1           = 1'b0;
      valid_d2           = 1'b0;
      ideal_overflow     = C_OVERFLOW_LOW;
      ideal_underflow    = C_UNDERFLOW_LOW;
      ideal_wr_count     = 0;
      ideal_rd_count     = 0;
      ideal_prog_full    = 1'b0;
      ideal_prog_empty   = 1'b1;
    end


  /*************************************************************************
   * Connect the module inputs and outputs to the internal signals of the 
   * behavioral model.
   *************************************************************************/
   //Inputs
   /*
    wire [C_DIN_WIDTH-1:0] DIN;
   wire [C_RD_PNTR_WIDTH-1:0] PROG_EMPTY_THRESH;
   wire [C_RD_PNTR_WIDTH-1:0] PROG_EMPTY_THRESH_ASSERT;
   wire [C_RD_PNTR_WIDTH-1:0] PROG_EMPTY_THRESH_NEGATE;
   wire [C_WR_PNTR_WIDTH-1:0] PROG_FULL_THRESH;
   wire [C_WR_PNTR_WIDTH-1:0] PROG_FULL_THRESH_ASSERT;
   wire [C_WR_PNTR_WIDTH-1:0] PROG_FULL_THRESH_NEGATE;   
   wire RD_CLK;
   wire RD_EN;
   wire RST;
   wire WR_CLK;
   wire WR_EN;
    */

   //***************************************************************************
   // Dout may change behavior based on latency
   //***************************************************************************
   assign ideal_dout_out[C_DOUT_WIDTH-1:0] = (C_PRELOAD_LATENCY==2 &&
                          (C_MEMORY_TYPE==0 || C_MEMORY_TYPE==1) )?
                         ideal_dout_d1: ideal_dout;   
   assign DOUT[C_DOUT_WIDTH-1:0] = ideal_dout_out; 

   //***************************************************************************
   // Assign SBITERR and DBITERR based on latency 
   //***************************************************************************
   assign SBITERR = (C_ERROR_INJECTION_TYPE == 1 || C_ERROR_INJECTION_TYPE == 3) && 
                    (C_PRELOAD_LATENCY == 2 &&
                    (C_MEMORY_TYPE==0 || C_MEMORY_TYPE==1) ) ?
                    err_type_d1[0]: err_type[0]; 
   assign DBITERR = (C_ERROR_INJECTION_TYPE == 2 || C_ERROR_INJECTION_TYPE == 3) &&
                    (C_PRELOAD_LATENCY==2 && (C_MEMORY_TYPE==0 || C_MEMORY_TYPE==1)) ?
                    err_type_d1[1]: err_type[1]; 
  
   //***************************************************************************
   // Safety-ckt logic with embedded reg/fabric reg
   //***************************************************************************
     generate
         if ((C_MEMORY_TYPE==0 || C_MEMORY_TYPE==1) && C_EN_SAFETY_CKT==1 && C_USE_EMBEDDED_REG < 3) begin
         
         reg [C_DOUT_WIDTH-1:0]     dout_rst_val_d1;
         reg [C_DOUT_WIDTH-1:0]     dout_rst_val_d2;
         reg [1:0] rst_delayed_sft1              =1;
         reg [1:0] rst_delayed_sft2              =1;
         reg [1:0] rst_delayed_sft3              =1;
         reg [1:0] rst_delayed_sft4              =1;

       //  if (C_HAS_VALID == 1) begin
       //       assign valid_out = valid_d1;
       //  end
             
        always@(posedge RD_CLK)
          begin
          rst_delayed_sft1 <= #`TCQ rd_rst_i;
          rst_delayed_sft2 <= #`TCQ rst_delayed_sft1;
          rst_delayed_sft3 <= #`TCQ rst_delayed_sft2; 
          rst_delayed_sft4 <= #`TCQ rst_delayed_sft3;
          end
        always@(posedge rst_delayed_sft4 or posedge rd_rst_i or posedge RD_CLK)
          begin
          if( rst_delayed_sft4 == 1'b1 || rd_rst_i == 1'b1) 
              ram_rd_en_d1 <= #`TCQ 1'b0;
          else 
               ram_rd_en_d1 <= #`TCQ ram_rd_en;
          end
          
        always@(posedge rst_delayed_sft2 or posedge RD_CLK) 
           begin
           if (rst_delayed_sft2 == 1'b1) begin
              if (C_USE_DOUT_RST == 1'b1) begin
                  @(posedge RD_CLK)
                   ideal_dout_d1 <= #`TCQ dout_reset_val;
              end
           end
           else begin
                   if (ram_rd_en_d1) begin
                   ideal_dout_d1   <= #`TCQ ideal_dout;
                   err_type_d1[0] <= #`TCQ err_type[0];
                   err_type_d1[1] <= #`TCQ err_type[1];
                   end
             end 
           end  
      end 
      endgenerate   

//***************************************************************************
   // Safety-ckt logic with embedded reg + fabric reg
   //***************************************************************************
     generate
         if ((C_MEMORY_TYPE==0 || C_MEMORY_TYPE==1) && C_EN_SAFETY_CKT==1 && C_USE_EMBEDDED_REG == 3) begin
         
         reg [C_DOUT_WIDTH-1:0]     dout_rst_val_d1;
         reg [C_DOUT_WIDTH-1:0]     dout_rst_val_d2;
         reg [1:0] rst_delayed_sft1              =1;
         reg [1:0] rst_delayed_sft2              =1;
         reg [1:0] rst_delayed_sft3              =1;
         reg [1:0] rst_delayed_sft4              =1;

        always@(posedge RD_CLK) begin
          rst_delayed_sft1 <= #`TCQ rd_rst_i;
          rst_delayed_sft2 <= #`TCQ rst_delayed_sft1;
          rst_delayed_sft3 <= #`TCQ rst_delayed_sft2; 
          rst_delayed_sft4 <= #`TCQ rst_delayed_sft3;
        end
        always@(posedge rst_delayed_sft4 or posedge rd_rst_i or posedge RD_CLK) begin
          if( rst_delayed_sft4 == 1'b1 || rd_rst_i == 1'b1) 
              ram_rd_en_d1 <= #`TCQ 1'b0;
          else begin
               ram_rd_en_d1 <= #`TCQ ram_rd_en;
               fab_rd_en_d1 <= #`TCQ ram_rd_en_d1;
          end
        end
          
        always@(posedge rst_delayed_sft2 or posedge RD_CLK) begin
           if (rst_delayed_sft2 == 1'b1) begin
              if (C_USE_DOUT_RST == 1'b1) begin
                   @(posedge RD_CLK)
                   ideal_dout_d1 <= #`TCQ dout_reset_val;
                   ideal_dout_both <= #`TCQ dout_reset_val;
              end
           end else begin
             if (ram_rd_en_d1) begin
               ideal_dout_both   <= #`TCQ ideal_dout;
               err_type_both[0] <= #`TCQ err_type[0];
               err_type_both[1] <= #`TCQ err_type[1];
             end
              
             if (fab_rd_en_d1) begin
               ideal_dout_d1   <= #`TCQ ideal_dout_both;
               err_type_d1[0] <= #`TCQ err_type_both[0];
               err_type_d1[1] <= #`TCQ err_type_both[1];
             end
           end 
         end      
      end 
      endgenerate    
 
   //***************************************************************************
   // Overflow may be active-low
   //***************************************************************************
   generate
      if (C_HAS_OVERFLOW==1) begin : blockOF1
   assign OVERFLOW = ideal_overflow ? !C_OVERFLOW_LOW : C_OVERFLOW_LOW;
      end
   endgenerate

   assign PROG_EMPTY = ideal_prog_empty;
   assign PROG_FULL  = ideal_prog_full;

   //***************************************************************************
   // Valid may change behavior based on latency or active-low
   //***************************************************************************
   generate
      if (C_HAS_VALID==1) begin : blockVL1
   assign valid_i   = (C_PRELOAD_LATENCY==0) ? (RD_EN & ~EMPTY) : ideal_valid;
   assign valid_out1 = (C_PRELOAD_LATENCY==2 &&
                       (C_MEMORY_TYPE==0 || C_MEMORY_TYPE==1) && C_USE_EMBEDDED_REG < 3)?
                       valid_d1: valid_i;  
   assign valid_out2 = (C_PRELOAD_LATENCY==2 &&
                       (C_MEMORY_TYPE==0 || C_MEMORY_TYPE==1) && C_USE_EMBEDDED_REG == 3)?
                       valid_d2: valid_i; 
   assign valid_out = (C_USE_EMBEDDED_REG == 3) ? valid_out2 : valid_out1;
   assign VALID     = valid_out ? !C_VALID_LOW : C_VALID_LOW;
     end
   endgenerate


   //***************************************************************************
   // Underflow may change behavior based on latency or active-low   
   //***************************************************************************
   generate
      if (C_HAS_UNDERFLOW==1) begin : blockUF1
   assign underflow_i = (C_PRELOAD_LATENCY==0) ? (RD_EN & EMPTY) : ideal_underflow;
   assign UNDERFLOW   = underflow_i ? !C_UNDERFLOW_LOW : C_UNDERFLOW_LOW;
    end
   endgenerate

   //***************************************************************************
   // Write acknowledge may be active low
   //***************************************************************************
   generate
      if (C_HAS_WR_ACK==1) begin : blockWK1
   assign WR_ACK = ideal_wr_ack ? !C_WR_ACK_LOW : C_WR_ACK_LOW;
     end
   endgenerate


   //***************************************************************************
   // Generate RD_DATA_COUNT if Use Extra Logic option is selected
   //***************************************************************************
   generate
      if (C_HAS_WR_DATA_COUNT == 1 && C_USE_FWFT_DATA_COUNT == 1) begin : wdc_fwft_ext

      reg  [C_PNTR_WIDTH-1:0]  adjusted_wr_pntr = 0;
      reg  [C_PNTR_WIDTH-1:0]  adjusted_rd_pntr = 0;
      wire [C_PNTR_WIDTH-1:0]  diff_wr_rd_tmp;
      wire [C_PNTR_WIDTH:0]    diff_wr_rd;
      reg  [C_PNTR_WIDTH:0]    wr_data_count_i  = 0;
        always @* begin
          if (C_WR_PNTR_WIDTH > C_RD_PNTR_WIDTH) begin
            adjusted_wr_pntr = wr_pntr;
            adjusted_rd_pntr = 0;
            adjusted_rd_pntr[C_PNTR_WIDTH-1:C_PNTR_WIDTH-C_RD_PNTR_WIDTH] = rd_pntr_wr;
          end else if (C_WR_PNTR_WIDTH < C_RD_PNTR_WIDTH) begin
            adjusted_rd_pntr = rd_pntr_wr;
            adjusted_wr_pntr = 0;
            adjusted_wr_pntr[C_PNTR_WIDTH-1:C_PNTR_WIDTH-C_WR_PNTR_WIDTH] = wr_pntr;
          end else begin
            adjusted_wr_pntr = wr_pntr;
            adjusted_rd_pntr = rd_pntr_wr;
          end
        end // always @*

        assign diff_wr_rd_tmp = adjusted_wr_pntr - adjusted_rd_pntr;
        assign diff_wr_rd     = {1'b0,diff_wr_rd_tmp};

        always @ (posedge wr_rst_i or posedge WR_CLK)
        begin
            if (wr_rst_i)
              wr_data_count_i <= 0;
            else
              wr_data_count_i <= #`TCQ diff_wr_rd + EXTRA_WORDS_DC;
        end // always @ (posedge WR_CLK or posedge WR_CLK)

        always @* begin
          if (C_WR_PNTR_WIDTH >= C_RD_PNTR_WIDTH)
            wdc_fwft_ext_as = wr_data_count_i[C_PNTR_WIDTH:0];
          else
            wdc_fwft_ext_as = wr_data_count_i[C_PNTR_WIDTH:C_RD_PNTR_WIDTH-C_WR_PNTR_WIDTH];
        end // always @*
      end // wdc_fwft_ext
   endgenerate

   //***************************************************************************
   // Generate RD_DATA_COUNT if Use Extra Logic option is selected
   //***************************************************************************
   reg  [C_RD_PNTR_WIDTH:0]    rdc_fwft_ext_as  = 0;

   generate if (C_USE_EMBEDDED_REG < 3) begin: rdc_fwft_ext_both
      if (C_HAS_RD_DATA_COUNT == 1 && C_USE_FWFT_DATA_COUNT == 1) begin : rdc_fwft_ext
      reg  [C_RD_PNTR_WIDTH-1:0]  adjusted_wr_pntr_rd = 0;
      wire [C_RD_PNTR_WIDTH-1:0]  diff_rd_wr_tmp;
      wire [C_RD_PNTR_WIDTH:0]    diff_rd_wr;
        always @* begin
          if (C_RD_PNTR_WIDTH > C_WR_PNTR_WIDTH) begin
            adjusted_wr_pntr_rd = 0;
            adjusted_wr_pntr_rd[C_RD_PNTR_WIDTH-1:C_RD_PNTR_WIDTH-C_WR_PNTR_WIDTH] = wr_pntr_rd;
          end else begin
            adjusted_wr_pntr_rd = wr_pntr_rd[C_WR_PNTR_WIDTH-1:C_WR_PNTR_WIDTH-C_RD_PNTR_WIDTH];
          end
        end // always @*

        assign diff_rd_wr_tmp = adjusted_wr_pntr_rd - rd_pntr;
        assign diff_rd_wr     = {1'b0,diff_rd_wr_tmp};


   always @ (posedge rd_rst_i or posedge RD_CLK)
        begin
            if (rd_rst_i) begin
              rdc_fwft_ext_as   <= 0;
            end else begin
              if (!stage2_valid)
                rdc_fwft_ext_as <= #`TCQ 0;
              else if (!stage1_valid && stage2_valid)
                rdc_fwft_ext_as <= #`TCQ 1;
              else
                rdc_fwft_ext_as <= #`TCQ diff_rd_wr + 2'h2;
            end 
        end // always @ (posedge WR_CLK or posedge WR_CLK)
      end // rdc_fwft_ext
 end
   endgenerate


  generate if (C_USE_EMBEDDED_REG == 3) begin
     if (C_HAS_RD_DATA_COUNT == 1 && C_USE_FWFT_DATA_COUNT == 1) begin : rdc_fwft_ext
      reg  [C_RD_PNTR_WIDTH-1:0]  adjusted_wr_pntr_rd = 0;
      wire [C_RD_PNTR_WIDTH-1:0]  diff_rd_wr_tmp;
      wire [C_RD_PNTR_WIDTH:0]    diff_rd_wr;
        always @* begin
          if (C_RD_PNTR_WIDTH > C_WR_PNTR_WIDTH) begin
            adjusted_wr_pntr_rd = 0;
            adjusted_wr_pntr_rd[C_RD_PNTR_WIDTH-1:C_RD_PNTR_WIDTH-C_WR_PNTR_WIDTH] = wr_pntr_rd;
          end else begin
            adjusted_wr_pntr_rd = wr_pntr_rd[C_WR_PNTR_WIDTH-1:C_WR_PNTR_WIDTH-C_RD_PNTR_WIDTH];
          end
        end // always @*

        assign diff_rd_wr_tmp = adjusted_wr_pntr_rd - rd_pntr;
        assign diff_rd_wr     = {1'b0,diff_rd_wr_tmp};
        wire [C_RD_PNTR_WIDTH:0]  diff_rd_wr_1;
   //     assign diff_rd_wr_1 = diff_rd_wr +2'h2;

       always @ (posedge rd_rst_i or posedge RD_CLK)
        begin
            if (rd_rst_i) begin
              rdc_fwft_ext_as   <= #`TCQ 0;
            end else begin
          //if (fab_read_data_valid_i == 1'b0 && ((ram_valid_i == 1'b0 && read_data_valid_i ==1'b0) || (ram_valid_i == 1'b0 && read_data_valid_i ==1'b1) || (ram_valid_i == 1'b1 && read_data_valid_i ==1'b0) || (ram_valid_i == 1'b1 && read_data_valid_i ==1'b1)))
          //    rdc_fwft_ext_as <= 1'b0;
          //else if (fab_read_data_valid_i == 1'b1 && ((ram_valid_i == 1'b0 && read_data_valid_i ==1'b0) || (ram_valid_i == 1'b0 && read_data_valid_i ==1'b1))) 
          //    rdc_fwft_ext_as <= 1'b1;
          //else
            rdc_fwft_ext_as <= diff_rd_wr + 2'h2 ;
        end



end
end
end
endgenerate
          

   //***************************************************************************
   // Assign the read data count value only if it is selected, 
   // otherwise output zeros.
   //***************************************************************************
   generate
      if (C_HAS_RD_DATA_COUNT == 1) begin : grdc
   assign RD_DATA_COUNT[C_RD_DATA_COUNT_WIDTH-1:0] = C_USE_FWFT_DATA_COUNT ?
          rdc_fwft_ext_as[C_RD_PNTR_WIDTH:C_RD_PNTR_WIDTH+1-C_RD_DATA_COUNT_WIDTH] :
          rd_data_count_int[C_RD_PNTR_WIDTH:C_RD_PNTR_WIDTH+1-C_RD_DATA_COUNT_WIDTH];
      end
   endgenerate

   generate
      if (C_HAS_RD_DATA_COUNT == 0) begin : gnrdc
   assign RD_DATA_COUNT[C_RD_DATA_COUNT_WIDTH-1:0] = {C_RD_DATA_COUNT_WIDTH{1'b0}};
      end
   endgenerate

   //***************************************************************************
   // Assign the write data count value only if it is selected, 
   // otherwise output zeros
   //***************************************************************************
   generate
      if (C_HAS_WR_DATA_COUNT == 1) begin : gwdc
   assign WR_DATA_COUNT[C_WR_DATA_COUNT_WIDTH-1:0] = (C_USE_FWFT_DATA_COUNT == 1) ?
          wdc_fwft_ext_as[C_WR_PNTR_WIDTH:C_WR_PNTR_WIDTH+1-C_WR_DATA_COUNT_WIDTH] :
          wr_data_count_int[C_WR_PNTR_WIDTH:C_WR_PNTR_WIDTH+1-C_WR_DATA_COUNT_WIDTH];
      end
   endgenerate
   
   generate
      if (C_HAS_WR_DATA_COUNT == 0) begin : gnwdc
   assign WR_DATA_COUNT[C_WR_DATA_COUNT_WIDTH-1:0] = {C_WR_DATA_COUNT_WIDTH{1'b0}};
      end
   endgenerate


  /**************************************************************************
  * Assorted registers for delayed versions of signals
  **************************************************************************/
  //Capture delayed version of valid
  generate
      if (C_HAS_VALID==1) begin : blockVL2
  always @(posedge RD_CLK or posedge rd_rst_i) begin
    if (rd_rst_i == 1'b1) begin
      valid_d1 <= 1'b0;
      valid_d2 <= 1'b0;
    end else begin
      valid_d1 <= #`TCQ valid_i;
      valid_d2 <= #`TCQ valid_d1;
    end 
//    if (C_USE_EMBEDDED_REG == 3 && (C_EN_SAFETY_CKT == 0 || C_EN_SAFETY_CKT == 1 ) begin
  //      valid_d2 <= #`TCQ valid_d1;
      //  end 
  end 
      end
 endgenerate  
   
  //Capture delayed version of dout
  /**************************************************************************
    *embedded/fabric reg with no safety ckt
    **************************************************************************/
  generate 
       if (C_USE_EMBEDDED_REG < 3) begin
  always @(posedge RD_CLK or posedge rd_rst_i) begin
    if (rd_rst_i == 1'b1) begin
       if (C_USE_DOUT_RST == 1'b1) begin
         @(posedge RD_CLK)
           ideal_dout_d1   <= #`TCQ dout_reset_val;
           ideal_dout   <= #`TCQ dout_reset_val;
       end
      // Reset err_type only if ECC is not selected
      if (C_USE_ECC == 0)
        err_type_d1     <= #`TCQ 0;
     end else if (ram_rd_en_d1) begin
      ideal_dout_d1   <= #`TCQ ideal_dout;
      err_type_d1     <= #`TCQ err_type;
           end    
  end  
   
end  
endgenerate 
/**************************************************************************
    *embedded + fabric reg with no safety ckt
    **************************************************************************/

generate 
  if (C_USE_EMBEDDED_REG == 3) begin
    always @(posedge RD_CLK or posedge rd_rst_i) begin
      if (rd_rst_i == 1'b1) begin
        if (C_USE_DOUT_RST == 1'b1) begin
           @(posedge RD_CLK)
             ideal_dout    <= #`TCQ dout_reset_val;
             ideal_dout_d1   <= #`TCQ dout_reset_val;
             ideal_dout_both   <= #`TCQ dout_reset_val;
        end
        // Reset err_type only if ECC is not selected
        if (C_USE_ECC == 0) begin
          err_type_d1     <= #`TCQ 0;
          err_type_both   <= #`TCQ 0;
        end
      end else begin
         if (ram_rd_en_d1) begin
           ideal_dout_both   <= #`TCQ ideal_dout;
           err_type_both     <= #`TCQ err_type;
         end    
         if (fab_rd_en_d1) begin
           ideal_dout_d1   <= #`TCQ ideal_dout_both;
           err_type_d1     <= #`TCQ err_type_both;
         end
      end
    end  
  end  
endgenerate 

  
   /**************************************************************************
    * Overflow and Underflow Flag calculation
    *  (handled separately because they don't support rst)
    **************************************************************************/
   generate
     if (C_HAS_OVERFLOW == 1 && IS_8SERIES == 0) begin : g7s_ovflw
       always @(posedge WR_CLK) begin
         ideal_overflow    <= #`TCQ WR_EN & FULL;
       end
     end else if (C_HAS_OVERFLOW == 1 && IS_8SERIES == 1) begin : g8s_ovflw
       always @(posedge WR_CLK) begin
         //ideal_overflow    <= #`TCQ WR_EN & (FULL | wr_rst_i);
         ideal_overflow    <= #`TCQ WR_EN & (FULL );
       end
     end
   endgenerate

   generate
     if (C_HAS_UNDERFLOW == 1 && IS_8SERIES == 0) begin : g7s_unflw
       always @(posedge RD_CLK) begin
         ideal_underflow    <= #`TCQ EMPTY & RD_EN;
       end
     end else if (C_HAS_UNDERFLOW == 1 && IS_8SERIES == 1) begin : g8s_unflw
       always @(posedge RD_CLK) begin
         ideal_underflow    <= #`TCQ (EMPTY) & RD_EN;
         //ideal_underflow    <= #`TCQ (rd_rst_i | EMPTY) & RD_EN;
       end
     end
   endgenerate

   /**************************************************************************
   * Write/Read Pointer Synchronization
   **************************************************************************/
   localparam NO_OF_SYNC_STAGE_INC_G2B = C_SYNCHRONIZER_STAGE + 1;
   wire [C_WR_PNTR_WIDTH-1:0] wr_pntr_sync_stgs [0:NO_OF_SYNC_STAGE_INC_G2B];
   wire [C_RD_PNTR_WIDTH-1:0] rd_pntr_sync_stgs [0:NO_OF_SYNC_STAGE_INC_G2B];
   genvar gss;

   generate for (gss = 1; gss <= NO_OF_SYNC_STAGE_INC_G2B; gss = gss + 1) begin : Sync_stage_inst
     fifo_generator_v13_1_2_sync_stage
       #(
         .C_WIDTH  (C_WR_PNTR_WIDTH)
        )
     rd_stg_inst
        (
         .RST      (rd_rst_i), 
         .CLK      (RD_CLK), 
         .DIN      (wr_pntr_sync_stgs[gss-1]), 
         .DOUT     (wr_pntr_sync_stgs[gss])
        );
 
     fifo_generator_v13_1_2_sync_stage
       #(
         .C_WIDTH  (C_RD_PNTR_WIDTH)
        )
     wr_stg_inst
        (
         .RST      (wr_rst_i), 
         .CLK      (WR_CLK), 
         .DIN      (rd_pntr_sync_stgs[gss-1]), 
         .DOUT     (rd_pntr_sync_stgs[gss])
        );
   end endgenerate // Sync_stage_inst

   assign wr_pntr_sync_stgs[0] = wr_pntr_rd1;
   assign rd_pntr_sync_stgs[0] = rd_pntr_wr1;
   always@* begin
     wr_pntr_rd           <= wr_pntr_sync_stgs[NO_OF_SYNC_STAGE_INC_G2B];
     rd_pntr_wr           <= rd_pntr_sync_stgs[NO_OF_SYNC_STAGE_INC_G2B];
   end

   /**************************************************************************
   * Write Domain Logic
   **************************************************************************/
   reg [C_WR_PNTR_WIDTH-1:0] diff_pntr = 0;
   always @(posedge WR_CLK or posedge wr_rst_i) begin : gen_fifo_wp
     if (wr_rst_i == 1'b1 && C_EN_SAFETY_CKT == 0)
       wr_pntr           <= 0;
     else if (C_EN_SAFETY_CKT == 1 && SAFETY_CKT_WR_RST == 1'b1)
       wr_pntr           <= #`TCQ 0;
   end
   always @(posedge WR_CLK or posedge wr_rst_i) begin : gen_fifo_w

     /****** Reset fifo (case 1)***************************************/
     if (wr_rst_i == 1'b1) begin
       num_wr_bits       <= 0;
       next_num_wr_bits   = 0;
       wr_ptr            <= C_WR_DEPTH - 1;
       rd_ptr_wrclk      <= C_RD_DEPTH - 1;
       ideal_wr_ack      <= 0;
       ideal_wr_count    <= 0;
       tmp_wr_listsize    = 0;
       rd_ptr_wrclk_next <= 0;
       wr_pntr_rd1       <= 0;

     end else begin //wr_rst_i==0

       wr_pntr_rd1   <= #`TCQ wr_pntr;

       //Determine the current number of words in the FIFO
       tmp_wr_listsize = (C_DEPTH_RATIO_RD > 1) ? num_wr_bits/C_DOUT_WIDTH :
                         num_wr_bits/C_DIN_WIDTH;
       rd_ptr_wrclk_next = rd_ptr;
       if (rd_ptr_wrclk < rd_ptr_wrclk_next) begin
         next_num_wr_bits = num_wr_bits -
                            C_DOUT_WIDTH*(rd_ptr_wrclk + C_RD_DEPTH
                                          - rd_ptr_wrclk_next);
       end else begin
         next_num_wr_bits = num_wr_bits -
                            C_DOUT_WIDTH*(rd_ptr_wrclk - rd_ptr_wrclk_next);
       end

       //If this is a write, handle the write by adding the value
       // to the linked list, and updating all outputs appropriately
       if (WR_EN == 1'b1) begin
         if (FULL == 1'b1) begin

           //If the FIFO is full, do NOT perform the write,
           // update flags accordingly
           if ((tmp_wr_listsize + C_DEPTH_RATIO_RD - 1)/C_DEPTH_RATIO_RD 
             >= C_FIFO_WR_DEPTH) begin
             //write unsuccessful - do not change contents

             //Do not acknowledge the write
             ideal_wr_ack      <= #`TCQ 0;
             //Reminder that FIFO is still full

             ideal_wr_count    <= #`TCQ num_write_words_sized_i;

           //If the FIFO is one from full, but reporting full
           end else 
             if ((tmp_wr_listsize + C_DEPTH_RATIO_RD - 1)/C_DEPTH_RATIO_RD ==
                C_FIFO_WR_DEPTH-1) begin
             //No change to FIFO

             //Write not successful
             ideal_wr_ack      <= #`TCQ 0;
             //With DEPTH-1 words in the FIFO, it is almost_full

             ideal_wr_count    <= #`TCQ num_write_words_sized_i;


           //If the FIFO is completely empty, but it is
           // reporting FULL for some reason (like reset)
           end else 
             if ((tmp_wr_listsize + C_DEPTH_RATIO_RD - 1)/C_DEPTH_RATIO_RD <=
                C_FIFO_WR_DEPTH-2) begin
             //No change to FIFO

             //Write not successful
             ideal_wr_ack      <= #`TCQ 0;
             //FIFO is really not close to full, so change flag status.

             ideal_wr_count    <= #`TCQ num_write_words_sized_i;
           end //(tmp_wr_listsize == 0)

         end else begin

           //If the FIFO is full, do NOT perform the write,
           // update flags accordingly
           if ((tmp_wr_listsize + C_DEPTH_RATIO_RD - 1)/C_DEPTH_RATIO_RD >=
              C_FIFO_WR_DEPTH) begin
             //write unsuccessful - do not change contents

             //Do not acknowledge the write
             ideal_wr_ack       <= #`TCQ 0;
             //Reminder that FIFO is still full

             ideal_wr_count     <= #`TCQ num_write_words_sized_i;

           //If the FIFO is one from full
           end else 
             if ((tmp_wr_listsize + C_DEPTH_RATIO_RD - 1)/C_DEPTH_RATIO_RD ==
                C_FIFO_WR_DEPTH-1) begin
             //Add value on DIN port to FIFO
             write_fifo;
             next_num_wr_bits = next_num_wr_bits + C_DIN_WIDTH;

             //Write successful, so issue acknowledge
             // and no error
             ideal_wr_ack      <= #`TCQ 1;
             //This write is CAUSING the FIFO to go full

             ideal_wr_count    <= #`TCQ num_write_words_sized_i;

           //If the FIFO is 2 from full
           end else 
             if ((tmp_wr_listsize + C_DEPTH_RATIO_RD - 1)/C_DEPTH_RATIO_RD == 
                C_FIFO_WR_DEPTH-2) begin
             //Add value on DIN port to FIFO
             write_fifo;
             next_num_wr_bits =  next_num_wr_bits + C_DIN_WIDTH;
             //Write successful, so issue acknowledge
             // and no error
             ideal_wr_ack      <= #`TCQ 1;
             //Still 2 from full

             ideal_wr_count    <= #`TCQ num_write_words_sized_i;

           //If the FIFO is not close to being full
           end else 
             if ((tmp_wr_listsize + C_DEPTH_RATIO_RD - 1)/C_DEPTH_RATIO_RD <
                C_FIFO_WR_DEPTH-2) begin
             //Add value on DIN port to FIFO
             write_fifo;
             next_num_wr_bits  = next_num_wr_bits + C_DIN_WIDTH;
             //Write successful, so issue acknowledge
             // and no error
             ideal_wr_ack      <= #`TCQ 1;
             //Not even close to full.

             ideal_wr_count    <= num_write_words_sized_i;

           end

         end

       end else begin //(WR_EN == 1'b1)

         //If user did not attempt a write, then do not
         // give ack or err
         ideal_wr_ack   <= #`TCQ 0;
         ideal_wr_count <= #`TCQ num_write_words_sized_i;
       end
       num_wr_bits       <= #`TCQ next_num_wr_bits;
       rd_ptr_wrclk      <= #`TCQ rd_ptr;

     end //wr_rst_i==0
   end // gen_fifo_w


  /***************************************************************************
   * Programmable FULL flags
   ***************************************************************************/

   wire [C_WR_PNTR_WIDTH-1:0] pf_thr_assert_val;
   wire [C_WR_PNTR_WIDTH-1:0] pf_thr_negate_val;

   generate if (C_PRELOAD_REGS == 1 && C_PRELOAD_LATENCY == 0) begin : FWFT
     assign pf_thr_assert_val = C_PROG_FULL_THRESH_ASSERT_VAL - EXTRA_WORDS_DC;
     assign pf_thr_negate_val = C_PROG_FULL_THRESH_NEGATE_VAL - EXTRA_WORDS_DC;
   end else begin // STD
     assign pf_thr_assert_val = C_PROG_FULL_THRESH_ASSERT_VAL;
     assign pf_thr_negate_val = C_PROG_FULL_THRESH_NEGATE_VAL;
   end endgenerate

   always @(posedge WR_CLK or posedge wr_rst_i) begin

     if (wr_rst_i == 1'b1) begin
       diff_pntr         <= 0;
     end else begin
       if (ram_wr_en)
         diff_pntr <= #`TCQ (wr_pntr - adj_rd_pntr_wr + 2'h1);
       else if (!ram_wr_en)
         diff_pntr <= #`TCQ (wr_pntr - adj_rd_pntr_wr);
    end
  end


   always @(posedge WR_CLK or posedge RST_FULL_FF) begin : gen_pf

     if (RST_FULL_FF == 1'b1) begin
       ideal_prog_full   <= C_FULL_FLAGS_RST_VAL;
     end else begin

       if (RST_FULL_GEN)
         ideal_prog_full   <= #`TCQ 0;
       //Single Programmable Full Constant Threshold
       else if (C_PROG_FULL_TYPE == 1) begin
         if (FULL == 0) begin
           if (diff_pntr >= pf_thr_assert_val)
             ideal_prog_full <= #`TCQ 1;
           else
             ideal_prog_full <= #`TCQ 0;
         end else
           ideal_prog_full   <= #`TCQ ideal_prog_full;
       //Two Programmable Full Constant Thresholds
       end else if (C_PROG_FULL_TYPE == 2) begin
         if (FULL == 0) begin
           if (diff_pntr >= pf_thr_assert_val)
             ideal_prog_full <= #`TCQ 1;
           else if (diff_pntr < pf_thr_negate_val)
             ideal_prog_full <= #`TCQ 0;
           else
             ideal_prog_full <= #`TCQ ideal_prog_full;
         end else
           ideal_prog_full   <= #`TCQ ideal_prog_full;
       //Single Programmable Full Threshold Input
       end else if (C_PROG_FULL_TYPE == 3) begin
         if (FULL == 0) begin
           if (C_PRELOAD_REGS == 1 && C_PRELOAD_LATENCY == 0) begin // FWFT
             if (diff_pntr >= (PROG_FULL_THRESH - EXTRA_WORDS_DC))
               ideal_prog_full <= #`TCQ 1;
             else
               ideal_prog_full <= #`TCQ 0;
           end else begin // STD
             if (diff_pntr >= PROG_FULL_THRESH)
               ideal_prog_full <= #`TCQ 1;
             else
               ideal_prog_full <= #`TCQ 0;
           end
         end else
           ideal_prog_full   <= #`TCQ ideal_prog_full;
       //Two Programmable Full Threshold Inputs
       end else if (C_PROG_FULL_TYPE == 4) begin
         if (FULL == 0) begin
           if (C_PRELOAD_REGS == 1 && C_PRELOAD_LATENCY == 0) begin // FWFT
             if (diff_pntr >= (PROG_FULL_THRESH_ASSERT - EXTRA_WORDS_DC))
               ideal_prog_full <= #`TCQ 1;
             else if (diff_pntr < (PROG_FULL_THRESH_NEGATE - EXTRA_WORDS_DC))
               ideal_prog_full <= #`TCQ 0;
             else
               ideal_prog_full <= #`TCQ ideal_prog_full;
           end else begin // STD
             if (diff_pntr >= PROG_FULL_THRESH_ASSERT)
               ideal_prog_full <= #`TCQ 1;
             else if (diff_pntr < PROG_FULL_THRESH_NEGATE)
               ideal_prog_full <= #`TCQ 0;
             else
               ideal_prog_full <= #`TCQ ideal_prog_full;
           end
         end else
           ideal_prog_full   <= #`TCQ ideal_prog_full;
       end // C_PROG_FULL_TYPE

     end //wr_rst_i==0
   end //

   
   /**************************************************************************
   * Read Domain Logic
   **************************************************************************/


   /*********************************************************
    * Programmable EMPTY flags
    *********************************************************/
   //Determine the Assert and Negate thresholds for Programmable Empty

   wire [C_RD_PNTR_WIDTH-1:0] pe_thr_assert_val;
   wire [C_RD_PNTR_WIDTH-1:0] pe_thr_negate_val;
   reg [C_RD_PNTR_WIDTH-1:0] diff_pntr_rd      = 0;

   always @(posedge RD_CLK or posedge rd_rst_i) begin : gen_pe

     if (rd_rst_i) begin
       diff_pntr_rd       <= 0;
       ideal_prog_empty   <= 1'b1;
     end else begin
       if (ram_rd_en)
         diff_pntr_rd       <=  #`TCQ (adj_wr_pntr_rd - rd_pntr) - 1'h1;
       else if (!ram_rd_en)
         diff_pntr_rd       <=  #`TCQ (adj_wr_pntr_rd - rd_pntr);
       else
         diff_pntr_rd       <=  #`TCQ diff_pntr_rd;
  
       if (C_PROG_EMPTY_TYPE == 1) begin
         if (EMPTY == 0) begin
           if (diff_pntr_rd <= pe_thr_assert_val)
             ideal_prog_empty <= #`TCQ 1;
           else
             ideal_prog_empty <= #`TCQ 0;
         end else
           ideal_prog_empty   <= #`TCQ ideal_prog_empty;
       end else if (C_PROG_EMPTY_TYPE == 2) begin
         if (EMPTY == 0) begin
           if (diff_pntr_rd <= pe_thr_assert_val)
             ideal_prog_empty <= #`TCQ 1;
           else if (diff_pntr_rd > pe_thr_negate_val)
             ideal_prog_empty <= #`TCQ 0;
           else
             ideal_prog_empty <= #`TCQ ideal_prog_empty;
         end else
           ideal_prog_empty   <= #`TCQ ideal_prog_empty;
       end else if (C_PROG_EMPTY_TYPE == 3) begin
         if (EMPTY == 0) begin
           if (diff_pntr_rd <= pe_thr_assert_val)
             ideal_prog_empty <= #`TCQ 1;
           else
             ideal_prog_empty <= #`TCQ 0;
         end else
           ideal_prog_empty   <= #`TCQ ideal_prog_empty;
       end else if (C_PROG_EMPTY_TYPE == 4) begin
         if (EMPTY == 0) begin
           if (diff_pntr_rd <= pe_thr_assert_val)
             ideal_prog_empty <= #`TCQ 1;
           else if (diff_pntr_rd > pe_thr_negate_val)
             ideal_prog_empty <= #`TCQ 0;
           else
             ideal_prog_empty <= #`TCQ ideal_prog_empty;
         end else
           ideal_prog_empty   <= #`TCQ ideal_prog_empty;
       end  //C_PROG_EMPTY_TYPE
     end
   end // gen_pe

   generate if (C_PROG_EMPTY_TYPE == 3) begin : single_pe_thr_input
     assign pe_thr_assert_val = (C_PRELOAD_REGS == 1 && C_PRELOAD_LATENCY == 0) ?
                                PROG_EMPTY_THRESH - 2'h2 : PROG_EMPTY_THRESH;
   end endgenerate // single_pe_thr_input

   generate if (C_PROG_EMPTY_TYPE == 4) begin : multiple_pe_thr_input
     assign pe_thr_assert_val = (C_PRELOAD_REGS == 1 && C_PRELOAD_LATENCY == 0) ?
                                PROG_EMPTY_THRESH_ASSERT - 2'h2 : PROG_EMPTY_THRESH_ASSERT;
     assign pe_thr_negate_val = (C_PRELOAD_REGS == 1 && C_PRELOAD_LATENCY == 0) ?
                                PROG_EMPTY_THRESH_NEGATE - 2'h2 : PROG_EMPTY_THRESH_NEGATE;
   end endgenerate // multiple_pe_thr_input

   generate if (C_PROG_EMPTY_TYPE < 3) begin : single_multiple_pe_thr_const
     assign pe_thr_assert_val = (C_PRELOAD_REGS == 1 && C_PRELOAD_LATENCY == 0) ?
                                C_PROG_EMPTY_THRESH_ASSERT_VAL - 2'h2 : C_PROG_EMPTY_THRESH_ASSERT_VAL;
     assign pe_thr_negate_val = (C_PRELOAD_REGS == 1 && C_PRELOAD_LATENCY == 0) ?
                                C_PROG_EMPTY_THRESH_NEGATE_VAL - 2'h2 : C_PROG_EMPTY_THRESH_NEGATE_VAL;
   end endgenerate // single_multiple_pe_thr_const

   always @(posedge RD_CLK or posedge rd_rst_i) begin : gen_fifo_rp
     if (rd_rst_i && C_EN_SAFETY_CKT == 0)
       rd_pntr            <= 0;
     else if (C_EN_SAFETY_CKT == 1 && SAFETY_CKT_RD_RST == 1'b1)
       rd_pntr            <= #`TCQ 0;
   end
   always @(posedge RD_CLK or posedge rd_rst_i) begin : gen_fifo_r_as

     /****** Reset fifo (case 1)***************************************/
     if (rd_rst_i) begin
       num_rd_bits        <= 0;
       next_num_rd_bits    = 0;
       rd_ptr             <= C_RD_DEPTH -1;
       rd_pntr_wr1        <= 0;
       wr_ptr_rdclk       <= C_WR_DEPTH -1;
  
       // DRAM resets asynchronously
       if (C_MEMORY_TYPE == 2 && C_USE_DOUT_RST == 1)
          ideal_dout    <= dout_reset_val;
  
       // Reset err_type only if ECC is not selected
       if (C_USE_ECC == 0) begin
         err_type         <= 0;
         err_type_d1      <= 0;
         err_type_both    <= 0;
       end
       ideal_valid        <= 1'b0;
       ideal_rd_count     <= 0;

     end else begin //rd_rst_i==0

       rd_pntr_wr1   <= #`TCQ rd_pntr;

       //Determine the current number of words in the FIFO
       tmp_rd_listsize = (C_DEPTH_RATIO_WR > 1) ? num_rd_bits/C_DIN_WIDTH :
                         num_rd_bits/C_DOUT_WIDTH;
       wr_ptr_rdclk_next = wr_ptr;

       if (wr_ptr_rdclk < wr_ptr_rdclk_next) begin
         next_num_rd_bits = num_rd_bits +
                            C_DIN_WIDTH*(wr_ptr_rdclk +C_WR_DEPTH
                                         - wr_ptr_rdclk_next);
       end else begin
         next_num_rd_bits = num_rd_bits +
                             C_DIN_WIDTH*(wr_ptr_rdclk - wr_ptr_rdclk_next);
       end

       /*****************************************************************/
       // Read Operation - Read Latency 1
       /*****************************************************************/
       if (C_PRELOAD_LATENCY==1 || C_PRELOAD_LATENCY==2) begin
                 ideal_valid        <= #`TCQ 1'b0;

         if (ram_rd_en == 1'b1) begin

           if (EMPTY == 1'b1) begin

             //If the FIFO is completely empty, and is reporting empty
             if (tmp_rd_listsize/C_DEPTH_RATIO_WR <= 0)
               begin
                 //Do not change the contents of the FIFO

                 //Do not acknowledge the read from empty FIFO
                 ideal_valid        <= #`TCQ 1'b0;
                 //Reminder that FIFO is still empty

                 ideal_rd_count     <= #`TCQ num_read_words_sized_i;
               end // if (tmp_rd_listsize <= 0)

             //If the FIFO is one from empty, but it is reporting empty
             else if (tmp_rd_listsize/C_DEPTH_RATIO_WR == 1)
               begin
                 //Do not change the contents of the FIFO

                 //Do not acknowledge the read from empty FIFO
                 ideal_valid        <= #`TCQ 1'b0;
                 //Note that FIFO is no longer empty, but is almost empty (has one word left)

                 ideal_rd_count     <= #`TCQ num_read_words_sized_i;

               end // if (tmp_rd_listsize == 1)

             //If the FIFO is two from empty, and is reporting empty
             else if (tmp_rd_listsize/C_DEPTH_RATIO_WR == 2)
               begin
                 //Do not change the contents of the FIFO

                 //Do not acknowledge the read from empty FIFO
                 ideal_valid        <= #`TCQ 1'b0;
                 //Fifo has two words, so is neither empty or almost empty

                 ideal_rd_count     <= #`TCQ num_read_words_sized_i;

               end // if (tmp_rd_listsize == 2)

             //If the FIFO is not close to empty, but is reporting that it is
             // Treat the FIFO as empty this time, but unset EMPTY flags.
             if ((tmp_rd_listsize/C_DEPTH_RATIO_WR > 2) && (tmp_rd_listsize/C_DEPTH_RATIO_WR<C_FIFO_RD_DEPTH))
               begin
                 //Do not change the contents of the FIFO

                 //Do not acknowledge the read from empty FIFO
                 ideal_valid <= #`TCQ 1'b0;
                 //Note that the FIFO is No Longer Empty or Almost Empty

                 ideal_rd_count <= #`TCQ num_read_words_sized_i;

               end // if ((tmp_rd_listsize > 2) && (tmp_rd_listsize<=C_FIFO_RD_DEPTH-1))
             end // else: if(ideal_empty == 1'b1)

           else //if (ideal_empty == 1'b0)
             begin

               //If the FIFO is completely full, and we are successfully reading from it
               if (tmp_rd_listsize/C_DEPTH_RATIO_WR >= C_FIFO_RD_DEPTH)
                 begin
                   //Read the value from the FIFO
                   read_fifo;
                   next_num_rd_bits = next_num_rd_bits - C_DOUT_WIDTH;

                   //Acknowledge the read from the FIFO, no error
                   ideal_valid        <= #`TCQ 1'b1;
                   //Not close to empty

                   ideal_rd_count     <= #`TCQ num_read_words_sized_i;

                 end // if (tmp_rd_listsize == C_FIFO_RD_DEPTH)

               //If the FIFO is not close to being empty
               else if ((tmp_rd_listsize/C_DEPTH_RATIO_WR > 2) && (tmp_rd_listsize/C_DEPTH_RATIO_WR<=C_FIFO_RD_DEPTH))
                 begin
                   //Read the value from the FIFO
                   read_fifo;
                   next_num_rd_bits = next_num_rd_bits - C_DOUT_WIDTH;

                   //Acknowledge the read from the FIFO, no error
                   ideal_valid        <= #`TCQ 1'b1;
                   //Not close to empty

                   ideal_rd_count     <= #`TCQ num_read_words_sized_i;

                 end // if ((tmp_rd_listsize > 2) && (tmp_rd_listsize<=C_FIFO_RD_DEPTH-1))

               //If the FIFO is two from empty
               else if (tmp_rd_listsize/C_DEPTH_RATIO_WR == 2)
                 begin
                   //Read the value from the FIFO
                   read_fifo;
                   next_num_rd_bits = next_num_rd_bits - C_DOUT_WIDTH;

                   //Acknowledge the read from the FIFO, no error
                   ideal_valid        <= #`TCQ 1'b1;
                   //Fifo is not yet empty. It is going almost_empty

                   ideal_rd_count     <= #`TCQ num_read_words_sized_i;

                 end // if (tmp_rd_listsize == 2)

               //If the FIFO is one from empty
               else if ((tmp_rd_listsize/C_DEPTH_RATIO_WR == 1))
                 begin
                   //Read the value from the FIFO
                   read_fifo;
                   next_num_rd_bits = next_num_rd_bits - C_DOUT_WIDTH;

                   //Acknowledge the read from the FIFO, no error
                   ideal_valid        <= #`TCQ 1'b1;
                   //Note that FIFO is GOING empty

                   ideal_rd_count     <= #`TCQ num_read_words_sized_i;

                 end // if (tmp_rd_listsize == 1)


               //If the FIFO is completely empty
               else if (tmp_rd_listsize/C_DEPTH_RATIO_WR <= 0)
                 begin
                   //Do not change the contents of the FIFO

                   //Do not acknowledge the read from empty FIFO
                   ideal_valid        <= #`TCQ 1'b0;

                   ideal_rd_count     <= #`TCQ num_read_words_sized_i;

                 end // if (tmp_rd_listsize <= 0)

             end // if (ideal_empty == 1'b0)

           end //(RD_EN == 1'b1)

         else //if (RD_EN == 1'b0)
           begin
             //If user did not attempt a read, do not give an ack or err
             ideal_valid          <= #`TCQ 1'b0;

             ideal_rd_count       <= #`TCQ num_read_words_sized_i;

           end // else: !if(RD_EN == 1'b1)

       /*****************************************************************/
       // Read Operation - Read Latency 0
       /*****************************************************************/
       end else if (C_PRELOAD_REGS==1 && C_PRELOAD_LATENCY==0) begin
                 ideal_valid        <= #`TCQ 1'b0;
         if (ram_rd_en == 1'b1) begin

           if (EMPTY == 1'b1) begin

             //If the FIFO is completely empty, and is reporting empty
             if (tmp_rd_listsize/C_DEPTH_RATIO_WR <= 0) begin
               //Do not change the contents of the FIFO

               //Do not acknowledge the read from empty FIFO
               ideal_valid        <= #`TCQ 1'b0;
               //Reminder that FIFO is still empty

               ideal_rd_count     <= #`TCQ num_read_words_sized_i;

             //If the FIFO is one from empty, but it is reporting empty
             end else if (tmp_rd_listsize/C_DEPTH_RATIO_WR == 1) begin
               //Do not change the contents of the FIFO

               //Do not acknowledge the read from empty FIFO
               ideal_valid        <= #`TCQ 1'b0;
               //Note that FIFO is no longer empty, but is almost empty (has one word left)

               ideal_rd_count     <= #`TCQ num_read_words_sized_i;

             //If the FIFO is two from empty, and is reporting empty
             end else if (tmp_rd_listsize/C_DEPTH_RATIO_WR == 2) begin
               //Do not change the contents of the FIFO

               //Do not acknowledge the read from empty FIFO
               ideal_valid        <= #`TCQ 1'b0;
               //Fifo has two words, so is neither empty or almost empty

               ideal_rd_count     <= #`TCQ num_read_words_sized_i;

               //If the FIFO is not close to empty, but is reporting that it is
             // Treat the FIFO as empty this time, but unset EMPTY flags.
             end else if ((tmp_rd_listsize/C_DEPTH_RATIO_WR > 2) &&
                         (tmp_rd_listsize/C_DEPTH_RATIO_WR<C_FIFO_RD_DEPTH)) begin
               //Do not change the contents of the FIFO

               //Do not acknowledge the read from empty FIFO
               ideal_valid        <= #`TCQ 1'b0;
               //Note that the FIFO is No Longer Empty or Almost Empty

               ideal_rd_count     <= #`TCQ num_read_words_sized_i;

             end // if ((tmp_rd_listsize > 2) && (tmp_rd_listsize<=C_FIFO_RD_DEPTH-1))

           end else begin

             //If the FIFO is completely full, and we are successfully reading from it
             if (tmp_rd_listsize/C_DEPTH_RATIO_WR >= C_FIFO_RD_DEPTH) begin
               //Read the value from the FIFO
               read_fifo;
               next_num_rd_bits = next_num_rd_bits - C_DOUT_WIDTH;

               //Acknowledge the read from the FIFO, no error
               ideal_valid        <= #`TCQ 1'b1;
               //Not close to empty

               ideal_rd_count     <= #`TCQ num_read_words_sized_i;

             //If the FIFO is not close to being empty
             end else if ((tmp_rd_listsize/C_DEPTH_RATIO_WR > 2) &&
                          (tmp_rd_listsize/C_DEPTH_RATIO_WR<=C_FIFO_RD_DEPTH)) begin
               //Read the value from the FIFO
               read_fifo;
               next_num_rd_bits = next_num_rd_bits - C_DOUT_WIDTH;

               //Acknowledge the read from the FIFO, no error
               ideal_valid        <= #`TCQ 1'b1;
               //Not close to empty

               ideal_rd_count     <= #`TCQ num_read_words_sized_i;

             //If the FIFO is two from empty
             end else if (tmp_rd_listsize/C_DEPTH_RATIO_WR == 2) begin
               //Read the value from the FIFO
               read_fifo;
               next_num_rd_bits = next_num_rd_bits - C_DOUT_WIDTH;

               //Acknowledge the read from the FIFO, no error
               ideal_valid        <= #`TCQ 1'b1;
               //Fifo is not yet empty. It is going almost_empty

               ideal_rd_count     <= #`TCQ num_read_words_sized_i;

             //If the FIFO is one from empty
             end else if (tmp_rd_listsize/C_DEPTH_RATIO_WR == 1) begin
               //Read the value from the FIFO
               read_fifo;
               next_num_rd_bits = next_num_rd_bits - C_DOUT_WIDTH;

               //Acknowledge the read from the FIFO, no error
               ideal_valid        <= #`TCQ 1'b1;
               //Note that FIFO is GOING empty

               ideal_rd_count     <= #`TCQ num_read_words_sized_i;

             //If the FIFO is completely empty
             end else if (tmp_rd_listsize/C_DEPTH_RATIO_WR <= 0) begin
               //Do not change the contents of the FIFO

               //Do not acknowledge the read from empty FIFO
               ideal_valid        <= #`TCQ 1'b0;
               //Reminder that FIFO is still empty

               ideal_rd_count     <= #`TCQ num_read_words_sized_i;

             end // if (tmp_rd_listsize <= 0)

           end // if (ideal_empty == 1'b0)

         end else begin//(RD_EN == 1'b0)

         
           //If user did not attempt a read, do not give an ack or err
           ideal_valid           <= #`TCQ 1'b0;
           ideal_rd_count        <= #`TCQ num_read_words_sized_i;

         end // else: !if(RD_EN == 1'b1)
       end //if (C_PRELOAD_REGS==1 && C_PRELOAD_LATENCY==0)

       num_rd_bits      <= #`TCQ next_num_rd_bits;
       wr_ptr_rdclk     <= #`TCQ wr_ptr;
     end //rd_rst_i==0
   end //always gen_fifo_r_as

endmodule // fifo_generator_v13_1_2_bhv_ver_as


/*******************************************************************************
 * Declaration of Low Latency Asynchronous FIFO
 ******************************************************************************/
module fifo_generator_v13_1_2_beh_ver_ll_afifo
   
  /***************************************************************************
   * Declare user parameters and their defaults
   ***************************************************************************/
  #(
    parameter  C_DIN_WIDTH                    = 8,
    parameter  C_DOUT_RST_VAL                 = "",
    parameter  C_DOUT_WIDTH                   = 8,
    parameter  C_FULL_FLAGS_RST_VAL           = 1,
    parameter  C_HAS_RD_DATA_COUNT            = 0,
    parameter  C_HAS_WR_DATA_COUNT            = 0,
    parameter  C_RD_DEPTH                     = 256,
    parameter  C_RD_PNTR_WIDTH                = 8,
    parameter  C_USE_DOUT_RST                 = 0,
    parameter  C_WR_DATA_COUNT_WIDTH          = 2,
    parameter  C_WR_DEPTH                     = 256,
    parameter  C_WR_PNTR_WIDTH                = 8,
    parameter  C_FIFO_TYPE                    = 0
   )

  /***************************************************************************
   * Declare Input and Output Ports
   ***************************************************************************/
  (
   input       [C_DIN_WIDTH-1:0]                 DIN,
   input                                         RD_CLK,
   input                                         RD_EN,
   input                                         WR_RST,
   input                                         RD_RST,
   input                                         WR_CLK,
   input                                         WR_EN,
   output reg  [C_DOUT_WIDTH-1:0]                DOUT = 0,
   output reg                                    EMPTY = 1'b1,
   output reg                                    FULL = C_FULL_FLAGS_RST_VAL
  );

  //-----------------------------------------------------------------------------
  // Low Latency Asynchronous FIFO
  //-----------------------------------------------------------------------------

  // Memory which will be used to simulate a FIFO
  reg [C_DIN_WIDTH-1:0] memory[C_WR_DEPTH-1:0];
  integer i;
  initial begin
    for (i = 0; i < C_WR_DEPTH; i = i + 1)
      memory[i] = 0;
  end

  reg  [C_WR_PNTR_WIDTH-1:0] wr_pntr_ll_afifo = 0;
  wire [C_RD_PNTR_WIDTH-1:0] rd_pntr_ll_afifo;
  reg  [C_RD_PNTR_WIDTH-1:0] rd_pntr_ll_afifo_q = 0;
  reg                        ll_afifo_full    = 1'b0;
  reg                        ll_afifo_empty   = 1'b1;
  wire                       write_allow;
  wire                       read_allow;

  assign write_allow = WR_EN & ~ll_afifo_full;
  assign read_allow  = RD_EN & ~ll_afifo_empty;

  //-----------------------------------------------------------------------------
  // Write Pointer Generation
  //-----------------------------------------------------------------------------
  always @(posedge WR_CLK or posedge WR_RST) begin
    if (WR_RST)
      wr_pntr_ll_afifo   <= 0;
    else if (write_allow)
      wr_pntr_ll_afifo <= #`TCQ wr_pntr_ll_afifo + 1;
  end

  //-----------------------------------------------------------------------------
  // Read Pointer Generation
  //-----------------------------------------------------------------------------
  always @(posedge RD_CLK or posedge RD_RST) begin
    if (RD_RST)
      rd_pntr_ll_afifo_q   <= 0;
    else
      rd_pntr_ll_afifo_q <= #`TCQ rd_pntr_ll_afifo;
  end
  assign rd_pntr_ll_afifo = read_allow ? rd_pntr_ll_afifo_q + 1 : rd_pntr_ll_afifo_q;
  
  //-----------------------------------------------------------------------------
  // Fill the Memory
  //-----------------------------------------------------------------------------
  always @(posedge WR_CLK) begin
    if (write_allow)
      memory[wr_pntr_ll_afifo] <= #`TCQ DIN;
  end

  //-----------------------------------------------------------------------------
  // Generate DOUT
  //-----------------------------------------------------------------------------
  always @(posedge RD_CLK) begin
      DOUT <= #`TCQ memory[rd_pntr_ll_afifo];
  end

  //-----------------------------------------------------------------------------
  // Generate EMPTY
  //-----------------------------------------------------------------------------
  always @(posedge RD_CLK or posedge RD_RST) begin
    if (RD_RST)
      ll_afifo_empty   <= 1'b1;
    else
      ll_afifo_empty   <= ((wr_pntr_ll_afifo == rd_pntr_ll_afifo_q) | 
                           (read_allow & (wr_pntr_ll_afifo == (rd_pntr_ll_afifo_q + 2'h1))));
  end

  //-----------------------------------------------------------------------------
  // Generate FULL
  //-----------------------------------------------------------------------------
  always @(posedge WR_CLK or posedge WR_RST) begin
    if (WR_RST)
      ll_afifo_full   <= 1'b1;
    else
      ll_afifo_full   <= ((rd_pntr_ll_afifo_q == (wr_pntr_ll_afifo + 2'h1)) | 
                           (write_allow & (rd_pntr_ll_afifo_q == (wr_pntr_ll_afifo + 2'h2))));
  end

  always @* begin
    FULL  <= ll_afifo_full;
    EMPTY <= ll_afifo_empty;
  end

endmodule // fifo_generator_v13_1_2_beh_ver_ll_afifo

/*******************************************************************************
 * Declaration of top-level module
 ******************************************************************************/
module fifo_generator_v13_1_2_bhv_ver_ss
   
  /**************************************************************************
   * Declare user parameters and their defaults
   *************************************************************************/
  #(
    parameter  C_FAMILY                       = "virtex7",
    parameter  C_DATA_COUNT_WIDTH             = 2,
    parameter  C_DIN_WIDTH                    = 8,
    parameter  C_DOUT_RST_VAL                 = "",
    parameter  C_DOUT_WIDTH                   = 8,
    parameter  C_FULL_FLAGS_RST_VAL           = 1,
    parameter  C_HAS_ALMOST_EMPTY             = 0,
    parameter  C_HAS_ALMOST_FULL              = 0,
    parameter  C_HAS_DATA_COUNT               = 0,
    parameter  C_HAS_OVERFLOW                 = 0,
    parameter  C_HAS_RD_DATA_COUNT            = 0,
    parameter  C_HAS_RST                      = 0,
    parameter  C_HAS_SRST                     = 0,
    parameter  C_HAS_UNDERFLOW                = 0,
    parameter  C_HAS_VALID                    = 0,
    parameter  C_HAS_WR_ACK                   = 0,
    parameter  C_HAS_WR_DATA_COUNT            = 0,
    parameter  C_IMPLEMENTATION_TYPE          = 0,
    parameter  C_MEMORY_TYPE                  = 1,
    parameter  C_OVERFLOW_LOW                 = 0,
    parameter  C_PRELOAD_LATENCY              = 1,
    parameter  C_PRELOAD_REGS                 = 0,
    parameter  C_PROG_EMPTY_THRESH_ASSERT_VAL = 0,
    parameter  C_PROG_EMPTY_THRESH_NEGATE_VAL = 0,
    parameter  C_PROG_EMPTY_TYPE              = 0,
    parameter  C_PROG_FULL_THRESH_ASSERT_VAL  = 0,
    parameter  C_PROG_FULL_THRESH_NEGATE_VAL  = 0,
    parameter  C_PROG_FULL_TYPE               = 0,
    parameter  C_RD_DATA_COUNT_WIDTH          = 2,
    parameter  C_RD_DEPTH                     = 256,
    parameter  C_RD_PNTR_WIDTH                = 8,
    parameter  C_UNDERFLOW_LOW                = 0,
    parameter  C_USE_DOUT_RST                 = 0,
    parameter  C_USE_EMBEDDED_REG             = 0,
    parameter  C_EN_SAFETY_CKT                = 0,
    parameter  C_USE_FWFT_DATA_COUNT          = 0,
    parameter  C_VALID_LOW                    = 0,
    parameter  C_WR_ACK_LOW                   = 0,
    parameter  C_WR_DATA_COUNT_WIDTH          = 2,
    parameter  C_WR_DEPTH                     = 256,
    parameter  C_WR_PNTR_WIDTH                = 8,
    parameter  C_USE_ECC                      = 0, 
    parameter  C_ENABLE_RST_SYNC              = 1,
    parameter  C_ERROR_INJECTION_TYPE         = 0,
    parameter  C_FIFO_TYPE                    = 0 
   )
   
  /**************************************************************************
   * Declare Input and Output Ports
   *************************************************************************/
   (
    //Inputs
    input                                 SAFETY_CKT_WR_RST,
    input                                 CLK,
    input       [C_DIN_WIDTH-1:0]         DIN,
    input       [C_RD_PNTR_WIDTH-1:0]     PROG_EMPTY_THRESH,
    input       [C_RD_PNTR_WIDTH-1:0]     PROG_EMPTY_THRESH_ASSERT,
    input       [C_RD_PNTR_WIDTH-1:0]     PROG_EMPTY_THRESH_NEGATE,
    input       [C_WR_PNTR_WIDTH-1:0]     PROG_FULL_THRESH,
    input       [C_WR_PNTR_WIDTH-1:0]     PROG_FULL_THRESH_ASSERT,
    input       [C_WR_PNTR_WIDTH-1:0]     PROG_FULL_THRESH_NEGATE,
    input                                 RD_EN,
    input                                 RD_EN_USER,
    input                                 USER_EMPTY_FB,
    input                                 RST,
    input                                 RST_FULL_GEN,
    input                                 RST_FULL_FF,
    input                                 SRST,
    input                                 WR_EN,
    input                                 INJECTDBITERR,
    input                                 INJECTSBITERR,
    input                                 WR_RST_BUSY,
    input                                 RD_RST_BUSY,
                                    
    //Outputs                       
    output                                ALMOST_EMPTY,
    output                                ALMOST_FULL,
    output reg   [C_DATA_COUNT_WIDTH-1:0] DATA_COUNT = 0,
    output       [C_DOUT_WIDTH-1:0]       DOUT,
    output                                EMPTY,
    output reg                            EMPTY_FB = 1'b1,
    output                                FULL,
    output                                OVERFLOW,
    output [C_RD_DATA_COUNT_WIDTH-1:0]    RD_DATA_COUNT,
    output [C_WR_DATA_COUNT_WIDTH-1:0]    WR_DATA_COUNT,
    output                                PROG_EMPTY,
    output                                PROG_FULL,
    output                                VALID,
    output                                UNDERFLOW,
    output                                WR_ACK,
    output                                SBITERR,
    output                                DBITERR
   );


   reg  [C_RD_PNTR_WIDTH:0] rd_data_count_int = 0;
   reg  [C_WR_PNTR_WIDTH:0] wr_data_count_int = 0;
   wire [C_RD_PNTR_WIDTH:0] rd_data_count_i_ss;
   wire [C_WR_PNTR_WIDTH:0] wr_data_count_i_ss;
   reg  [C_WR_PNTR_WIDTH:0] wdc_fwft_ext_as = 0;
   /***************************************************************************
    * Parameters used as constants
    **************************************************************************/
  localparam IS_8SERIES         = (C_FAMILY == "virtexu" || C_FAMILY == "kintexu" || C_FAMILY == "artixu" || C_FAMILY == "virtexuplus" || C_FAMILY == "zynquplus" || C_FAMILY == "kintexuplus") ? 1 : 0;
   localparam C_DEPTH_RATIO_WR =  
      (C_WR_DEPTH>C_RD_DEPTH) ? (C_WR_DEPTH/C_RD_DEPTH) : 1;
   localparam C_DEPTH_RATIO_RD =  
      (C_RD_DEPTH>C_WR_DEPTH) ? (C_RD_DEPTH/C_WR_DEPTH) : 1;
   //localparam C_FIFO_WR_DEPTH = C_WR_DEPTH - 1;
   //localparam C_FIFO_RD_DEPTH = C_RD_DEPTH - 1;
   localparam C_GRTR_PNTR_WIDTH = (C_WR_PNTR_WIDTH > C_RD_PNTR_WIDTH) ? C_WR_PNTR_WIDTH : C_RD_PNTR_WIDTH ; 


   //  C_DEPTH_RATIO_WR | C_DEPTH_RATIO_RD | C_PNTR_WIDTH    | EXTRA_WORDS_DC
   //  -----------------|------------------|-----------------|---------------
   //  1                | 8                | C_RD_PNTR_WIDTH | 2
   //  1                | 4                | C_RD_PNTR_WIDTH | 2
   //  1                | 2                | C_RD_PNTR_WIDTH | 2
   //  1                | 1                | C_WR_PNTR_WIDTH | 2
   //  2                | 1                | C_WR_PNTR_WIDTH | 4
   //  4                | 1                | C_WR_PNTR_WIDTH | 8
   //  8                | 1                | C_WR_PNTR_WIDTH | 16
   
   localparam C_PNTR_WIDTH  = (C_WR_PNTR_WIDTH>=C_RD_PNTR_WIDTH) ? C_WR_PNTR_WIDTH : C_RD_PNTR_WIDTH;
   wire [C_PNTR_WIDTH:0] EXTRA_WORDS_DC = (C_DEPTH_RATIO_WR == 1) ? 2 : (2 * C_DEPTH_RATIO_WR/C_DEPTH_RATIO_RD);
   wire [C_WR_PNTR_WIDTH:0] EXTRA_WORDS_PF = (C_DEPTH_RATIO_WR == 1) ? 2 : (2 * C_DEPTH_RATIO_WR/C_DEPTH_RATIO_RD);
   //wire [C_RD_PNTR_WIDTH:0] EXTRA_WORDS_PE = (C_DEPTH_RATIO_RD == 1) ? 2 : (2 * C_DEPTH_RATIO_RD/C_DEPTH_RATIO_WR);
   localparam  EXTRA_WORDS_PF_PARAM = (C_DEPTH_RATIO_WR == 1) ? 2 : (2 * C_DEPTH_RATIO_WR/C_DEPTH_RATIO_RD);
   //localparam  EXTRA_WORDS_PE_PARAM  = (C_DEPTH_RATIO_RD == 1) ? 2 : (2 * C_DEPTH_RATIO_RD/C_DEPTH_RATIO_WR);

   localparam [31:0] reads_per_write = C_DIN_WIDTH/C_DOUT_WIDTH;
   
   localparam [31:0] log2_reads_per_write = log2_val(reads_per_write);
   
   localparam [31:0] writes_per_read = C_DOUT_WIDTH/C_DIN_WIDTH;
   
   localparam [31:0] log2_writes_per_read = log2_val(writes_per_read);


   //When RST is present, set FULL reset value to '1'.
   //If core has no RST, make sure FULL powers-on as '0'.
   //The reset value assignments for FULL, ALMOST_FULL, and PROG_FULL are not 
   //changed for v3.2(IP2_Im). When the core has Sync Reset, C_HAS_SRST=1 and C_HAS_RST=0.
   // Therefore, during SRST, all the FULL flags reset to 0.
   localparam                      C_HAS_FAST_FIFO = 0;
   localparam                      C_FIFO_WR_DEPTH = C_WR_DEPTH;
   localparam                      C_FIFO_RD_DEPTH = C_RD_DEPTH;
   // Local parameters used to determine whether to inject ECC error or not
   localparam SYMMETRIC_PORT = (C_DIN_WIDTH == C_DOUT_WIDTH) ? 1 : 0;
   localparam ERR_INJECTION = (C_ERROR_INJECTION_TYPE != 0) ? 1 : 0;
   localparam C_USE_ECC_1 = (C_USE_ECC == 1 || C_USE_ECC ==2) ? 1:0;
   localparam ENABLE_ERR_INJECTION = C_USE_ECC && SYMMETRIC_PORT && ERR_INJECTION;
   localparam C_DATA_WIDTH = (ENABLE_ERR_INJECTION == 1) ? (C_DIN_WIDTH+2) : C_DIN_WIDTH;
   localparam IS_ASYMMETRY = (C_DIN_WIDTH == C_DOUT_WIDTH) ? 0 : 1;
   localparam LESSER_WIDTH = (C_RD_PNTR_WIDTH > C_WR_PNTR_WIDTH) ? C_WR_PNTR_WIDTH : C_RD_PNTR_WIDTH;
  localparam [C_RD_PNTR_WIDTH-1 : 0] DIFF_MAX_RD = {C_RD_PNTR_WIDTH{1'b1}}; 
  localparam [C_WR_PNTR_WIDTH-1 : 0] DIFF_MAX_WR = {C_WR_PNTR_WIDTH{1'b1}}; 


   /**************************************************************************
    * FIFO Contents Tracking and Data Count Calculations
    *************************************************************************/
   // Memory which will be used to simulate a FIFO
   reg [C_DIN_WIDTH-1:0] memory[C_WR_DEPTH-1:0];
   reg [1:0] ecc_err[C_WR_DEPTH-1:0];

   
   /**************************************************************************
    * Internal Registers and wires
    *************************************************************************/

   //Temporary signals used for calculating the model's outputs. These
   //are only used in the assign statements immediately following wire,
   //parameter, and function declarations.
   wire                           underflow_i;
   wire                           valid_i;
   wire                           valid_out;
   reg [31:0]  num_wr_bits;
   reg [31:0]  num_rd_bits;
   reg [31:0]  next_num_wr_bits;
   reg [31:0]  next_num_rd_bits;

   //The write pointer - tracks write operations
   // (Works opposite to core: wr_ptr is a DOWN counter)
   reg  [31:0]                 wr_ptr;
   reg  [C_WR_PNTR_WIDTH-1:0]  wr_pntr_rd1    = 0;
   reg  [C_WR_PNTR_WIDTH-1:0]  wr_pntr_rd2    = 0;
   reg  [C_WR_PNTR_WIDTH-1:0]  wr_pntr_rd3    = 0;
   reg  [C_WR_PNTR_WIDTH-1:0]  wr_pntr_rd     = 0;
   reg                         wr_rst_d1      =0;

   //The read pointer - tracks read operations
   // (rd_ptr Works opposite to core: rd_ptr is a DOWN counter)
   reg  [31:0]                 rd_ptr;
   reg  [C_RD_PNTR_WIDTH-1:0]  rd_pntr_wr1 = 0;
   reg  [C_RD_PNTR_WIDTH-1:0]  rd_pntr_wr2 = 0;
   reg  [C_RD_PNTR_WIDTH-1:0]  rd_pntr_wr3 = 0;
   reg  [C_RD_PNTR_WIDTH-1:0]  rd_pntr_wr4 = 0;
   reg  [C_RD_PNTR_WIDTH-1:0]  rd_pntr_wr  = 0;

   wire                        ram_rd_en;
   wire                        empty_int;
   wire                        almost_empty_int;
   wire                        ram_wr_en;
   wire                        full_int;
   wire                        almost_full_int;
   reg                         ram_rd_en_reg = 1'b0;
   reg                         ram_rd_en_d1 = 1'b0;
   reg                         fab_rd_en_d1 = 1'b0;
   wire                         srst_rrst_busy;



   //Ideal FIFO signals. These are the raw output of the behavioral model,
   //which behaves like an ideal FIFO.
   reg [1:0]                      err_type           = 0;
   reg [1:0]                      err_type_d1        = 0;
   reg [1:0]                      err_type_both      = 0;
   reg  [C_DOUT_WIDTH-1:0]        ideal_dout         = 0;
   reg  [C_DOUT_WIDTH-1:0]        ideal_dout_d1      = 0;
   reg  [C_DOUT_WIDTH-1:0]        ideal_dout_both      = 0;
   wire [C_DOUT_WIDTH-1:0]        ideal_dout_out;
   wire                           fwft_enabled;
   reg                            ideal_wr_ack       = 0;
   reg                            ideal_valid        = 0;
   reg                            ideal_overflow     = C_OVERFLOW_LOW;
   reg                            ideal_underflow    = C_UNDERFLOW_LOW;

   reg                            full_i             = C_FULL_FLAGS_RST_VAL;
   reg                            full_i_temp        = 0;
   reg                            empty_i            = 1;
   reg                            almost_full_i      = 0;
   reg                            almost_empty_i     = 1;
   reg                            prog_full_i        = 0;
   reg                            prog_empty_i       = 1;
   reg [C_WR_PNTR_WIDTH-1:0]      wr_pntr            = 0;
   reg [C_RD_PNTR_WIDTH-1:0]      rd_pntr            = 0;
   wire [C_RD_PNTR_WIDTH-1:0]  adj_wr_pntr_rd;
   wire [C_WR_PNTR_WIDTH-1:0]  adj_rd_pntr_wr;
   reg [C_RD_PNTR_WIDTH-1:0]      diff_count         = 0;

   reg                            write_allow_q      = 0;
   reg                            read_allow_q       = 0;
   reg                            valid_d1           = 0;
   reg                            valid_both           = 0;
   reg                            valid_d2           = 0;
   wire                           rst_i;
   wire                           srst_i;

   //user specified value for reseting the size of the fifo
   reg [C_DOUT_WIDTH-1:0]         dout_reset_val = 0;

   reg [31:0]  wr_ptr_rdclk;
   reg [31:0]  wr_ptr_rdclk_next;
   reg [31:0]  rd_ptr_wrclk;
   reg [31:0]  rd_ptr_wrclk_next;




   /****************************************************************************
    * Function Declarations
    ***************************************************************************/

   /****************************************************************************
    * hexstr_conv
    *   Converts a string of type hex to a binary value (for C_DOUT_RST_VAL)
    ***************************************************************************/
    function [C_DOUT_WIDTH-1:0] hexstr_conv;
    input [(C_DOUT_WIDTH*8)-1:0] def_data;

    integer index,i,j;
    reg [3:0] bin;

    begin
      index = 0;
      hexstr_conv = 'b0;
      for( i=C_DOUT_WIDTH-1; i>=0; i=i-1 ) begin
        case (def_data[7:0])
          8'b00000000 : begin
            bin = 4'b0000;
            i = -1;
          end
          8'b00110000 : bin = 4'b0000;
          8'b00110001 : bin = 4'b0001;
          8'b00110010 : bin = 4'b0010;
          8'b00110011 : bin = 4'b0011;
          8'b00110100 : bin = 4'b0100;
          8'b00110101 : bin = 4'b0101;
          8'b00110110 : bin = 4'b0110;
          8'b00110111 : bin = 4'b0111;
          8'b00111000 : bin = 4'b1000;
          8'b00111001 : bin = 4'b1001;
          8'b01000001 : bin = 4'b1010;
          8'b01000010 : bin = 4'b1011;
          8'b01000011 : bin = 4'b1100;
          8'b01000100 : bin = 4'b1101;
          8'b01000101 : bin = 4'b1110;
          8'b01000110 : bin = 4'b1111;
          8'b01100001 : bin = 4'b1010;
          8'b01100010 : bin = 4'b1011;
          8'b01100011 : bin = 4'b1100;
          8'b01100100 : bin = 4'b1101;
          8'b01100101 : bin = 4'b1110;
          8'b01100110 : bin = 4'b1111;
          default : begin
            bin = 4'bx;
          end
        endcase
        for( j=0; j<4; j=j+1) begin
          if ((index*4)+j < C_DOUT_WIDTH) begin
            hexstr_conv[(index*4)+j] = bin[j];
          end
        end
        index = index + 1;
        def_data = def_data >> 8;
      end
    end
  endfunction
 /**************************************************************************
  * log2_val
  *   Returns the 'log2' value for the input value for the supported ratios
  ***************************************************************************/
  function [31:0] log2_val;
    input [31:0] binary_val;

    begin
      if (binary_val == 8) begin
        log2_val = 3;
      end else if (binary_val == 4) begin
        log2_val = 2;
      end else begin
        log2_val = 1;
      end
    end
  endfunction

   reg                     ideal_prog_full          = 0;
   reg                     ideal_prog_empty         = 1;
   reg [C_WR_DATA_COUNT_WIDTH-1 : 0] ideal_wr_count = 0;
   reg [C_RD_DATA_COUNT_WIDTH-1 : 0] ideal_rd_count = 0;

   //Assorted reg values for delayed versions of signals   
   //reg         valid_d1     = 0;
   
   
   //user specified value for reseting the size of the fifo
   //reg [C_DOUT_WIDTH-1:0]            dout_reset_val = 0;
   
   //temporary registers for WR_RESPONSE_LATENCY feature
   
   integer                           tmp_wr_listsize;
   integer                           tmp_rd_listsize;
   
   //Signal for registered version of prog full and empty
   
   //Threshold values for Programmable Flags
   integer                           prog_empty_actual_thresh_assert;
   integer                           prog_empty_actual_thresh_negate;
   integer                           prog_full_actual_thresh_assert;
   integer                           prog_full_actual_thresh_negate;


 /**************************************************************************
   * write_fifo
   *   This task writes a word to the FIFO memory and updates the 
   * write pointer.
   *   FIFO size is relative to write domain.
  ***************************************************************************/
  task write_fifo;
    begin
      memory[wr_ptr]     <= DIN;
      wr_pntr <= #`TCQ wr_pntr + 1;
      // Store the type of error injection (double/single) on write
      case (C_ERROR_INJECTION_TYPE)
        3:       ecc_err[wr_ptr]    <= {INJECTDBITERR,INJECTSBITERR};
        2:       ecc_err[wr_ptr]    <= {INJECTDBITERR,1'b0};
        1:       ecc_err[wr_ptr]    <= {1'b0,INJECTSBITERR};
        default: ecc_err[wr_ptr]    <= 0;
      endcase
      // (Works opposite to core: wr_ptr is a DOWN counter)
      if (wr_ptr == 0) begin
        wr_ptr          <= C_WR_DEPTH - 1;
      end else begin
        wr_ptr          <= wr_ptr - 1;
      end
    end
  endtask // write_fifo

  /**************************************************************************
   * read_fifo
   *   This task reads a word from the FIFO memory and updates the read 
   * pointer. It's output is the ideal_dout bus.
   *   FIFO size is relative to write domain.
   ***************************************************************************/
  task read_fifo;
    integer i;
    reg [C_DOUT_WIDTH-1:0]      tmp_dout;
    reg [C_DIN_WIDTH-1:0]       memory_read;
    reg [31:0]                  tmp_rd_ptr;
    reg [31:0]                  rd_ptr_high;
    reg [31:0]                  rd_ptr_low;
    reg [1:0]                   tmp_ecc_err;
    begin
      rd_pntr <= #`TCQ rd_pntr + 1;

      // output is wider than input
      if (reads_per_write == 0) begin
        tmp_dout = 0;
        tmp_rd_ptr = (rd_ptr << log2_writes_per_read)+(writes_per_read-1);
        for (i = writes_per_read - 1; i >= 0; i = i - 1) begin
          tmp_dout = tmp_dout << C_DIN_WIDTH;
          tmp_dout = tmp_dout | memory[tmp_rd_ptr];
           
          // (Works opposite to core: rd_ptr is a DOWN counter)
          if (tmp_rd_ptr == 0) begin
            tmp_rd_ptr = C_WR_DEPTH - 1;
          end else begin
            tmp_rd_ptr = tmp_rd_ptr - 1;
          end
        end

      // output is symmetric
      end else if (reads_per_write == 1) begin
        tmp_dout = memory[rd_ptr][C_DIN_WIDTH-1:0];
        // Retreive the error injection type. Based on the error injection type
        // corrupt the output data.
        tmp_ecc_err = ecc_err[rd_ptr];
        if (ENABLE_ERR_INJECTION && C_DIN_WIDTH == C_DOUT_WIDTH) begin
          if (tmp_ecc_err[1]) begin // Corrupt the output data only for double bit error
            if (C_DOUT_WIDTH == 1) begin
              $display("FAILURE : Data width must be >= 2 for double bit error injection.");
              $finish;
            end else if (C_DOUT_WIDTH == 2)
              tmp_dout = {~tmp_dout[C_DOUT_WIDTH-1],~tmp_dout[C_DOUT_WIDTH-2]};
            else
              tmp_dout = {~tmp_dout[C_DOUT_WIDTH-1],~tmp_dout[C_DOUT_WIDTH-2],(tmp_dout << 2)};
          end else begin
            tmp_dout = tmp_dout[C_DOUT_WIDTH-1:0];
          end
          err_type <= {tmp_ecc_err[1], tmp_ecc_err[0] & !tmp_ecc_err[1]};
        end else begin
          err_type <= 0;
        end

      // input is wider than output
      end else begin
        rd_ptr_high = rd_ptr >> log2_reads_per_write;
        rd_ptr_low  = rd_ptr & (reads_per_write - 1);
        memory_read = memory[rd_ptr_high];
        tmp_dout    = memory_read >> (rd_ptr_low*C_DOUT_WIDTH);
      end
      ideal_dout <= tmp_dout;
       
      // (Works opposite to core: rd_ptr is a DOWN counter)
     if (rd_ptr == 0) begin
        rd_ptr <= C_RD_DEPTH - 1;
      end else begin
        rd_ptr <= rd_ptr - 1;
      end

     end
  endtask


   
  /*************************************************************************
  * Initialize Signals for clean power-on simulation
  *************************************************************************/
   initial begin
      num_wr_bits        = 0;
      num_rd_bits        = 0;
      next_num_wr_bits   = 0;
      next_num_rd_bits   = 0;
      rd_ptr             = C_RD_DEPTH - 1;
      wr_ptr             = C_WR_DEPTH - 1;
      wr_pntr            = 0;
      rd_pntr            = 0;
      rd_ptr_wrclk       = rd_ptr;
      wr_ptr_rdclk       = wr_ptr;
      dout_reset_val     = hexstr_conv(C_DOUT_RST_VAL);
      ideal_dout         = dout_reset_val;
      err_type           = 0;
      err_type_d1        = 0;
      err_type_both      = 0;
      ideal_dout_d1      = dout_reset_val;
      ideal_dout_both    = dout_reset_val;
      ideal_wr_ack       = 1'b0;
      ideal_valid        = 1'b0;
      valid_d1           = 1'b0;
      valid_both         = 1'b0;
      ideal_overflow     = C_OVERFLOW_LOW;
      ideal_underflow    = C_UNDERFLOW_LOW;
      ideal_wr_count     = 0;
      ideal_rd_count     = 0;
      ideal_prog_full    = 1'b0;
      ideal_prog_empty   = 1'b1;

   end


  /*************************************************************************
   * Connect the module inputs and outputs to the internal signals of the
   * behavioral model.
   *************************************************************************/
   //Inputs
   /*
   wire CLK;
   wire [C_DIN_WIDTH-1:0] DIN;
   wire [C_RD_PNTR_WIDTH-1:0] PROG_EMPTY_THRESH;
   wire [C_RD_PNTR_WIDTH-1:0] PROG_EMPTY_THRESH_ASSERT;
   wire [C_RD_PNTR_WIDTH-1:0] PROG_EMPTY_THRESH_NEGATE;
   wire [C_WR_PNTR_WIDTH-1:0] PROG_FULL_THRESH;
   wire [C_WR_PNTR_WIDTH-1:0] PROG_FULL_THRESH_ASSERT;
   wire [C_WR_PNTR_WIDTH-1:0] PROG_FULL_THRESH_NEGATE;
   wire RD_EN;
   wire RST;
   wire WR_EN;
    */

  // Assign ALMOST_EPMTY
  generate if (C_HAS_ALMOST_EMPTY == 1) begin : gae
    assign ALMOST_EMPTY = almost_empty_i;
  end else begin : gnae
    assign ALMOST_EMPTY = 0;
  end endgenerate // gae

  // Assign ALMOST_FULL
  generate if (C_HAS_ALMOST_FULL==1) begin : gaf
    assign ALMOST_FULL  = almost_full_i;
  end else begin : gnaf
    assign ALMOST_FULL  = 0;
  end endgenerate // gaf

   // Dout may change behavior based on latency
  localparam C_FWFT_ENABLED = (C_PRELOAD_LATENCY == 0 && C_PRELOAD_REGS == 1)?
                         1: 0;
  assign fwft_enabled = (C_PRELOAD_LATENCY == 0 && C_PRELOAD_REGS == 1)?
                         1: 0;
  assign ideal_dout_out= ((C_USE_EMBEDDED_REG>0 && (fwft_enabled == 0)) &&
                          (C_MEMORY_TYPE==0 || C_MEMORY_TYPE==1))?
                         ideal_dout_d1: ideal_dout; 
  assign DOUT = ideal_dout_out;

  // Assign SBITERR and DBITERR based on latency 
  assign SBITERR = (C_ERROR_INJECTION_TYPE == 1 || C_ERROR_INJECTION_TYPE == 3) && 
                   ((C_USE_EMBEDDED_REG>0 && (fwft_enabled == 0)) &&
                    (C_MEMORY_TYPE==0 || C_MEMORY_TYPE==1)) ?
                   err_type_d1[0]: err_type[0]; 
  assign DBITERR = (C_ERROR_INJECTION_TYPE == 2 || C_ERROR_INJECTION_TYPE == 3) &&
                   ((C_USE_EMBEDDED_REG>0 && (fwft_enabled == 0)) &&
                    (C_MEMORY_TYPE==0 || C_MEMORY_TYPE==1)) ?
                   err_type_d1[1]: err_type[1]; 

  assign EMPTY         = empty_i;
  assign FULL          = full_i;
  //saftey_ckt with one register

  generate
         if ((C_MEMORY_TYPE==0 || C_MEMORY_TYPE==1) && C_EN_SAFETY_CKT==1 && (C_USE_EMBEDDED_REG == 1 || C_USE_EMBEDDED_REG == 2 )) begin
         
         reg [C_DOUT_WIDTH-1:0]     dout_rst_val_d1;
         reg [C_DOUT_WIDTH-1:0]     dout_rst_val_d2;
         reg [1:0] rst_delayed_sft1              =1;
         reg [1:0] rst_delayed_sft2              =1;
         reg [1:0] rst_delayed_sft3              =1;
         reg [1:0] rst_delayed_sft4              =1;
         
        always@(posedge CLK)
          begin
          rst_delayed_sft1 <= #`TCQ rst_i;
          rst_delayed_sft2 <= #`TCQ rst_delayed_sft1;
          rst_delayed_sft3 <= #`TCQ rst_delayed_sft2; 
          rst_delayed_sft4 <= #`TCQ rst_delayed_sft3;
          end
        always@(posedge rst_delayed_sft2 or posedge rst_i or posedge CLK)
          begin
          if( rst_delayed_sft2 == 1'b1 || rst_i == 1'b1) begin 
              ram_rd_en_d1 <= #`TCQ 1'b0;
              valid_d1 <= #`TCQ 1'b0;
          end
          else begin
               ram_rd_en_d1 <= #`TCQ (RD_EN && ~(empty_i));
               valid_d1 <= #`TCQ valid_i;
          end
          end
          
           always@(posedge rst_delayed_sft2 or posedge CLK) 
           begin
           if (rst_delayed_sft2 == 1'b1) begin
              if (C_USE_DOUT_RST == 1'b1) begin
                   @(posedge CLK)
                   ideal_dout_d1 <= #`TCQ dout_reset_val;
              end
              end
           else if (srst_rrst_busy == 1'b1) begin
                   if (C_USE_DOUT_RST == 1'b1) begin
                   ideal_dout_d1 <= #`TCQ dout_reset_val;
                   end
           end else if (ram_rd_en_d1) begin
                   ideal_dout_d1   <= #`TCQ ideal_dout;
                   err_type_d1[0] <= #`TCQ err_type[0];
                   err_type_d1[1] <= #`TCQ err_type[1];
                end
           end   
      end //if 
      endgenerate   

//safety ckt with both registers

generate
         if ((C_MEMORY_TYPE==0 || C_MEMORY_TYPE==1) && C_EN_SAFETY_CKT==1 && C_USE_EMBEDDED_REG == 3) begin
         
         reg [C_DOUT_WIDTH-1:0]     dout_rst_val_d1;
         reg [C_DOUT_WIDTH-1:0]     dout_rst_val_d2;
         reg [1:0] rst_delayed_sft1              =1;
         reg [1:0] rst_delayed_sft2              =1;
         reg [1:0] rst_delayed_sft3              =1;
         reg [1:0] rst_delayed_sft4              =1;
         
        always@(posedge CLK) begin
          rst_delayed_sft1 <= #`TCQ rst_i;
          rst_delayed_sft2 <= #`TCQ rst_delayed_sft1;
          rst_delayed_sft3 <= #`TCQ rst_delayed_sft2; 
          rst_delayed_sft4 <= #`TCQ rst_delayed_sft3;
        end
        always@(posedge rst_delayed_sft2 or posedge rst_i or posedge CLK) begin
          if (rst_delayed_sft2 == 1'b1 || rst_i == 1'b1) begin 
            ram_rd_en_d1 <= #`TCQ 1'b0;
            valid_d1 <= #`TCQ 1'b0;
          end else begin
            ram_rd_en_d1 <= #`TCQ (RD_EN && ~(empty_i));
            fab_rd_en_d1 <= #`TCQ ram_rd_en_d1;
            valid_both <= #`TCQ valid_i;
            valid_d1 <= #`TCQ valid_both;
          end
        end

        always@(posedge rst_delayed_sft2 or posedge CLK) begin
          if (rst_delayed_sft2 == 1'b1) begin
             if (C_USE_DOUT_RST == 1'b1) begin
                   @(posedge CLK)
                  ideal_dout_d1 <= #`TCQ dout_reset_val;
             end
          end else if (srst_rrst_busy == 1'b1) begin
             if (C_USE_DOUT_RST == 1'b1) begin
               ideal_dout_d1 <= #`TCQ dout_reset_val;
             end
          end else begin 
            if (ram_rd_en_d1) begin
               ideal_dout_both   <= #`TCQ ideal_dout;
               err_type_both[0] <= #`TCQ err_type[0];
               err_type_both[1] <= #`TCQ err_type[1];
             end
             if (fab_rd_en_d1) begin
               ideal_dout_d1   <= #`TCQ ideal_dout_both;
               err_type_d1[0] <= #`TCQ err_type_both[0];
               err_type_d1[1] <= #`TCQ err_type_both[1];
            end
          end
        end
      end //if 
      endgenerate    
 
 
  //Overflow may be active-low
  generate if (C_HAS_OVERFLOW==1) begin : gof
    assign OVERFLOW = ideal_overflow ? !C_OVERFLOW_LOW : C_OVERFLOW_LOW;
  end else begin : gnof
    assign OVERFLOW = 0;
  end endgenerate // gof

  assign PROG_EMPTY    = prog_empty_i;
  assign PROG_FULL     = prog_full_i;

   //Valid may change behavior based on latency or active-low
  generate if (C_HAS_VALID==1) begin : gvalid
    assign valid_i       = (C_PRELOAD_LATENCY == 0) ? (RD_EN & ~EMPTY) : ideal_valid;
    assign valid_out     = (C_PRELOAD_LATENCY == 2 && C_MEMORY_TYPE < 2) ?
                            valid_d1 : valid_i; 
    assign VALID         = valid_out ? !C_VALID_LOW : C_VALID_LOW;
  end else begin : gnvalid
    assign VALID         = 0;
  end endgenerate // gvalid

  //Trim data count differently depending on set widths
  generate if (C_HAS_DATA_COUNT == 1) begin : gdc
    always @* begin
      diff_count <= wr_pntr - rd_pntr;
      if (C_DATA_COUNT_WIDTH > C_RD_PNTR_WIDTH) begin
        DATA_COUNT[C_RD_PNTR_WIDTH-1:0]  <= diff_count;
        DATA_COUNT[C_DATA_COUNT_WIDTH-1] <= 1'b0 ; 
      end else begin
        DATA_COUNT <= diff_count[C_RD_PNTR_WIDTH-1:C_RD_PNTR_WIDTH-C_DATA_COUNT_WIDTH];
      end
    end
//  end else begin : gndc
//    always @* DATA_COUNT <= 0;
  end endgenerate // gdc

  //Underflow may change behavior based on latency or active-low
  generate if (C_HAS_UNDERFLOW==1) begin : guf
    assign underflow_i   = ideal_underflow;
    assign UNDERFLOW     = underflow_i ? !C_UNDERFLOW_LOW : C_UNDERFLOW_LOW;
  end else begin : gnuf
    assign UNDERFLOW     = 0;
  end endgenerate // guf
 

  //Write acknowledge may be active low 
  generate if (C_HAS_WR_ACK==1) begin : gwr_ack
    assign WR_ACK        = ideal_wr_ack ? !C_WR_ACK_LOW : C_WR_ACK_LOW;
  end else begin : gnwr_ack
    assign WR_ACK        = 0;
  end endgenerate // gwr_ack


  /*****************************************************************************
   * Internal reset logic 
   ****************************************************************************/
  assign srst_i        = C_EN_SAFETY_CKT ? SAFETY_CKT_WR_RST : C_HAS_SRST ? (SRST | WR_RST_BUSY) : 0;
  assign rst_i            = C_HAS_RST ? RST : 0;
  assign srst_wrst_busy   = srst_i;
  assign srst_rrst_busy   = srst_i;

   /**************************************************************************
    * Assorted registers for delayed versions of signals
    **************************************************************************/
   //Capture delayed version of valid
   generate if (C_HAS_VALID == 1 && (C_USE_EMBEDDED_REG <3)) begin : blockVL20
     always @(posedge CLK or posedge rst_i) begin
        if (rst_i == 1'b1) begin
           valid_d1 <= 1'b0;
        end else begin
           if (srst_rrst_busy) begin
              valid_d1 <= #`TCQ 1'b0;
           end else begin
              valid_d1 <= #`TCQ valid_i;
           end
        end    
     end // always @ (posedge CLK or posedge rst_i)
     end 
   endgenerate // blockVL20

  generate if (C_HAS_VALID == 1 && (C_USE_EMBEDDED_REG == 3)) begin 
     always @(posedge CLK or posedge rst_i) begin
        if (rst_i == 1'b1) begin
           valid_d1   <= 1'b0;
           valid_both <= 1'b0;
        end else begin
           if (srst_rrst_busy) begin
              valid_d1 <= #`TCQ 1'b0;
              valid_both <= #`TCQ 1'b0;
              
           end else begin
              valid_both <= #`TCQ valid_i;
               valid_d1 <= #`TCQ valid_both;
           end
        end    
     end // always @ (posedge CLK or posedge rst_i)
  end
 endgenerate // blockVL20


   // Determine which stage in FWFT registers are valid
   reg stage1_valid = 0;
   reg stage2_valid = 0;
   generate
     if (C_PRELOAD_LATENCY == 0) begin : grd_fwft_proc
       always @ (posedge CLK or posedge rst_i) begin
         if (rst_i) begin
           stage1_valid     <= #`TCQ 0;
           stage2_valid     <= #`TCQ 0;
         end else begin

           if (!stage1_valid && !stage2_valid) begin
             if (!EMPTY)
               stage1_valid    <= #`TCQ 1'b1;
             else
               stage1_valid    <= #`TCQ 1'b0;
           end else if (stage1_valid && !stage2_valid) begin
             if (EMPTY) begin
               stage1_valid    <= #`TCQ 1'b0;
               stage2_valid    <= #`TCQ 1'b1;
             end else begin
               stage1_valid    <= #`TCQ 1'b1;
               stage2_valid    <= #`TCQ 1'b1;
             end
           end else if (!stage1_valid && stage2_valid) begin
             if (EMPTY && RD_EN) begin
               stage1_valid    <= #`TCQ 1'b0;
               stage2_valid    <= #`TCQ 1'b0;
             end else if (!EMPTY && RD_EN) begin
               stage1_valid    <= #`TCQ 1'b1;
               stage2_valid    <= #`TCQ 1'b0;
             end else if (!EMPTY && !RD_EN) begin
               stage1_valid    <= #`TCQ 1'b1;
               stage2_valid    <= #`TCQ 1'b1;
             end else begin
               stage1_valid    <= #`TCQ 1'b0;
               stage2_valid    <= #`TCQ 1'b1;
             end
           end else if (stage1_valid && stage2_valid) begin
             if (EMPTY && RD_EN) begin
               stage1_valid    <= #`TCQ 1'b0;
               stage2_valid    <= #`TCQ 1'b1;
             end else begin
               stage1_valid    <= #`TCQ 1'b1;
               stage2_valid    <= #`TCQ 1'b1;
             end
           end else begin
             stage1_valid    <= #`TCQ 1'b0;
             stage2_valid    <= #`TCQ 1'b0;
           end
         end // rd_rst_i
       end // always
     end
   endgenerate



   //***************************************************************************
   // Assign the read data count value only if it is selected, 
   // otherwise output zeros.
   //***************************************************************************
   generate
      if (C_HAS_RD_DATA_COUNT == 1 && C_USE_FWFT_DATA_COUNT ==1) begin : grdc
       assign RD_DATA_COUNT[C_RD_DATA_COUNT_WIDTH-1:0] = rd_data_count_i_ss[C_RD_PNTR_WIDTH:C_RD_PNTR_WIDTH+1-C_RD_DATA_COUNT_WIDTH];
      end
   endgenerate

   generate
      if (C_HAS_RD_DATA_COUNT == 0) begin : gnrdc
   assign RD_DATA_COUNT[C_RD_DATA_COUNT_WIDTH-1:0] = {C_RD_DATA_COUNT_WIDTH{1'b0}};
      end
   endgenerate

   //***************************************************************************
   // Assign the write data count value only if it is selected, 
   // otherwise output zeros
   //***************************************************************************
   generate
      if (C_HAS_WR_DATA_COUNT == 1 && C_USE_FWFT_DATA_COUNT == 1) begin : gwdc
       assign WR_DATA_COUNT[C_WR_DATA_COUNT_WIDTH-1:0] = wr_data_count_i_ss[C_WR_PNTR_WIDTH:C_WR_PNTR_WIDTH+1-C_WR_DATA_COUNT_WIDTH] ;
      end
   endgenerate
   
   generate
      if (C_HAS_WR_DATA_COUNT == 0) begin : gnwdc
   assign WR_DATA_COUNT[C_WR_DATA_COUNT_WIDTH-1:0] = {C_WR_DATA_COUNT_WIDTH{1'b0}};
      end
   endgenerate
   
   //reg ram_rd_en_d1 = 1'b0;
   //Capture delayed version of dout
   generate if (C_EN_SAFETY_CKT == 0 && (C_USE_EMBEDDED_REG<3)) begin
   always @(posedge CLK or posedge rst_i) begin
      if (rst_i == 1'b1) begin
         // Reset err_type only if ECC is not selected
         if (C_USE_ECC == 0) begin
            err_type_d1      <= #`TCQ 0;
            err_type_both    <= #`TCQ 0;
         end
         // DRAM and SRAM reset asynchronously
         if ((C_MEMORY_TYPE == 2 || C_MEMORY_TYPE == 3) && C_USE_DOUT_RST == 1) begin
            ideal_dout_d1 <= #`TCQ dout_reset_val;
         end
         ram_rd_en_d1 <= #`TCQ 1'b0;
        if (C_USE_DOUT_RST == 1) begin
            @(posedge CLK)
            ideal_dout_d1 <= #`TCQ dout_reset_val;
        end
      end else begin
         ram_rd_en_d1 <= #`TCQ RD_EN & ~EMPTY;
         if (srst_rrst_busy) begin
            ram_rd_en_d1 <= #`TCQ 1'b0;
            // Reset err_type only if ECC is not selected
            if (C_USE_ECC == 0) begin
               err_type_d1   <= #`TCQ 0;
               err_type_both <= #`TCQ 0;
            end
            // Reset DRAM and SRAM based FIFO, BRAM based FIFO is reset above
            if ((C_MEMORY_TYPE == 2 || C_MEMORY_TYPE == 3) && C_USE_DOUT_RST == 1) begin
               ideal_dout_d1 <= #`TCQ dout_reset_val;
            end 
         if (C_USE_DOUT_RST == 1) begin
           // @(posedge CLK)
            ideal_dout_d1 <= #`TCQ dout_reset_val;
         end
         end else begin
            if (ram_rd_en_d1 ) begin
            ideal_dout_d1 <= #`TCQ ideal_dout;
            err_type_d1   <= #`TCQ err_type;
            end
         end
      end    
   end   // always
end
endgenerate 

//no safety ckt with both registers
 generate if (C_EN_SAFETY_CKT == 0 && (C_USE_EMBEDDED_REG==3)) begin
   always @(posedge CLK or posedge rst_i) begin
      if (rst_i == 1'b1) begin
          ram_rd_en_d1 <= #`TCQ 1'b0;
          fab_rd_en_d1 <= #`TCQ 1'b0;
         // Reset err_type only if ECC is not selected
         if (C_USE_ECC == 0) begin
            err_type_d1      <= #`TCQ 0;
            err_type_both    <= #`TCQ 0;
         end
         // DRAM and SRAM reset asynchronously
         if ((C_MEMORY_TYPE == 2 || C_MEMORY_TYPE == 3) && C_USE_DOUT_RST == 1) begin
            ideal_dout_d1 <= #`TCQ dout_reset_val;
            ideal_dout_both <= #`TCQ dout_reset_val; 
            
      end
        if (C_USE_DOUT_RST == 1) begin
            @(posedge CLK)
            ideal_dout_d1 <= #`TCQ dout_reset_val;
            ideal_dout_both <= #`TCQ dout_reset_val;
       end
      end else begin
         if (srst_rrst_busy) begin 
           ram_rd_en_d1 <= #`TCQ 1'b0;
           fab_rd_en_d1 <= #`TCQ 1'b0;
           // Reset err_type only if ECC is not selected
           if (C_USE_ECC == 0) begin
              err_type_d1   <= #`TCQ 0;
              err_type_both <= #`TCQ 0;
           end
           // Reset DRAM and SRAM based FIFO, BRAM based FIFO is reset above
           if ((C_MEMORY_TYPE == 2 || C_MEMORY_TYPE == 3) && C_USE_DOUT_RST == 1) begin
              ideal_dout_d1 <= #`TCQ dout_reset_val;
           end 
           if (C_USE_DOUT_RST == 1) begin
             ideal_dout_d1 <= #`TCQ dout_reset_val;
           end
         end else begin
           ram_rd_en_d1 <= #`TCQ RD_EN & ~EMPTY;
           fab_rd_en_d1 <= #`TCQ (ram_rd_en_d1);
           if (ram_rd_en_d1 ) begin
             ideal_dout_both <= #`TCQ ideal_dout;
             err_type_both   <= #`TCQ err_type;
           end
           if (fab_rd_en_d1 ) begin
             ideal_dout_d1 <= #`TCQ ideal_dout_both;
             err_type_d1   <= #`TCQ err_type_both;
           end
         end
      end    
   end   // always
end
endgenerate 
   /**************************************************************************
    * Overflow and Underflow Flag calculation
    *  (handled separately because they don't support rst)
    **************************************************************************/
   generate if (C_HAS_OVERFLOW == 1 && IS_8SERIES == 0) begin : g7s_ovflw
     always @(posedge CLK) begin
       ideal_overflow    <= #`TCQ WR_EN & full_i;
     end
   end else if (C_HAS_OVERFLOW == 1 && IS_8SERIES == 1) begin : g8s_ovflw
     always @(posedge CLK) begin
       //ideal_overflow    <= #`TCQ WR_EN & (rst_i | full_i);
       ideal_overflow    <= #`TCQ WR_EN & (WR_RST_BUSY | full_i);
     end
   end endgenerate // blockOF20
 
   generate if (C_HAS_UNDERFLOW == 1 && IS_8SERIES == 0) begin : g7s_unflw
     always @(posedge CLK) begin
       ideal_underflow   <= #`TCQ empty_i & RD_EN;
     end
   end else if (C_HAS_UNDERFLOW == 1 && IS_8SERIES == 1) begin : g8s_unflw
     always @(posedge CLK) begin
       //ideal_underflow   <= #`TCQ (rst_i | empty_i) & RD_EN;
       ideal_underflow   <= #`TCQ (RD_RST_BUSY | empty_i) & RD_EN;
     end
   end endgenerate // blockUF20


   /**************************
    * Read Data Count
    *************************/

   reg [31:0] num_read_words_dc;
   reg [C_RD_DATA_COUNT_WIDTH-1:0] num_read_words_sized_i;
   
   always @(num_rd_bits) begin
     if (C_USE_FWFT_DATA_COUNT) begin
        
        //If using extra logic for FWFT Data Counts, 
        // then scale FIFO contents to read domain, 
        // and add two read words for FWFT stages
        //This value is only a temporary value and not used in the code.
        num_read_words_dc = (num_rd_bits/C_DOUT_WIDTH+2);
        
        //Trim the read words for use with RD_DATA_COUNT
        num_read_words_sized_i = 
          num_read_words_dc[C_RD_PNTR_WIDTH : C_RD_PNTR_WIDTH-C_RD_DATA_COUNT_WIDTH+1];
        
     end else begin
        
        //If not using extra logic for FWFT Data Counts, 
        // then scale FIFO contents to read domain.
        //This value is only a temporary value and not used in the code.
        num_read_words_dc = num_rd_bits/C_DOUT_WIDTH;
        
        //Trim the read words for use with RD_DATA_COUNT
        num_read_words_sized_i = 
          num_read_words_dc[C_RD_PNTR_WIDTH-1 : C_RD_PNTR_WIDTH-C_RD_DATA_COUNT_WIDTH];
        
     end //if (C_USE_FWFT_DATA_COUNT)
   end //always

   
   /**************************
    * Write Data Count
    *************************/

   reg [31:0] num_write_words_dc;
   reg [C_WR_DATA_COUNT_WIDTH-1:0] num_write_words_sized_i;
   
   always @(num_wr_bits) begin
     if (C_USE_FWFT_DATA_COUNT) begin
        
        //Calculate the Data Count value for the number of write words, 
        // when using First-Word Fall-Through with extra logic for Data 
        // Counts. This takes into consideration the number of words that 
        // are expected to be stored in the FWFT register stages (it always 
        // assumes they are filled).
        //This value is scaled to the Write Domain.
        //The expression (((A-1)/B))+1 divides A/B, but takes the 
        // ceiling of the result.
        //When num_wr_bits==0, set the result manually to prevent 
        // division errors.
        //EXTRA_WORDS_DC is the number of words added to write_words 
        // due to FWFT.
        //This value is only a temporary value and not used in the code.
        num_write_words_dc = (num_wr_bits==0) ? EXTRA_WORDS_DC :  (((num_wr_bits-1)/C_DIN_WIDTH)+1) + EXTRA_WORDS_DC ;
        
        //Trim the write words for use with WR_DATA_COUNT
        num_write_words_sized_i = 
          num_write_words_dc[C_WR_PNTR_WIDTH : C_WR_PNTR_WIDTH-C_WR_DATA_COUNT_WIDTH+1];
        
     end else begin
        
        //Calculate the Data Count value for the number of write words, when NOT
        // using First-Word Fall-Through with extra logic for Data Counts. This 
        // calculates only the number of words in the internal FIFO.
        //The expression (((A-1)/B))+1 divides A/B, but takes the 
        // ceiling of the result.
        //This value is scaled to the Write Domain.
        //When num_wr_bits==0, set the result manually to prevent 
        // division errors.
        //This value is only a temporary value and not used in the code.
        num_write_words_dc = (num_wr_bits==0) ? 0 : ((num_wr_bits-1)/C_DIN_WIDTH)+1;
        
        //Trim the read words for use with RD_DATA_COUNT
        num_write_words_sized_i = 
          num_write_words_dc[C_WR_PNTR_WIDTH-1 : C_WR_PNTR_WIDTH-C_WR_DATA_COUNT_WIDTH];
        
     end //if (C_USE_FWFT_DATA_COUNT)
   end //always


  /*************************************************************************
   * Write and Read Logic  
   ************************************************************************/
   wire              write_allow;
   wire              read_allow;
   wire              read_allow_dc;
   wire              write_only;
   wire              read_only;
   //wire              write_only_q;
   reg              write_only_q;
   //wire              read_only_q;
   reg              read_only_q;
   reg              full_reg;
   reg              rst_full_ff_reg1;
   reg              rst_full_ff_reg2;
   wire              ram_full_comb;
   wire              carry;
   
   assign write_allow  = WR_EN & ~full_i;
   assign read_allow   = RD_EN & ~empty_i;
   assign read_allow_dc = RD_EN_USER & ~USER_EMPTY_FB;
   //assign write_only   = write_allow & ~read_allow;
   //assign write_only_q = write_allow_q;
   //assign read_only    = read_allow    & ~write_allow;
   //assign read_only_q  = read_allow_q ;
   wire [C_WR_PNTR_WIDTH-1:0] diff_pntr;
   wire [C_RD_PNTR_WIDTH-1:0] diff_pntr_pe;
   reg [C_WR_PNTR_WIDTH-1:0] diff_pntr_reg1 = 0;
   reg [C_RD_PNTR_WIDTH-1:0] diff_pntr_pe_reg1 = 0;
   reg [C_RD_PNTR_WIDTH:0] diff_pntr_pe_asym = 0;
   wire [C_RD_PNTR_WIDTH:0] adj_wr_pntr_rd_asym ;
   wire [C_RD_PNTR_WIDTH:0] rd_pntr_asym;
   reg [C_WR_PNTR_WIDTH-1:0] diff_pntr_reg2 = 0;
   reg [C_WR_PNTR_WIDTH-1:0] diff_pntr_pe_reg2 = 0;
   wire [C_RD_PNTR_WIDTH-1:0] diff_pntr_pe_max;
   wire [C_RD_PNTR_WIDTH-1:0] diff_pntr_max;

   assign diff_pntr_pe_max = DIFF_MAX_RD;
   assign diff_pntr_max = DIFF_MAX_WR;



   generate if (IS_ASYMMETRY == 0) begin : diff_pntr_sym
    assign write_only   = write_allow & ~read_allow;
    assign read_only    = read_allow    & ~write_allow;
    end endgenerate
    generate if ( IS_ASYMMETRY == 1 && C_WR_PNTR_WIDTH < C_RD_PNTR_WIDTH) begin : wr_grt_rd
     assign read_only   = read_allow & &(rd_pntr[C_RD_PNTR_WIDTH-C_WR_PNTR_WIDTH-1 : 0]) & ~write_allow;
     assign write_only    = write_allow    & ~(read_allow & &(rd_pntr[C_RD_PNTR_WIDTH-C_WR_PNTR_WIDTH-1 : 0]));
    end endgenerate
    generate if (IS_ASYMMETRY ==1 && C_WR_PNTR_WIDTH > C_RD_PNTR_WIDTH) begin : rd_grt_wr
     assign read_only   = read_allow & ~(write_allow  & &(wr_pntr[C_WR_PNTR_WIDTH-C_RD_PNTR_WIDTH-1 : 0]));
     assign write_only    = write_allow &  &(wr_pntr[C_WR_PNTR_WIDTH-C_RD_PNTR_WIDTH-1 : 0]) & ~read_allow;
    end endgenerate


   //-----------------------------------------------------------------------------
   // Write and Read pointer generation
   //-----------------------------------------------------------------------------
   always @(posedge CLK or posedge rst_i) begin
     if (rst_i && C_EN_SAFETY_CKT == 0) begin
       wr_pntr         <= 0;
       rd_pntr         <= 0;
     end else begin
       if (srst_i) begin
         wr_pntr       <= #`TCQ 0;
         rd_pntr       <= #`TCQ 0;
       end else begin
         if (write_allow) wr_pntr <= #`TCQ wr_pntr + 1;
         if (read_allow)  rd_pntr <= #`TCQ rd_pntr + 1;
       end
     end
   end

   generate if (C_FIFO_TYPE == 2) begin : gll_dm_dout
   always @(posedge CLK) begin
     if (write_allow) begin
       if (ENABLE_ERR_INJECTION == 1)
         memory[wr_pntr] <= #`TCQ {INJECTDBITERR,INJECTSBITERR,DIN};
       else
         memory[wr_pntr] <= #`TCQ DIN;
     end
   end

   reg  [C_DATA_WIDTH-1:0] dout_tmp_q;
   reg [C_DATA_WIDTH-1:0] dout_tmp = 0;
   reg  [C_DATA_WIDTH-1:0] dout_tmp1 = 0;
   always @(posedge CLK) begin
     dout_tmp_q <= #`TCQ ideal_dout;
   end



     always @* begin
       if (read_allow)
         ideal_dout <= memory[rd_pntr];
       else
         ideal_dout <= dout_tmp_q;
     end
   end endgenerate // gll_dm_dout


   /**************************************************************************
   * Write Domain Logic
   **************************************************************************/
   assign ram_rd_en        = RD_EN & !EMPTY;

   //reg [C_WR_PNTR_WIDTH-1:0] diff_pntr = 0;
   generate if (C_FIFO_TYPE != 2) begin : gnll_din
   always @(posedge CLK or posedge rst_i) begin : gen_fifo_w

     /****** Reset fifo (case 1)***************************************/
     if (rst_i == 1'b1) begin
       num_wr_bits       <= #`TCQ 0;
       next_num_wr_bits   = #`TCQ 0;
       wr_ptr            <= #`TCQ C_WR_DEPTH - 1;
       rd_ptr_wrclk      <= #`TCQ C_RD_DEPTH - 1;
       ideal_wr_ack      <= #`TCQ 0;
       ideal_wr_count    <= #`TCQ 0;
       tmp_wr_listsize    = #`TCQ 0;
       rd_ptr_wrclk_next <= #`TCQ 0;
       wr_pntr           <= #`TCQ 0;
       wr_pntr_rd1       <= #`TCQ 0;

     end else begin //rst_i==0
     if (srst_wrst_busy) begin
       num_wr_bits       <= #`TCQ 0;
       next_num_wr_bits   = #`TCQ 0;
       wr_ptr            <= #`TCQ C_WR_DEPTH - 1;
       rd_ptr_wrclk      <= #`TCQ C_RD_DEPTH - 1;
       ideal_wr_ack      <= #`TCQ 0;
       ideal_wr_count    <= #`TCQ 0;
       tmp_wr_listsize    = #`TCQ 0;
       rd_ptr_wrclk_next <= #`TCQ 0;
       wr_pntr           <= #`TCQ 0;
       wr_pntr_rd1       <= #`TCQ 0;
     end else begin//srst_i=0

       wr_pntr_rd1   <= #`TCQ wr_pntr;

       //Determine the current number of words in the FIFO
       tmp_wr_listsize = (C_DEPTH_RATIO_RD > 1) ? num_wr_bits/C_DOUT_WIDTH :
                         num_wr_bits/C_DIN_WIDTH;
       rd_ptr_wrclk_next = rd_ptr;
       if (rd_ptr_wrclk < rd_ptr_wrclk_next) begin
         next_num_wr_bits = num_wr_bits -
                            C_DOUT_WIDTH*(rd_ptr_wrclk + C_RD_DEPTH
                                          - rd_ptr_wrclk_next);
       end else begin
         next_num_wr_bits = num_wr_bits -
                            C_DOUT_WIDTH*(rd_ptr_wrclk - rd_ptr_wrclk_next);
       end

       if (WR_EN == 1'b1) begin
         if (FULL == 1'b1) begin

             ideal_wr_ack      <= #`TCQ 0;
             //Reminder that FIFO is still full
             ideal_wr_count    <= #`TCQ num_write_words_sized_i;

         end else begin
             write_fifo;
             next_num_wr_bits  = next_num_wr_bits + C_DIN_WIDTH;
             //Write successful, so issue acknowledge
             // and no error  
             ideal_wr_ack      <= #`TCQ 1;
             //Not even close to full.
             ideal_wr_count    <= num_write_words_sized_i;

           //end

         end

       end else begin //(WR_EN == 1'b1)

         //If user did not attempt a write, then do not
         // give ack or err
         ideal_wr_ack   <= #`TCQ 0;
         ideal_wr_count <= #`TCQ num_write_words_sized_i;
       end
       num_wr_bits       <= #`TCQ next_num_wr_bits;
       rd_ptr_wrclk      <= #`TCQ rd_ptr;

     end //srst_i==0
     end //wr_rst_i==0
   end // gen_fifo_w
    end endgenerate

   generate if (C_FIFO_TYPE < 2 && C_MEMORY_TYPE < 2) begin : gnll_dm_dout
     always @(posedge CLK) begin
       if (rst_i || srst_rrst_busy) begin
         if (C_USE_DOUT_RST == 1) begin
           ideal_dout <= #`TCQ dout_reset_val;
           ideal_dout_both <= #`TCQ dout_reset_val;
         end
       end
     end
    end endgenerate




   generate if (C_FIFO_TYPE != 2) begin : gnll_dout
   always @(posedge CLK or posedge rst_i) begin : gen_fifo_r

     /****** Reset fifo (case 1)***************************************/
     if (rst_i) begin
       num_rd_bits        <= #`TCQ 0;
       next_num_rd_bits    = #`TCQ 0;
       rd_ptr             <= #`TCQ C_RD_DEPTH -1;
       rd_pntr            <= #`TCQ 0;
       //rd_pntr_wr1       <= #`TCQ 0;
       wr_ptr_rdclk       <= #`TCQ C_WR_DEPTH -1;
  
       // DRAM resets asynchronously
       if (C_FIFO_TYPE < 2 && (C_MEMORY_TYPE == 2 || C_MEMORY_TYPE == 3 )&& C_USE_DOUT_RST == 1)
          ideal_dout    <= #`TCQ dout_reset_val;
  
       // Reset err_type only if ECC is not selected
       if (C_USE_ECC == 0) begin
         err_type         <= #`TCQ 0;
         err_type_d1      <= 0;
         err_type_both    <= 0;
       end
       ideal_valid        <= #`TCQ 1'b0;
       ideal_rd_count     <= #`TCQ 0;

     end else begin //rd_rst_i==0
     if (srst_rrst_busy) begin
       num_rd_bits        <= #`TCQ 0;
       next_num_rd_bits    = #`TCQ 0;
       rd_ptr             <= #`TCQ C_RD_DEPTH -1;
       rd_pntr            <= #`TCQ 0;
       //rd_pntr_wr1       <= #`TCQ 0;
       wr_ptr_rdclk       <= #`TCQ C_WR_DEPTH -1;
  
       // DRAM resets synchronously
       if (C_FIFO_TYPE < 2 && (C_MEMORY_TYPE == 2 || C_MEMORY_TYPE == 3 )&& C_USE_DOUT_RST == 1)
          ideal_dout    <= #`TCQ dout_reset_val;
  
       // Reset err_type only if ECC is not selected
       if (C_USE_ECC == 0) begin
         err_type         <= #`TCQ 0;
         err_type_d1      <= #`TCQ 0;
         err_type_both    <= #`TCQ 0;
       end
       ideal_valid        <= #`TCQ 1'b0;
       ideal_rd_count     <= #`TCQ 0;
      end //srst_i
      else begin

       //rd_pntr_wr1   <= #`TCQ rd_pntr;

       //Determine the current number of words in the FIFO
       tmp_rd_listsize = (C_DEPTH_RATIO_WR > 1) ? num_rd_bits/C_DIN_WIDTH :
                         num_rd_bits/C_DOUT_WIDTH;
       wr_ptr_rdclk_next = wr_ptr;

       if (wr_ptr_rdclk < wr_ptr_rdclk_next) begin
         next_num_rd_bits = num_rd_bits +
                            C_DIN_WIDTH*(wr_ptr_rdclk +C_WR_DEPTH
                                         - wr_ptr_rdclk_next);
       end else begin
         next_num_rd_bits = num_rd_bits +
                             C_DIN_WIDTH*(wr_ptr_rdclk - wr_ptr_rdclk_next);
       end

         if (RD_EN == 1'b1) begin

           if (EMPTY == 1'b1) begin
                 ideal_valid        <= #`TCQ 1'b0;
                 ideal_rd_count     <= #`TCQ num_read_words_sized_i;
               end 
           else 
             begin
                   read_fifo;
                   next_num_rd_bits = next_num_rd_bits - C_DOUT_WIDTH;

                   //Acknowledge the read from the FIFO, no error
                   ideal_valid        <= #`TCQ 1'b1;
                   ideal_rd_count     <= #`TCQ num_read_words_sized_i;

                 end // if (tmp_rd_listsize == 2)
         end

       num_rd_bits      <= #`TCQ next_num_rd_bits;
       wr_ptr_rdclk     <= #`TCQ wr_ptr;
     end //s_rst_i==0
     end //rd_rst_i==0
   end //always
  end endgenerate

   //-----------------------------------------------------------------------------
   // Generate diff_pntr for PROG_FULL generation
   // Generate diff_pntr_pe for PROG_EMPTY generation
   //-----------------------------------------------------------------------------
   generate if ((C_PROG_FULL_TYPE != 0 || C_PROG_EMPTY_TYPE != 0) && IS_ASYMMETRY == 0) begin : reg_write_allow
     always @(posedge CLK ) begin
       if (rst_i) begin
         write_only_q   <= 1'b0;
         read_only_q    <= 1'b0;
         diff_pntr_reg1       <= 0;
         diff_pntr_pe_reg1    <= 0;
         diff_pntr_reg2       <= 0;
         diff_pntr_pe_reg2    <= 0;
       end else begin
         if (srst_i || srst_wrst_busy || srst_rrst_busy) begin
          if (srst_rrst_busy) begin
           read_only_q  <= #`TCQ 1'b0;
           diff_pntr_pe_reg1  <= #`TCQ 0;
           diff_pntr_pe_reg2  <= #`TCQ 0;
          end
          if (srst_wrst_busy) begin
           write_only_q <= #`TCQ 1'b0;
           diff_pntr_reg1     <= #`TCQ 0;
           diff_pntr_reg2     <= #`TCQ 0;
          end
         end else begin
           write_only_q <= #`TCQ write_only;
           read_only_q  <= #`TCQ read_only;
           diff_pntr_reg2  <= #`TCQ diff_pntr_reg1;
           diff_pntr_pe_reg2  <= #`TCQ diff_pntr_pe_reg1;

           // Add 1 to the difference pointer value when only write happens.
           if (write_only)  
             diff_pntr_reg1 <= #`TCQ wr_pntr - adj_rd_pntr_wr + 1;
           else
             diff_pntr_reg1 <= #`TCQ wr_pntr - adj_rd_pntr_wr;

           // Add 1 to the difference pointer value when write or both write & read or no write & read happen.
           if (read_only)  
             diff_pntr_pe_reg1 <= #`TCQ adj_wr_pntr_rd - rd_pntr - 1;
           else
             diff_pntr_pe_reg1 <= #`TCQ adj_wr_pntr_rd - rd_pntr;
         end
       end
     end
   assign diff_pntr_pe = diff_pntr_pe_reg1;
   assign diff_pntr = diff_pntr_reg1;
   end endgenerate // reg_write_allow

   generate if ((C_PROG_FULL_TYPE != 0 || C_PROG_EMPTY_TYPE != 0) && IS_ASYMMETRY == 1) begin : reg_write_allow_asym
    assign adj_wr_pntr_rd_asym[C_RD_PNTR_WIDTH:0] = {adj_wr_pntr_rd,1'b1};
    assign rd_pntr_asym[C_RD_PNTR_WIDTH:0] = {~rd_pntr,1'b1};
     always @(posedge CLK ) begin
       if (rst_i) begin
         diff_pntr_pe_asym    <= 0;
         diff_pntr_reg1       <= 0;
         full_reg             <= 0;
         rst_full_ff_reg1     <= 1;
         rst_full_ff_reg2     <= 1;
         diff_pntr_pe_reg1    <= 0;
       end else begin
         if (srst_i || srst_wrst_busy || srst_rrst_busy) begin
          if (srst_wrst_busy)
           diff_pntr_reg1     <= #`TCQ 0;
          if (srst_rrst_busy)
           full_reg             <=  #`TCQ 0;
           rst_full_ff_reg1     <=  #`TCQ 1;
           rst_full_ff_reg2     <=  #`TCQ 1;
           diff_pntr_pe_asym    <=  #`TCQ 0;
           diff_pntr_pe_reg1  <= #`TCQ 0;
         end else begin
             diff_pntr_pe_asym <= #`TCQ adj_wr_pntr_rd_asym + rd_pntr_asym;
             full_reg          <= #`TCQ full_i;
             rst_full_ff_reg1  <=  #`TCQ RST_FULL_FF;
             rst_full_ff_reg2  <=  #`TCQ rst_full_ff_reg1;
           if (~full_i) begin  
             diff_pntr_reg1 <=  #`TCQ wr_pntr - adj_rd_pntr_wr;
          end
         end
       end
     end
   assign carry = (~(|(diff_pntr_pe_asym [C_RD_PNTR_WIDTH : 1])));
   assign diff_pntr_pe = (full_reg && ~rst_full_ff_reg2 && carry ) ? diff_pntr_pe_max : diff_pntr_pe_asym[C_RD_PNTR_WIDTH:1];
   assign diff_pntr = diff_pntr_reg1;
   end endgenerate // reg_write_allow_asym


   //-----------------------------------------------------------------------------
   // Generate FULL flag
   //-----------------------------------------------------------------------------
   wire                 comp0;
   wire                 comp1;
   wire                 going_full;
   wire                 leaving_full;
 
 generate if (C_WR_PNTR_WIDTH > C_RD_PNTR_WIDTH) begin :  gpad 	
    assign adj_rd_pntr_wr [C_WR_PNTR_WIDTH-1 : C_WR_PNTR_WIDTH-C_RD_PNTR_WIDTH] = rd_pntr;
    assign adj_rd_pntr_wr[C_WR_PNTR_WIDTH-C_RD_PNTR_WIDTH-1 : 0] = 0;
  end endgenerate

  generate if (C_WR_PNTR_WIDTH <= C_RD_PNTR_WIDTH) begin :  gtrim 
    assign adj_rd_pntr_wr = rd_pntr[C_RD_PNTR_WIDTH-1 : C_RD_PNTR_WIDTH-C_WR_PNTR_WIDTH];
  end endgenerate

   assign comp1         = (adj_rd_pntr_wr == (wr_pntr + 1'b1));
   assign comp0         = (adj_rd_pntr_wr == wr_pntr);

    generate if (C_WR_PNTR_WIDTH == C_RD_PNTR_WIDTH) begin : gf_wp_eq_rp
     assign going_full    = (comp1 & write_allow & ~read_allow);
     assign leaving_full  = (comp0 & read_allow) | RST_FULL_GEN;
    end endgenerate

    // Write data width is bigger than read data width
    // Write depth is smaller than read depth
    // One write could be equal to 2 or 4 or 8 reads
    generate if (C_WR_PNTR_WIDTH < C_RD_PNTR_WIDTH) begin : gf_asym
      assign going_full = (comp1 & write_allow & (~ (read_allow & &(rd_pntr[C_RD_PNTR_WIDTH-C_WR_PNTR_WIDTH-1 : 0]))));
      assign leaving_full = (comp0 & read_allow & &(rd_pntr[C_RD_PNTR_WIDTH-C_WR_PNTR_WIDTH-1 : 0])) | RST_FULL_GEN;
    end endgenerate

    generate if (C_WR_PNTR_WIDTH > C_RD_PNTR_WIDTH) begin : gf_wp_gt_rp 
      assign going_full = (comp1 & write_allow & ~read_allow);
      assign leaving_full =(comp0 & read_allow) | RST_FULL_GEN;
    end endgenerate


   assign ram_full_comb = going_full | (~leaving_full & full_i);

   always @(posedge CLK or posedge RST_FULL_FF) begin
     if (RST_FULL_FF)
       full_i   <= C_FULL_FLAGS_RST_VAL;
     else if (srst_wrst_busy)
       full_i   <= #`TCQ C_FULL_FLAGS_RST_VAL;
     else
       full_i   <= #`TCQ ram_full_comb;
    end

   //-----------------------------------------------------------------------------
   // Generate EMPTY flag
   //-----------------------------------------------------------------------------
   wire                 ecomp0;
   wire                 ecomp1;
   wire                 going_empty;
   wire                 leaving_empty;
   wire                 ram_empty_comb;

  
 generate if (C_RD_PNTR_WIDTH > C_WR_PNTR_WIDTH) begin :  pad 	
    assign adj_wr_pntr_rd [C_RD_PNTR_WIDTH-1 : C_RD_PNTR_WIDTH-C_WR_PNTR_WIDTH] = wr_pntr;
    assign adj_wr_pntr_rd[C_RD_PNTR_WIDTH-C_WR_PNTR_WIDTH-1 : 0] = 0;
  end endgenerate

  generate if (C_RD_PNTR_WIDTH <= C_WR_PNTR_WIDTH) begin :  trim 
    assign adj_wr_pntr_rd = wr_pntr[C_WR_PNTR_WIDTH-1 : C_WR_PNTR_WIDTH-C_RD_PNTR_WIDTH];
  end endgenerate

   assign ecomp1         = (adj_wr_pntr_rd == (rd_pntr + 1'b1));
   assign ecomp0         = (adj_wr_pntr_rd == rd_pntr);


    generate if (C_WR_PNTR_WIDTH == C_RD_PNTR_WIDTH) begin : ge_wp_eq_rp
     assign going_empty    = (ecomp1 & ~write_allow & read_allow);
     assign leaving_empty  = (ecomp0 & write_allow);
    end endgenerate

    generate if (C_WR_PNTR_WIDTH > C_RD_PNTR_WIDTH) begin : ge_wp_gt_rp
      assign going_empty = (ecomp1 & read_allow & (~(write_allow & &(wr_pntr[C_WR_PNTR_WIDTH-C_RD_PNTR_WIDTH-1 : 0]))));
      assign leaving_empty = (ecomp0 & write_allow & &(wr_pntr[C_WR_PNTR_WIDTH-C_RD_PNTR_WIDTH-1 : 0]));
    end endgenerate
  
   generate if (C_WR_PNTR_WIDTH < C_RD_PNTR_WIDTH) begin : ge_wp_lt_rp 
      assign going_empty = (ecomp1 & ~write_allow & read_allow);
      assign leaving_empty =(ecomp0 & write_allow);
    end endgenerate



    assign ram_empty_comb = going_empty | (~leaving_empty & empty_i);

   always @(posedge CLK or posedge rst_i) begin
     if (rst_i)
       empty_i  <= 1'b1;
     else if (srst_rrst_busy)
       empty_i  <= #`TCQ 1'b1;
     else
       empty_i  <= #`TCQ ram_empty_comb;
    end
   always @(posedge CLK or posedge rst_i) begin
     if (rst_i && C_EN_SAFETY_CKT == 0) begin
       EMPTY_FB     <= 1'b1;
     end else begin
       if (srst_rrst_busy || (SAFETY_CKT_WR_RST && C_EN_SAFETY_CKT))
         EMPTY_FB   <= #`TCQ 1'b1;
       else
         EMPTY_FB   <= #`TCQ ram_empty_comb;
     end
   end // always

   //-----------------------------------------------------------------------------
   // Generate Read and write data counts for asymmetic common clock
   //-----------------------------------------------------------------------------

    reg [C_GRTR_PNTR_WIDTH :0] count_dc = 0; 
    wire [C_GRTR_PNTR_WIDTH :0] ratio; 
    wire decr_by_one;
    wire incr_by_ratio;
    wire incr_by_one;
    wire decr_by_ratio;

   localparam IS_FWFT          = (C_PRELOAD_REGS == 1 && C_PRELOAD_LATENCY == 0) ? 1 : 0;

   generate if (C_WR_PNTR_WIDTH < C_RD_PNTR_WIDTH) begin : rd_depth_gt_wr 
      assign ratio         = C_DEPTH_RATIO_RD;
      assign decr_by_one   = (IS_FWFT == 1)? read_allow_dc : read_allow;
      assign incr_by_ratio = write_allow;

      always @(posedge CLK or posedge rst_i) begin
       if (rst_i)
         count_dc  <= #`TCQ 0;
       else if (srst_wrst_busy)
         count_dc  <= #`TCQ 0;
       else begin
	 if (decr_by_one) begin
	   if (!incr_by_ratio) 
            count_dc <= #`TCQ count_dc - 1;
           else
	    count_dc <= #`TCQ count_dc - 1  + ratio ;
	 end
	 else begin
	   if (!incr_by_ratio) 
            count_dc <= #`TCQ count_dc ;
           else
	    count_dc <= #`TCQ count_dc + ratio ;
	end
       end
       end

       assign rd_data_count_i_ss[C_RD_PNTR_WIDTH : 0] = count_dc;
       assign wr_data_count_i_ss[C_WR_PNTR_WIDTH : 0] = count_dc[C_RD_PNTR_WIDTH : C_RD_PNTR_WIDTH-C_WR_PNTR_WIDTH];

    end endgenerate


    generate if (C_WR_PNTR_WIDTH > C_RD_PNTR_WIDTH) begin : wr_depth_gt_rd 
      assign ratio         = C_DEPTH_RATIO_WR;
      assign incr_by_one   = write_allow;
      assign decr_by_ratio = (IS_FWFT == 1)? read_allow_dc : read_allow;

      always @(posedge CLK or posedge rst_i) begin
       if (rst_i)
         count_dc  <= #`TCQ 0;
       else if (srst_wrst_busy)
         count_dc  <= #`TCQ 0;
       else begin
	 if (incr_by_one) begin
	   if (!decr_by_ratio) 
            count_dc <= #`TCQ count_dc + 1;
           else
	    count_dc <= #`TCQ count_dc + 1  - ratio ;
	 end
	 else begin
	   if (!decr_by_ratio) 
            count_dc <= #`TCQ count_dc ;
           else
	    count_dc <= #`TCQ count_dc - ratio ;
	end
       end
       end

       assign wr_data_count_i_ss[C_WR_PNTR_WIDTH : 0] = count_dc;
       assign rd_data_count_i_ss[C_RD_PNTR_WIDTH : 0] = count_dc[C_WR_PNTR_WIDTH : C_WR_PNTR_WIDTH-C_RD_PNTR_WIDTH];

    end endgenerate






   //-----------------------------------------------------------------------------
   // Generate WR_ACK flag
   //-----------------------------------------------------------------------------
   always @(posedge CLK or posedge rst_i) begin
     if (rst_i)
       ideal_wr_ack  <= 1'b0;
     else if (srst_wrst_busy)
       ideal_wr_ack  <= #`TCQ 1'b0;
     else if (WR_EN & ~full_i)
       ideal_wr_ack  <= #`TCQ 1'b1;
     else
       ideal_wr_ack  <= #`TCQ 1'b0;
    end

   //-----------------------------------------------------------------------------
   // Generate VALID flag
   //-----------------------------------------------------------------------------
   always @(posedge CLK or posedge rst_i) begin
     if (rst_i)
       ideal_valid  <= 1'b0;
     else if (srst_rrst_busy)
       ideal_valid  <= #`TCQ 1'b0;
     else if (RD_EN & ~empty_i)
       ideal_valid  <= #`TCQ 1'b1;
     else
       ideal_valid  <= #`TCQ 1'b0;
    end


   //-----------------------------------------------------------------------------
   // Generate ALMOST_FULL flag
   //-----------------------------------------------------------------------------
   //generate if (C_HAS_ALMOST_FULL == 1 || C_PROG_FULL_TYPE > 2 || C_PROG_EMPTY_TYPE > 2) begin : gaf_ss

     wire                 fcomp2;
     wire                 going_afull;
     wire                 leaving_afull;
     wire                 ram_afull_comb;


   assign fcomp2         = (adj_rd_pntr_wr == (wr_pntr + 2'h2));

    generate if (C_WR_PNTR_WIDTH == C_RD_PNTR_WIDTH) begin : gaf_wp_eq_rp
     assign going_afull    = (fcomp2 & write_allow & ~read_allow);
     assign leaving_afull  = (comp1 & read_allow & ~write_allow) | RST_FULL_GEN;
    end endgenerate

    // Write data width is bigger than read data width
    // Write depth is smaller than read depth
    // One write could be equal to 2 or 4 or 8 reads
    generate if (C_WR_PNTR_WIDTH < C_RD_PNTR_WIDTH) begin : gaf_asym
      assign going_afull = (fcomp2 & write_allow & (~ (read_allow & &(rd_pntr[C_RD_PNTR_WIDTH-C_WR_PNTR_WIDTH-1 : 0]))));
      assign leaving_afull = (comp1 & (~write_allow) & read_allow & &(rd_pntr[C_RD_PNTR_WIDTH-C_WR_PNTR_WIDTH-1 : 0])) | RST_FULL_GEN;
    end endgenerate

    generate if (C_WR_PNTR_WIDTH > C_RD_PNTR_WIDTH) begin : gaf_wp_gt_rp 
      assign going_afull = (fcomp2 & write_allow & ~read_allow);
      assign leaving_afull =((comp0 | comp1 | fcomp2) & read_allow) | RST_FULL_GEN;
    end endgenerate

     assign ram_afull_comb  = going_afull | (~leaving_afull & almost_full_i);


     always @(posedge CLK or posedge RST_FULL_FF) begin
       if (RST_FULL_FF)
         almost_full_i   <= C_FULL_FLAGS_RST_VAL;
       else if (srst_wrst_busy)
         almost_full_i   <= #`TCQ C_FULL_FLAGS_RST_VAL;
       else
         almost_full_i   <= #`TCQ ram_afull_comb;
      end
  // end endgenerate // gaf_ss

   //-----------------------------------------------------------------------------
   // Generate ALMOST_EMPTY flag
   //-----------------------------------------------------------------------------
   //generate if (C_HAS_ALMOST_EMPTY == 1) begin : gae_ss

     wire                 ecomp2;
     wire                 going_aempty;
     wire                 leaving_aempty;
     wire                 ram_aempty_comb;
      
     assign ecomp2          = (adj_wr_pntr_rd == (rd_pntr + 2'h2));
   
    generate if (C_WR_PNTR_WIDTH == C_RD_PNTR_WIDTH) begin : gae_wp_eq_rp
     assign going_aempty    = (ecomp2 & ~write_allow & read_allow);
     assign leaving_aempty  = (ecomp1 & write_allow & ~read_allow);
    end endgenerate

    generate if (C_WR_PNTR_WIDTH > C_RD_PNTR_WIDTH) begin : gae_wp_gt_rp
      assign going_aempty = (ecomp2 & read_allow & (~(write_allow & &(wr_pntr[C_WR_PNTR_WIDTH-C_RD_PNTR_WIDTH-1 : 0]))));
      assign leaving_aempty = (ecomp1 & ~read_allow & write_allow & &(wr_pntr[C_WR_PNTR_WIDTH-C_RD_PNTR_WIDTH-1 : 0]));
    end endgenerate
  
   generate if (C_WR_PNTR_WIDTH < C_RD_PNTR_WIDTH) begin : gae_wp_lt_rp 
      assign going_aempty = (ecomp2 & ~write_allow & read_allow);
      assign leaving_aempty =((ecomp2 | ecomp1 |ecomp0) & write_allow);
    end endgenerate


     assign ram_aempty_comb = going_aempty | (~leaving_aempty & almost_empty_i);

     always @(posedge CLK or posedge rst_i) begin
       if (rst_i)
         almost_empty_i  <= 1'b1;
       else if (srst_rrst_busy)
         almost_empty_i  <= #`TCQ 1'b1;
       else
         almost_empty_i  <= #`TCQ ram_aempty_comb;
      end
  // end endgenerate // gae_ss

   //-----------------------------------------------------------------------------
   // Generate PROG_FULL
   //-----------------------------------------------------------------------------

   localparam  C_PF_ASSERT_VAL = (C_PRELOAD_LATENCY == 0) ? 
                                  C_PROG_FULL_THRESH_ASSERT_VAL - EXTRA_WORDS_PF_PARAM : // FWFT 
                                  C_PROG_FULL_THRESH_ASSERT_VAL; // STD
   localparam  C_PF_NEGATE_VAL = (C_PRELOAD_LATENCY == 0) ? 
                                  C_PROG_FULL_THRESH_NEGATE_VAL - EXTRA_WORDS_PF_PARAM: // FWFT
                                  C_PROG_FULL_THRESH_NEGATE_VAL; // STD

   //-----------------------------------------------------------------------------
   // Generate PROG_FULL for single programmable threshold constant
   //-----------------------------------------------------------------------------
   wire [C_WR_PNTR_WIDTH-1:0] temp = C_PF_ASSERT_VAL;   
   generate if (C_PROG_FULL_TYPE == 1) begin : single_pf_const
     always @(posedge CLK or posedge RST_FULL_FF) begin
       if (RST_FULL_FF && C_HAS_RST)
         prog_full_i   <= C_FULL_FLAGS_RST_VAL;
       else begin 
         if (srst_wrst_busy)
           prog_full_i <= #`TCQ C_FULL_FLAGS_RST_VAL;
       else if (IS_ASYMMETRY == 0) begin 
         if (RST_FULL_GEN)
          prog_full_i <= #`TCQ 1'b0;
         else if (diff_pntr == C_PF_ASSERT_VAL && write_only_q)
           prog_full_i <= #`TCQ 1'b1;
         else if (diff_pntr == C_PF_ASSERT_VAL && read_only_q)
           prog_full_i <= #`TCQ 1'b0;
         else
           prog_full_i <= #`TCQ prog_full_i;
       end
       else begin
       if (RST_FULL_GEN)
        prog_full_i <= #`TCQ 1'b0;
       else if (~RST_FULL_GEN ) begin 
        if (diff_pntr>= C_PF_ASSERT_VAL )
          prog_full_i <= #`TCQ 1'b1;
        else if  ((diff_pntr) < C_PF_ASSERT_VAL )
        prog_full_i <= #`TCQ 1'b0;
       else
         prog_full_i <= #`TCQ 1'b0;
        end 
       else
         prog_full_i <= #`TCQ prog_full_i;
       end
      end
     end
   end endgenerate // single_pf_const

   //-----------------------------------------------------------------------------
   // Generate PROG_FULL for multiple programmable threshold constants
   //-----------------------------------------------------------------------------
   generate if (C_PROG_FULL_TYPE == 2) begin : multiple_pf_const
     always @(posedge CLK or posedge RST_FULL_FF) begin
       //if (RST_FULL_FF)
       if (RST_FULL_FF && C_HAS_RST)
         prog_full_i   <= C_FULL_FLAGS_RST_VAL;
       else begin
         if (srst_wrst_busy)
           prog_full_i <= #`TCQ C_FULL_FLAGS_RST_VAL;
       else if (IS_ASYMMETRY == 0) begin 
         if (RST_FULL_GEN)
           prog_full_i <= #`TCQ 1'b0;
         else if (diff_pntr == C_PF_ASSERT_VAL && write_only_q)
           prog_full_i <= #`TCQ 1'b1;
         else if (diff_pntr == C_PF_NEGATE_VAL && read_only_q)
           prog_full_i <= #`TCQ 1'b0;
         else
           prog_full_i <= #`TCQ prog_full_i;
       end
       else begin
       if (RST_FULL_GEN)
        prog_full_i <= #`TCQ 1'b0;
       else if (~RST_FULL_GEN ) begin 
        if (diff_pntr >= C_PF_ASSERT_VAL )
          prog_full_i <= #`TCQ 1'b1;
       else if  (diff_pntr < C_PF_NEGATE_VAL)
         prog_full_i <= #`TCQ 1'b0;
       else
         prog_full_i <= #`TCQ prog_full_i;
        end 
       else
         prog_full_i <= #`TCQ prog_full_i;
       end
      end
     end
   end endgenerate //multiple_pf_const

   //-----------------------------------------------------------------------------
   // Generate PROG_FULL for single programmable threshold input port
   //-----------------------------------------------------------------------------
   wire [C_WR_PNTR_WIDTH-1:0] pf3_assert_val = (C_PRELOAD_LATENCY == 0) ? 
                                               PROG_FULL_THRESH - EXTRA_WORDS_PF: // FWFT
                                               PROG_FULL_THRESH; // STD
   generate if (C_PROG_FULL_TYPE == 3) begin : single_pf_input

     always @(posedge CLK or posedge RST_FULL_FF) begin//0
       //if (RST_FULL_FF)
       if (RST_FULL_FF && C_HAS_RST)
         prog_full_i   <= C_FULL_FLAGS_RST_VAL;
       else begin //1
         if (srst_wrst_busy)
           prog_full_i <= #`TCQ C_FULL_FLAGS_RST_VAL;
       else if (IS_ASYMMETRY == 0) begin//2 
         if (RST_FULL_GEN)
           prog_full_i <= #`TCQ 1'b0;
         else if (~almost_full_i) begin//3
           if (diff_pntr > pf3_assert_val)
             prog_full_i <= #`TCQ 1'b1;
           else if (diff_pntr == pf3_assert_val) begin//4
             if (read_only_q)
               prog_full_i <= #`TCQ 1'b0;
             else
               prog_full_i <= #`TCQ 1'b1;
           end else//4
             prog_full_i <= #`TCQ 1'b0;
         end else//3
           prog_full_i <= #`TCQ prog_full_i;
       end //2
       else begin//5
       if (RST_FULL_GEN)
        prog_full_i <= #`TCQ 1'b0;
       else if (~full_i ) begin//6 
        if (diff_pntr >= pf3_assert_val )
          prog_full_i <= #`TCQ 1'b1;
        else if  (diff_pntr < pf3_assert_val) begin//7
         prog_full_i <= #`TCQ 1'b0;
       end//7
       end//6
      else
           prog_full_i <= #`TCQ prog_full_i;
       end//5
     end//1
     end//0
   end endgenerate //single_pf_input
  
   //-----------------------------------------------------------------------------
   // Generate PROG_FULL for multiple programmable threshold input ports
   //-----------------------------------------------------------------------------
   wire [C_WR_PNTR_WIDTH-1:0] pf_assert_val = (C_PRELOAD_LATENCY == 0) ? 
                                               (PROG_FULL_THRESH_ASSERT -EXTRA_WORDS_PF) : // FWFT
                                               PROG_FULL_THRESH_ASSERT; // STD
   wire [C_WR_PNTR_WIDTH-1:0] pf_negate_val = (C_PRELOAD_LATENCY == 0) ? 
                                               (PROG_FULL_THRESH_NEGATE -EXTRA_WORDS_PF) : // FWFT
                                               PROG_FULL_THRESH_NEGATE; // STD

   generate if (C_PROG_FULL_TYPE == 4) begin : multiple_pf_inputs
     always @(posedge CLK or posedge RST_FULL_FF) begin
       if (RST_FULL_FF && C_HAS_RST)
         prog_full_i   <= C_FULL_FLAGS_RST_VAL;
       else begin
         if (srst_wrst_busy)
           prog_full_i <= #`TCQ C_FULL_FLAGS_RST_VAL;
       else if (IS_ASYMMETRY == 0) begin 
         if (RST_FULL_GEN)
           prog_full_i <= #`TCQ 1'b0;
         else if (~almost_full_i) begin
           if (diff_pntr >= pf_assert_val)
             prog_full_i <= #`TCQ 1'b1;
           else if ((diff_pntr == pf_negate_val && read_only_q) ||
                  diff_pntr < pf_negate_val)
             prog_full_i <= #`TCQ 1'b0;
           else
             prog_full_i <= #`TCQ prog_full_i;
         end else
           prog_full_i <= #`TCQ prog_full_i;
       end
       else begin
       if (RST_FULL_GEN)
        prog_full_i <= #`TCQ 1'b0;
       else if (~full_i ) begin 
        if (diff_pntr >= pf_assert_val )
          prog_full_i <= #`TCQ 1'b1;
       else if (diff_pntr < pf_negate_val) 
         prog_full_i <= #`TCQ 1'b0;
       else
         prog_full_i <= #`TCQ prog_full_i;
        end 
       else
         prog_full_i <= #`TCQ prog_full_i;
       end

     end
   end
   end endgenerate //multiple_pf_inputs

   //-----------------------------------------------------------------------------
   // Generate PROG_EMPTY
   //-----------------------------------------------------------------------------
   localparam  C_PE_ASSERT_VAL = (C_PRELOAD_LATENCY == 0) ?
                                  C_PROG_EMPTY_THRESH_ASSERT_VAL - 2: // FWFT
                                  C_PROG_EMPTY_THRESH_ASSERT_VAL; // STD
   localparam  C_PE_NEGATE_VAL = (C_PRELOAD_LATENCY == 0) ?
                                  C_PROG_EMPTY_THRESH_NEGATE_VAL - 2: // FWFT
                                  C_PROG_EMPTY_THRESH_NEGATE_VAL; // STD

   //-----------------------------------------------------------------------------
   // Generate PROG_EMPTY for single programmable threshold constant
   //-----------------------------------------------------------------------------
   generate if (C_PROG_EMPTY_TYPE == 1) begin : single_pe_const
     always @(posedge CLK or posedge rst_i) begin
       //if (rst_i) 
       if (rst_i && C_HAS_RST) 
         prog_empty_i  <= 1'b1;
       else begin
         if (srst_rrst_busy) 
           prog_empty_i <= #`TCQ 1'b1;
       else if (IS_ASYMMETRY == 0) begin 
         if (diff_pntr_pe == C_PE_ASSERT_VAL && read_only_q)
           prog_empty_i <= #`TCQ 1'b1;
         else if (diff_pntr_pe == C_PE_ASSERT_VAL && write_only_q)
           prog_empty_i <= #`TCQ 1'b0;
         else
           prog_empty_i <= #`TCQ prog_empty_i;
       end
       else begin
       if (~rst_i ) begin 
        if (diff_pntr_pe <= C_PE_ASSERT_VAL)
          prog_empty_i <= #`TCQ 1'b1;
        else if  (diff_pntr_pe > C_PE_ASSERT_VAL)
         prog_empty_i <= #`TCQ 1'b0;
        end 
       else
         prog_empty_i <= #`TCQ prog_empty_i;
       end
     end
     end
   end endgenerate // single_pe_const

   //-----------------------------------------------------------------------------
   // Generate PROG_EMPTY for multiple programmable threshold constants
   //-----------------------------------------------------------------------------
   generate if (C_PROG_EMPTY_TYPE == 2) begin : multiple_pe_const
     always @(posedge CLK or posedge rst_i) begin
       //if (rst_i)
       if (rst_i && C_HAS_RST) 
         prog_empty_i  <= 1'b1;
       else begin
         if (srst_rrst_busy)
           prog_empty_i <= #`TCQ 1'b1;
       else if (IS_ASYMMETRY == 0) begin 
         if (diff_pntr_pe == C_PE_ASSERT_VAL && read_only_q)
           prog_empty_i <= #`TCQ 1'b1;
         else if (diff_pntr_pe == C_PE_NEGATE_VAL && write_only_q)
           prog_empty_i <= #`TCQ 1'b0;
         else
           prog_empty_i <= #`TCQ prog_empty_i;
       end
       else begin
       if (~rst_i ) begin 
        if (diff_pntr_pe <= C_PE_ASSERT_VAL )
          prog_empty_i <= #`TCQ 1'b1;
        else if (diff_pntr_pe > C_PE_NEGATE_VAL) 
         prog_empty_i <= #`TCQ 1'b0;
       else
         prog_empty_i <= #`TCQ prog_empty_i;
        end 
       else
         prog_empty_i <= #`TCQ prog_empty_i;
       end

     end

     end
   end endgenerate //multiple_pe_const

   //-----------------------------------------------------------------------------
   // Generate PROG_EMPTY for single programmable threshold input port
   //-----------------------------------------------------------------------------
   wire [C_RD_PNTR_WIDTH-1:0] pe3_assert_val = (C_PRELOAD_LATENCY == 0) ?
                                               (PROG_EMPTY_THRESH -2) : // FWFT
                                                PROG_EMPTY_THRESH; // STD
   generate if (C_PROG_EMPTY_TYPE == 3) begin : single_pe_input
     always @(posedge CLK or posedge rst_i) begin
       //if (rst_i)
       if (rst_i && C_HAS_RST) 
         prog_empty_i  <= 1'b1;
       else begin
         if (srst_rrst_busy)
           prog_empty_i <= #`TCQ 1'b1;
       else if (IS_ASYMMETRY == 0) begin 
          if (~almost_full_i) begin
           if (diff_pntr_pe < pe3_assert_val)
             prog_empty_i <= #`TCQ 1'b1;
           else if (diff_pntr_pe == pe3_assert_val) begin
             if (write_only_q)
               prog_empty_i <= #`TCQ 1'b0;
             else
               prog_empty_i <= #`TCQ 1'b1;
           end else
             prog_empty_i <= #`TCQ 1'b0;
         end else
           prog_empty_i <= #`TCQ prog_empty_i;
       end
       else begin
        if (diff_pntr_pe <= pe3_assert_val )
          prog_empty_i <= #`TCQ 1'b1;
        else if  (diff_pntr_pe > pe3_assert_val)
         prog_empty_i <= #`TCQ 1'b0;
       else
         prog_empty_i <= #`TCQ prog_empty_i;
        end 
     end

     end
   end endgenerate // single_pe_input

   //-----------------------------------------------------------------------------
   // Generate PROG_EMPTY for multiple programmable threshold input ports
   //-----------------------------------------------------------------------------
   wire [C_RD_PNTR_WIDTH-1:0] pe4_assert_val = (C_PRELOAD_LATENCY == 0) ?
                                               (PROG_EMPTY_THRESH_ASSERT - 2) : // FWFT
                                                PROG_EMPTY_THRESH_ASSERT; // STD
   wire [C_RD_PNTR_WIDTH-1:0] pe4_negate_val = (C_PRELOAD_LATENCY == 0) ?
                                               (PROG_EMPTY_THRESH_NEGATE - 2) : // FWFT
                                                PROG_EMPTY_THRESH_NEGATE; // STD
   generate if (C_PROG_EMPTY_TYPE == 4) begin : multiple_pe_inputs
     always @(posedge CLK or posedge rst_i) begin
       //if (rst_i)
       if (rst_i && C_HAS_RST) 
         prog_empty_i  <= 1'b1;
       else begin
         if (srst_rrst_busy)
           prog_empty_i <= #`TCQ 1'b1;
      else if (IS_ASYMMETRY == 0) begin 
          if (~almost_full_i) begin
           if (diff_pntr_pe <= pe4_assert_val)
             prog_empty_i <= #`TCQ 1'b1;
           else if (((diff_pntr_pe == pe4_negate_val) && write_only_q) || 
                     (diff_pntr_pe > pe4_negate_val)) begin
             prog_empty_i <= #`TCQ 1'b0;
           end else
             prog_empty_i <= #`TCQ prog_empty_i;
         end else
           prog_empty_i <= #`TCQ prog_empty_i;
       end
       else begin
        if (diff_pntr_pe <= pe4_assert_val )
          prog_empty_i <= #`TCQ 1'b1;
        else if (diff_pntr_pe > pe4_negate_val) 
         prog_empty_i <= #`TCQ 1'b0;
       else
         prog_empty_i <= #`TCQ prog_empty_i;
        end 
     end
     end
   end endgenerate // multiple_pe_inputs

endmodule // fifo_generator_v13_1_2_bhv_ver_ss



/**************************************************************************
 * First-Word Fall-Through module (preload 0)
 **************************************************************************/
module fifo_generator_v13_1_2_bhv_ver_preload0
  #(
    parameter  C_DOUT_RST_VAL            = "",
    parameter  C_DOUT_WIDTH              = 8,
    parameter  C_HAS_RST                 = 0,
    parameter  C_ENABLE_RST_SYNC         = 0,
    parameter  C_HAS_SRST                = 0,
    parameter  C_USE_EMBEDDED_REG        = 0,
    parameter  C_EN_SAFETY_CKT           = 0, 
    parameter  C_USE_DOUT_RST            = 0,
    parameter  C_USE_ECC                 = 0,
    parameter  C_USERVALID_LOW           = 0,
    parameter  C_USERUNDERFLOW_LOW       = 0,
    parameter  C_MEMORY_TYPE             = 0,
    parameter  C_FIFO_TYPE               = 0
  )
  (
    //Inputs
    input                          SAFETY_CKT_RD_RST,
    input                          RD_CLK,
    input                          RD_RST,
    input                          SRST,
    input                          WR_RST_BUSY,
    input                          RD_RST_BUSY,
    input                          RD_EN,
    input                          FIFOEMPTY,
    input       [C_DOUT_WIDTH-1:0] FIFODATA,
    input                          FIFOSBITERR,
    input                          FIFODBITERR,
   
    //Outputs
    output reg  [C_DOUT_WIDTH-1:0] USERDATA,
    output                         USERVALID,
    output                         USERUNDERFLOW,
    output                         USEREMPTY,
    output                         USERALMOSTEMPTY,
    output                         RAMVALID,
    output                         FIFORDEN,
    output reg                     USERSBITERR,
    output reg                     USERDBITERR,
    output reg                     STAGE2_REG_EN,
    output                         fab_read_data_valid_i_o,
    output                         read_data_valid_i_o,
    output                         ram_valid_i_o,
    output      [1:0]              VALID_STAGES 
  );
 //Internal signals
 wire                      preloadstage1;
 wire                      preloadstage2;
 reg                       ram_valid_i;
 reg                       fab_valid;
 reg                       read_data_valid_i;
 reg                       fab_read_data_valid_i;
 reg                       fab_read_data_valid_i_1;
 reg                       ram_valid_i_d;
 reg                       read_data_valid_i_d;
 reg                       fab_read_data_valid_i_d;
 wire                      ram_regout_en;
 reg                       ram_regout_en_d1;
 reg                       ram_regout_en_d2;
 wire                      fab_regout_en;
 wire                      ram_rd_en;
 reg                       empty_i        = 1'b1;
 reg                       empty_sckt     = 1'b1;
 reg                       sckt_rrst_q    = 1'b0;
 reg                       sckt_rrst_done = 1'b0;
 reg                       empty_q        = 1'b1;
 reg                       rd_en_q        = 1'b0;
 reg                       almost_empty_i = 1'b1;
 reg                       almost_empty_q = 1'b1;
 wire                      rd_rst_i;
 wire                      srst_i;
 reg  [C_DOUT_WIDTH-1:0]   userdata_both;
 wire                      uservalid_both;
 wire                      uservalid_one;
 reg                       user_sbiterr_both = 1'b0;
 reg                       user_dbiterr_both = 1'b0;
  
assign ram_valid_i_o = ram_valid_i;
assign read_data_valid_i_o = read_data_valid_i;
assign fab_read_data_valid_i_o = fab_read_data_valid_i; 



/*************************************************************************
* FUNCTIONS
*************************************************************************/

   /*************************************************************************
    * hexstr_conv
    *   Converts a string of type hex to a binary value (for C_DOUT_RST_VAL)
    ***********************************************************************/
    function [C_DOUT_WIDTH-1:0] hexstr_conv;
    input [(C_DOUT_WIDTH*8)-1:0] def_data;

    integer index,i,j;
    reg [3:0] bin;

    begin
      index = 0;
      hexstr_conv = 'b0;
      for( i=C_DOUT_WIDTH-1; i>=0; i=i-1 )
      begin
        case (def_data[7:0])
          8'b00000000 :
          begin
            bin = 4'b0000;
            i = -1;
          end
          8'b00110000 : bin = 4'b0000;
          8'b00110001 : bin = 4'b0001;
          8'b00110010 : bin = 4'b0010;
          8'b00110011 : bin = 4'b0011;
          8'b00110100 : bin = 4'b0100;
          8'b00110101 : bin = 4'b0101;
          8'b00110110 : bin = 4'b0110;
          8'b00110111 : bin = 4'b0111;
          8'b00111000 : bin = 4'b1000;
          8'b00111001 : bin = 4'b1001;
          8'b01000001 : bin = 4'b1010;
          8'b01000010 : bin = 4'b1011;
          8'b01000011 : bin = 4'b1100;
          8'b01000100 : bin = 4'b1101;
          8'b01000101 : bin = 4'b1110;
          8'b01000110 : bin = 4'b1111;
          8'b01100001 : bin = 4'b1010;
          8'b01100010 : bin = 4'b1011;
          8'b01100011 : bin = 4'b1100;
          8'b01100100 : bin = 4'b1101;
          8'b01100101 : bin = 4'b1110;
          8'b01100110 : bin = 4'b1111;
          default :
          begin
            bin = 4'bx;
          end
        endcase
        for( j=0; j<4; j=j+1)
        begin
          if ((index*4)+j < C_DOUT_WIDTH)
          begin
            hexstr_conv[(index*4)+j] = bin[j];
          end
        end
        index = index + 1;
        def_data = def_data >> 8;
      end
    end
  endfunction

   
   //*************************************************************************
   //  Set power-on states for regs
   //*************************************************************************
   initial begin
      ram_valid_i       = 1'b0;
      fab_valid         = 1'b0;
      read_data_valid_i = 1'b0;
      fab_read_data_valid_i = 1'b0;
      fab_read_data_valid_i_1 = 1'b0;
      USERDATA          = hexstr_conv(C_DOUT_RST_VAL);
      userdata_both          = hexstr_conv(C_DOUT_RST_VAL);
      USERSBITERR       = 1'b0;
      USERDBITERR       = 1'b0;
      user_sbiterr_both = 1'b0;
      user_dbiterr_both = 1'b0;
   end //initial

   //***************************************************************************
   //  connect up optional reset
   //***************************************************************************
   assign rd_rst_i = (C_HAS_RST == 1 || C_ENABLE_RST_SYNC == 0) ? RD_RST : 0;
   assign srst_i = C_EN_SAFETY_CKT ? SAFETY_CKT_RD_RST : C_HAS_SRST ? SRST : 0;

   reg  sckt_rd_rst_fwft = 1'b0;
   reg  fwft_rst_done_i  = 1'b0;
   wire fwft_rst_done;
   assign fwft_rst_done = C_EN_SAFETY_CKT ? fwft_rst_done_i : 1'b1;
   always @ (posedge RD_CLK) begin
     sckt_rd_rst_fwft <= #`TCQ SAFETY_CKT_RD_RST;
   end

   always @ (posedge rd_rst_i or posedge RD_CLK) begin
     if (rd_rst_i)
       fwft_rst_done_i  <= 1'b0;
     else if (sckt_rd_rst_fwft & ~SAFETY_CKT_RD_RST)
       fwft_rst_done_i  <= #`TCQ 1'b1;
   end

   localparam INVALID             = 0;
   localparam STAGE1_VALID        = 2;
   localparam STAGE2_VALID        = 1;
   localparam BOTH_STAGES_VALID   = 3;

   reg  [1:0] curr_fwft_state = INVALID;
   reg  [1:0] next_fwft_state = INVALID;


generate if (C_USE_EMBEDDED_REG < 3 && C_FIFO_TYPE != 2) begin
         always @* begin
         case (curr_fwft_state)
            INVALID: begin
               if (~FIFOEMPTY)
                  next_fwft_state     <= STAGE1_VALID;
               else
                  next_fwft_state     <= INVALID;
               end
            STAGE1_VALID: begin
               if (FIFOEMPTY)
                  next_fwft_state     <= STAGE2_VALID;
               else
                  next_fwft_state     <= BOTH_STAGES_VALID;
               end
            STAGE2_VALID: begin
               if (FIFOEMPTY && RD_EN)
                  next_fwft_state     <= INVALID;
               else if (~FIFOEMPTY && RD_EN)
                  next_fwft_state     <= STAGE1_VALID;
               else if (~FIFOEMPTY && ~RD_EN)
                  next_fwft_state     <= BOTH_STAGES_VALID;
               else
                  next_fwft_state     <= STAGE2_VALID;
               end
            BOTH_STAGES_VALID: begin
               if (FIFOEMPTY && RD_EN)
                  next_fwft_state     <= STAGE2_VALID;
               else if (~FIFOEMPTY && RD_EN)
                  next_fwft_state     <= BOTH_STAGES_VALID;
               else
                  next_fwft_state     <= BOTH_STAGES_VALID;
               end
            default: next_fwft_state     <= INVALID;
         endcase
      end

      always @ (posedge rd_rst_i or posedge RD_CLK) begin
         if (rd_rst_i && C_EN_SAFETY_CKT == 0)
            curr_fwft_state  <= INVALID;
         else if (srst_i)
            curr_fwft_state  <= #`TCQ INVALID;
         else
            curr_fwft_state  <= #`TCQ next_fwft_state;
      end

      always @* begin
         case (curr_fwft_state)
            INVALID:           STAGE2_REG_EN <= 1'b0;
            STAGE1_VALID:      STAGE2_REG_EN <= 1'b1;
            STAGE2_VALID:      STAGE2_REG_EN <= 1'b0;
            BOTH_STAGES_VALID: STAGE2_REG_EN <= RD_EN;
            default:           STAGE2_REG_EN <= 1'b0;
         endcase
      end

 
    assign VALID_STAGES = curr_fwft_state;

     //***************************************************************************
     //  preloadstage2 indicates that stage2 needs to be updated. This is true
     //  whenever read_data_valid is false, and RAM_valid is true.
     //***************************************************************************
     
     assign preloadstage2 = ram_valid_i & (~read_data_valid_i | RD_EN );
    

     //***************************************************************************
     //  preloadstage1 indicates that stage1 needs to be updated. This is true
     //  whenever the RAM has data (RAM_EMPTY is false), and either RAM_Valid is
     //  false (indicating that Stage1 needs updating), or preloadstage2 is active
     //  (indicating that Stage2 is going to update, so Stage1, therefore, must
     //  also be updated to keep it valid.
     //***************************************************************************
     assign preloadstage1 = ((~ram_valid_i | preloadstage2) & ~FIFOEMPTY);
  
     //***************************************************************************
     // Calculate RAM_REGOUT_EN
     //  The output registers are controlled by the ram_regout_en signal.
     //  These registers should be updated either when the output in Stage2 is
     //  invalid (preloadstage2), OR when the user is reading, in which case the
     //  Stage2 value will go invalid unless it is replenished.
     //***************************************************************************
     assign ram_regout_en = preloadstage2;

     //***************************************************************************
     // Calculate RAM_RD_EN
     //   RAM_RD_EN will be asserted whenever the RAM needs to be read in order to
     //  update the value in Stage1.
     //   One case when this happens is when preloadstage1=true, which indicates
     //  that the data in Stage1 or Stage2 is invalid, and needs to automatically
     //  be updated.
     //   The other case is when the user is reading from the FIFO, which 
     // guarantees that Stage1 or Stage2 will be invalid on the next clock 
     // cycle, unless it is replinished by data from the memory. So, as long 
     // as the RAM has data in it, a read of the RAM should occur.
     //***************************************************************************
     assign ram_rd_en = (RD_EN & ~FIFOEMPTY) | preloadstage1;
   end
endgenerate // gnll_fifo

   reg curr_state         = 0;
   reg next_state         = 0;
   reg leaving_empty_fwft = 0;
   reg going_empty_fwft   = 0;
   reg empty_i_q          = 0;
   reg ram_rd_en_fwft     = 0;
   generate if (C_FIFO_TYPE == 2) begin : gll_fifo
     always @* begin // FSM fo FWFT
       case (curr_state)
         1'b0: begin
           if (~FIFOEMPTY)
             next_state <= 1'b1;
           else
             next_state <= 1'b0;
           end
         1'b1: begin
           if (FIFOEMPTY && RD_EN)
             next_state <= 1'b0;
           else
             next_state <= 1'b1;
           end
         default: next_state <= 1'b0;
       endcase
     end

     always @ (posedge RD_CLK or posedge rd_rst_i) begin
        if (rd_rst_i) begin
           empty_i       <= 1'b1;
           empty_i_q     <= 1'b1;
           ram_valid_i   <= 1'b0;
        end else if (srst_i) begin
           empty_i       <= #`TCQ 1'b1;
           empty_i_q     <= #`TCQ 1'b1;
           ram_valid_i   <= #`TCQ 1'b0;
        end else begin
           empty_i       <= #`TCQ going_empty_fwft | (~leaving_empty_fwft & empty_i);
           empty_i_q     <= #`TCQ FIFOEMPTY;
           ram_valid_i   <= #`TCQ next_state;
        end
     end //always

     always @ (posedge RD_CLK or posedge rd_rst_i) begin
        if (rd_rst_i && C_EN_SAFETY_CKT == 0) begin
           curr_state    <= 1'b0;
        end else if (srst_i) begin
           curr_state    <= #`TCQ 1'b0;
        end else begin
           curr_state    <= #`TCQ next_state;
        end
     end //always

     wire                  fe_of_empty; 
     assign fe_of_empty   = empty_i_q & ~FIFOEMPTY;

     always @* begin // Finding leaving empty
       case (curr_state)
         1'b0:    leaving_empty_fwft <= fe_of_empty;
         1'b1:    leaving_empty_fwft <= 1'b1;
         default: leaving_empty_fwft <= 1'b0;
       endcase
     end

     always @* begin // Finding going empty
       case (curr_state)
         1'b1:    going_empty_fwft <= FIFOEMPTY & RD_EN;
         default: going_empty_fwft <= 1'b0;
       endcase
     end

     always @* begin // Generating FWFT rd_en
       case (curr_state)
         1'b0:    ram_rd_en_fwft <= ~FIFOEMPTY;
         1'b1:    ram_rd_en_fwft <= ~FIFOEMPTY & RD_EN;
         default: ram_rd_en_fwft <= 1'b0;
       endcase
     end

     assign ram_regout_en = ram_rd_en_fwft;
     //assign ram_regout_en_d1 = ram_rd_en_fwft;
     //assign ram_regout_en_d2 = ram_rd_en_fwft;
     assign ram_rd_en     = ram_rd_en_fwft;
   end endgenerate // gll_fifo


   //***************************************************************************
   // Calculate RAMVALID_P0_OUT
   //   RAMVALID_P0_OUT indicates that the data in Stage1 is valid.
   //
   //   If the RAM is being read from on this clock cycle (ram_rd_en=1), then
   //   RAMVALID_P0_OUT is certainly going to be true.
   //   If the RAM is not being read from, but the output registers are being
   //   updated to fill Stage2 (ram_regout_en=1), then Stage1 will be emptying,
   //   therefore causing RAMVALID_P0_OUT to be false.
   //   Otherwise, RAMVALID_P0_OUT will remain unchanged.
   //***************************************************************************
   // PROCESS regout_valid
   generate if (C_FIFO_TYPE < 2) begin : gnll_fifo_ram_valid
     always @ (posedge RD_CLK or posedge rd_rst_i) begin  
        if (rd_rst_i) begin 
           // asynchronous reset (active high)
           ram_valid_i     <= #`TCQ 1'b0;
        end else begin
           if (srst_i) begin 
              // synchronous reset (active high)
              ram_valid_i     <= #`TCQ 1'b0;
           end else begin
              if (ram_rd_en == 1'b1) begin
                 ram_valid_i   <= #`TCQ 1'b1;
              end else begin
                 if (ram_regout_en == 1'b1)
                   ram_valid_i <= #`TCQ 1'b0;
                 else
                   ram_valid_i <= #`TCQ ram_valid_i;
              end
           end //srst_i
        end //rd_rst_i
     end //always
   end endgenerate // gnll_fifo_ram_valid
   
   //***************************************************************************
   // Calculate READ_DATA_VALID
   //  READ_DATA_VALID indicates whether the value in Stage2 is valid or not.
   //  Stage2 has valid data whenever Stage1 had valid data and 
   //  ram_regout_en_i=1, such that the data in Stage1 is propogated 
   //  into Stage2.
   //***************************************************************************
  
 generate if(C_USE_EMBEDDED_REG < 3) begin
 always @ (posedge RD_CLK or posedge rd_rst_i) begin
      if (rd_rst_i)
        read_data_valid_i <= #`TCQ 1'b0;
      else if (srst_i)
        read_data_valid_i <= #`TCQ 1'b0;
      else
        read_data_valid_i <= #`TCQ ram_valid_i | (read_data_valid_i & ~RD_EN);
   end //always
end 
endgenerate

   
   
   //**************************************************************************
   // Calculate EMPTY
   //  Defined as the inverse of READ_DATA_VALID
   //
   // Description:
   //
   //  If read_data_valid_i indicates that the output is not valid,
   // and there is no valid data on the output of the ram to preload it
   // with, then we will report empty.
   //
   //  If there is no valid data on the output of the ram and we are
   // reading, then the FIFO will go empty.
   //
   //**************************************************************************
   generate if (C_FIFO_TYPE < 2 && C_USE_EMBEDDED_REG < 3) begin : gnll_fifo_empty
     always @ (posedge RD_CLK or posedge rd_rst_i) begin
        if (rd_rst_i) begin
           // asynchronous reset (active high)
           empty_i <= #`TCQ 1'b1;
        end else begin
           if (srst_i) begin
              // synchronous reset (active high)
              empty_i <= #`TCQ 1'b1;
           end else begin
              // rising clock edge
              empty_i <= #`TCQ (~ram_valid_i & ~read_data_valid_i) | (~ram_valid_i & RD_EN);
           end
        end
     end //always
   end endgenerate // gnll_fifo_empty
   
   // Register RD_EN from user to calculate USERUNDERFLOW.
   // Register empty_i to calculate USERUNDERFLOW.
   always @ (posedge RD_CLK) begin
     rd_en_q <= #`TCQ RD_EN;
     empty_q <= #`TCQ empty_i;
   end //always
   
   
   //***************************************************************************
   // Calculate user_almost_empty
   //  user_almost_empty is defined such that, unless more words are written
   //  to the FIFO, the next read will cause the FIFO to go EMPTY.
   //
   //  In most cases, whenever the output registers are updated (due to a user
   // read or a preload condition), then user_almost_empty will update to
   // whatever RAM_EMPTY is.
   //
   //  The exception is when the output is valid, the user is not reading, and
   // Stage1 is not empty. In this condition, Stage1 will be preloaded from the
   // memory, so we need to make sure user_almost_empty deasserts properly under
   // this condition.
   //***************************************************************************
 generate if ( C_USE_EMBEDDED_REG < 3) begin
  always @ (posedge RD_CLK or posedge rd_rst_i)
     begin
        if (rd_rst_i) begin         // asynchronous reset (active high)
             almost_empty_i <= #`TCQ 1'b1;
             almost_empty_q <= #`TCQ 1'b1;
        end else begin // rising clock edge
           if (srst_i) begin          // synchronous reset (active high)
              almost_empty_i <= #`TCQ 1'b1;
              almost_empty_q <= #`TCQ 1'b1;
           end else begin
              if ((ram_regout_en) | (~FIFOEMPTY & read_data_valid_i & ~RD_EN)) begin
                 almost_empty_i <= #`TCQ FIFOEMPTY;
              end
              almost_empty_q   <= #`TCQ empty_i;
           end
        end
     end //always
end
endgenerate
   
   
     
  // BRAM resets synchronously
 generate 
        if (C_EN_SAFETY_CKT==0 && C_USE_EMBEDDED_REG < 3) begin
   always @ ( posedge rd_rst_i)
     begin
        if (rd_rst_i || srst_i) begin
          if (C_USE_DOUT_RST == 1 && C_MEMORY_TYPE < 2)
           @(posedge RD_CLK)
            USERDATA     <= #`TCQ hexstr_conv(C_DOUT_RST_VAL);
        end
     end //always

 
   always @ (posedge RD_CLK or posedge rd_rst_i)
     begin
        if (rd_rst_i) begin //asynchronous reset (active high)
          if (C_USE_ECC == 0) begin // Reset S/DBITERR only if ECC is OFF
            USERSBITERR    <= #`TCQ 0;
            USERDBITERR    <= #`TCQ 0;
          end
          // DRAM resets asynchronously
          if (C_USE_DOUT_RST == 1 && C_MEMORY_TYPE == 2) begin  //asynchronous reset (active high)
             USERDATA     <= #`TCQ hexstr_conv(C_DOUT_RST_VAL);
        end
        end  else begin // rising clock edge
          if (srst_i) begin
            if (C_USE_ECC == 0) begin // Reset S/DBITERR only if ECC is OFF
              USERSBITERR  <= #`TCQ 0;
              USERDBITERR  <= #`TCQ 0;
            end
            if (C_USE_DOUT_RST == 1) begin
              USERDATA   <= #`TCQ hexstr_conv(C_DOUT_RST_VAL);
          end
          end  else if (fwft_rst_done) begin
            if (ram_regout_en) begin
               USERDATA     <= #`TCQ FIFODATA;
               USERSBITERR  <= #`TCQ FIFOSBITERR;
               USERDBITERR  <= #`TCQ FIFODBITERR;
            end
          end
        end
     end //always
   end   //if
  endgenerate
//safety ckt with one register
generate
       if (C_EN_SAFETY_CKT==1 && C_USE_EMBEDDED_REG < 3) begin
         reg [C_DOUT_WIDTH-1:0]     dout_rst_val_d1;
         reg [C_DOUT_WIDTH-1:0]     dout_rst_val_d2;
         reg [1:0] rst_delayed_sft1              =1;
         reg [1:0] rst_delayed_sft2              =1;
         reg [1:0] rst_delayed_sft3              =1;
         reg [1:0] rst_delayed_sft4              =1;
         
        always@(posedge RD_CLK)
          begin
          rst_delayed_sft1 <= #`TCQ rd_rst_i;
          rst_delayed_sft2 <= #`TCQ rst_delayed_sft1;
          rst_delayed_sft3 <= #`TCQ rst_delayed_sft2; 
          rst_delayed_sft4 <= #`TCQ rst_delayed_sft3;
          end
        always @ (posedge RD_CLK)
     begin
        if (rd_rst_i || srst_i) begin
          if (C_USE_DOUT_RST == 1 && C_MEMORY_TYPE < 2 && rst_delayed_sft1 == 1'b1) begin
            @(posedge RD_CLK)
            USERDATA     <= #`TCQ hexstr_conv(C_DOUT_RST_VAL);
          end
        end
     end //always
 
   always @ (posedge RD_CLK or posedge rd_rst_i)
     begin
        if (rd_rst_i) begin //asynchronous reset (active high)
          if (C_USE_ECC == 0) begin // Reset S/DBITERR only if ECC is OFF
            USERSBITERR    <= #`TCQ 0;
            USERDBITERR    <= #`TCQ 0;
          end
          // DRAM resets asynchronously
          if (C_USE_DOUT_RST == 1 && C_MEMORY_TYPE == 2)begin  //asynchronous reset (active high)
          //@(posedge RD_CLK)
            USERDATA     <= #`TCQ hexstr_conv(C_DOUT_RST_VAL);
         end 
       end
        else begin // rising clock edge
          if (srst_i) begin
            if (C_USE_ECC == 0) begin // Reset S/DBITERR only if ECC is OFF
              USERSBITERR  <= #`TCQ 0;
              USERDBITERR  <= #`TCQ 0;
            end
            if (C_USE_DOUT_RST == 1) begin
            //  @(posedge RD_CLK)
              USERDATA   <= #`TCQ hexstr_conv(C_DOUT_RST_VAL);
          end
          end else if (fwft_rst_done) begin
            if (ram_regout_en == 1'b1 && rd_rst_i == 1'b0) begin
               USERDATA     <= #`TCQ FIFODATA;
               USERSBITERR  <= #`TCQ FIFOSBITERR;
               USERDBITERR  <= #`TCQ FIFODBITERR;
            end          
          end
        end
       end //always
  end //if
endgenerate


generate if (C_USE_EMBEDDED_REG == 3 && C_FIFO_TYPE != 2) begin
         

      always @* begin
         case (curr_fwft_state)
            INVALID: begin
               if (~FIFOEMPTY)
                  next_fwft_state     <= STAGE1_VALID;
               else
                  next_fwft_state     <= INVALID;
               end
            STAGE1_VALID: begin
               if (FIFOEMPTY)
                  next_fwft_state     <= STAGE2_VALID;
               else
                  next_fwft_state     <= BOTH_STAGES_VALID;
               end
            STAGE2_VALID: begin
               if (FIFOEMPTY && RD_EN)
                  next_fwft_state     <= INVALID;
               else if (~FIFOEMPTY && RD_EN)
                  next_fwft_state     <= STAGE1_VALID;
               else if (~FIFOEMPTY && ~RD_EN)
                  next_fwft_state     <= BOTH_STAGES_VALID;
               else
                  next_fwft_state     <= STAGE2_VALID;
               end
            BOTH_STAGES_VALID: begin
               if (FIFOEMPTY && RD_EN)
                  next_fwft_state     <= STAGE2_VALID;
               else if (~FIFOEMPTY && RD_EN)
                  next_fwft_state     <= BOTH_STAGES_VALID;
               else
                  next_fwft_state     <= BOTH_STAGES_VALID;
               end
            default: next_fwft_state     <= INVALID;
         endcase
      end

      always @ (posedge rd_rst_i or posedge RD_CLK) begin
         if (rd_rst_i && C_EN_SAFETY_CKT == 0)
            curr_fwft_state  <= INVALID;
         else if (srst_i)
            curr_fwft_state  <= #`TCQ INVALID;
         else
            curr_fwft_state  <= #`TCQ next_fwft_state;
      end

     always @ (posedge RD_CLK or posedge rd_rst_i) begin : proc_delay
            if (rd_rst_i == 1) begin
                ram_regout_en_d1 <= #`TCQ 1'b0;
            end
            else begin
                 if (srst_i == 1'b1) 
                 ram_regout_en_d1 <= #`TCQ 1'b0;
                 else
                 ram_regout_en_d1 <= #`TCQ ram_regout_en;
                 end
            end //always
   //  assign fab_regout_en = ((ram_regout_en_d1 & ~(ram_regout_en_d2) & empty_i) | (RD_EN & !empty_i));
       assign fab_regout_en = ((ram_valid_i == 1'b0 || ram_valid_i == 1'b1) && read_data_valid_i == 1'b1 && fab_read_data_valid_i == 1'b0 )? 1'b1: ((ram_valid_i == 1'b0 || ram_valid_i == 1'b1) && read_data_valid_i == 1'b1 && fab_read_data_valid_i == 1'b1) ? RD_EN : 1'b0;

     always @ (posedge RD_CLK or posedge rd_rst_i) begin : proc_delay1
            if (rd_rst_i == 1) begin
                ram_regout_en_d2 <= #`TCQ 1'b0;
            end
            else begin
                 if (srst_i == 1'b1) 
                 ram_regout_en_d2 <= #`TCQ 1'b0;
                 else
                 ram_regout_en_d2 <= #`TCQ ram_regout_en_d1;
                 end
            end //always

    

      always @* begin
         case (curr_fwft_state)
            INVALID:           STAGE2_REG_EN <= 1'b0;
            STAGE1_VALID:      STAGE2_REG_EN <= 1'b1;
            STAGE2_VALID:      STAGE2_REG_EN <= 1'b0;
            BOTH_STAGES_VALID: STAGE2_REG_EN <= RD_EN;
            default:           STAGE2_REG_EN <= 1'b0;
         endcase
      end

     always @ (posedge RD_CLK) begin
        ram_valid_i_d <= #`TCQ ram_valid_i;
        read_data_valid_i_d <= #`TCQ read_data_valid_i;
        fab_read_data_valid_i_d <= #`TCQ fab_read_data_valid_i;

     end
    assign VALID_STAGES = curr_fwft_state;

     //***************************************************************************
     //  preloadstage2 indicates that stage2 needs to be updated. This is true
     //  whenever read_data_valid is false, and RAM_valid is true.
     //***************************************************************************
    
     assign preloadstage2 = ram_valid_i & (~read_data_valid_i | RD_EN );

     //***************************************************************************
     //  preloadstage1 indicates that stage1 needs to be updated. This is true
     //  whenever the RAM has data (RAM_EMPTY is false), and either RAM_Valid is
     //  false (indicating that Stage1 needs updating), or preloadstage2 is active
     //  (indicating that Stage2 is going to update, so Stage1, therefore, must
     //  also be updated to keep it valid.
     //***************************************************************************
     assign preloadstage1 = ((~ram_valid_i | preloadstage2) & ~FIFOEMPTY);
  
     //***************************************************************************
     // Calculate RAM_REGOUT_EN
     //  The output registers are controlled by the ram_regout_en signal.
     //  These registers should be updated either when the output in Stage2 is
     //  invalid (preloadstage2), OR when the user is reading, in which case the
     //  Stage2 value will go invalid unless it is replenished.
     //***************************************************************************
     assign ram_regout_en = (ram_valid_i == 1'b1 && (read_data_valid_i == 1'b0 || fab_read_data_valid_i == 1'b0)) ? 1'b1 : (read_data_valid_i == 1'b1 && fab_read_data_valid_i == 1'b1 && ram_valid_i == 1'b1) ? RD_EN : 1'b0;

     //***************************************************************************
     // Calculate RAM_RD_EN
     //   RAM_RD_EN will be asserted whenever the RAM needs to be read in order to
     //  update the value in Stage1.
     //   One case when this happens is when preloadstage1=true, which indicates
     //  that the data in Stage1 or Stage2 is invalid, and needs to automatically
     //  be updated.
     //   The other case is when the user is reading from the FIFO, which 
     // guarantees that Stage1 or Stage2 will be invalid on the next clock 
     // cycle, unless it is replinished by data from the memory. So, as long 
     // as the RAM has data in it, a read of the RAM should occur.
     //***************************************************************************
     assign ram_rd_en = ((RD_EN | ~ fab_read_data_valid_i) & ~FIFOEMPTY) | preloadstage1;
   end
   endgenerate // gnll_fifo

   

   //***************************************************************************
   // Calculate RAMVALID_P0_OUT
   //   RAMVALID_P0_OUT indicates that the data in Stage1 is valid.
   //
   //   If the RAM is being read from on this clock cycle (ram_rd_en=1), then
   //   RAMVALID_P0_OUT is certainly going to be true.
   //   If the RAM is not being read from, but the output registers are being
   //   updated to fill Stage2 (ram_regout_en=1), then Stage1 will be emptying,
   //   therefore causing RAMVALID_P0_OUT to be false   //   Otherwise, RAMVALID_P0_OUT will remain unchanged.
   //***************************************************************************
   // PROCESS regout_valid
     generate if (C_FIFO_TYPE < 2 && C_USE_EMBEDDED_REG == 3) begin : gnll_fifo_fab_valid

     
     always @ (posedge RD_CLK or posedge rd_rst_i) begin  
        if (rd_rst_i) begin 
           // asynchronous reset (active high)
           fab_valid     <= #`TCQ 1'b0;
        end else begin
           if (srst_i) begin 
              // synchronous reset (active high)
              fab_valid    <= #`TCQ 1'b0;
           end else begin
              if (ram_regout_en == 1'b1) begin
                 fab_valid  <= #`TCQ 1'b1;
              end else begin
                 if (fab_regout_en == 1'b1)
                   fab_valid <= #`TCQ 1'b0;
                 else
                   fab_valid <= #`TCQ fab_valid;
              end
           end //srst_i
        end //rd_rst_i
     end //always
   end endgenerate // gnll_fifo_fab_valid

   
   //***************************************************************************
   // Calculate READ_DATA_VALID
   //  READ_DATA_VALID indicates whether the value in Stage2 is valid or not.
   //  Stage2 has valid data whenever Stage1 had valid data and 
   //  ram_regout_en_i=1, such that the data in Stage1 is propogated 
   //  into Stage2.
   //***************************************************************************
    generate if(C_USE_EMBEDDED_REG == 3) begin
   always @ (posedge RD_CLK or posedge rd_rst_i) begin
      if (rd_rst_i)
        read_data_valid_i <= #`TCQ 1'b0;
      else if (srst_i)
        read_data_valid_i <= #`TCQ 1'b0;
      else begin
        if (ram_regout_en == 1'b1) begin
          read_data_valid_i <= #`TCQ 1'b1;
        end else begin
         if (fab_regout_en == 1'b1)
          read_data_valid_i <= #`TCQ 1'b0;
        else
          read_data_valid_i <= #`TCQ read_data_valid_i;
        end 
      end 
   end //always
end
endgenerate

//generate if(C_USE_EMBEDDED_REG == 3) begin
//   always @ (posedge RD_CLK or posedge rd_rst_i) begin
//      if (rd_rst_i)
//        read_data_valid_i <= #`TCQ 1'b0;
//      else if (srst_i)
//        read_data_valid_i <= #`TCQ 1'b0;
//
//      if (ram_regout_en == 1'b1) begin
//        fab_read_data_valid_i <= #`TCQ 1'b0;
//      end else begin
//       if (fab_regout_en == 1'b1)
//        fab_read_data_valid_i <= #`TCQ 1'b1;
//      else
//        fab_read_data_valid_i <= #`TCQ fab_read_data_valid_i;
//      end 
//   end //always
//end
//endgenerate

     generate if(C_USE_EMBEDDED_REG == 3 ) begin 
    always @ (posedge RD_CLK or posedge rd_rst_i) begin :fabout_dvalid
      if (rd_rst_i)
        fab_read_data_valid_i <= #`TCQ 1'b0;
      else if (srst_i)
        fab_read_data_valid_i <= #`TCQ 1'b0;
      else 
        fab_read_data_valid_i <= #`TCQ fab_valid | (fab_read_data_valid_i & ~RD_EN);
   end //always
end
endgenerate
 
always @ (posedge RD_CLK ) begin : proc_del1
             begin
                 fab_read_data_valid_i_1 <= #`TCQ fab_read_data_valid_i;
              end
            end //always
 
 
   //**************************************************************************
   // Calculate EMPTY
   //  Defined as the inverse of READ_DATA_VALID
   //
   // Description:
   //
   //  If read_data_valid_i indicates that the output is not valid,
   // and there is no valid data on the output of the ram to preload it
   // with, then we will report empty.
   //
   //  If there is no valid data on the output of the ram and we are
   // reading, then the FIFO will go empty.
   //
   //**************************************************************************
   generate if (C_FIFO_TYPE < 2 && C_USE_EMBEDDED_REG == 3 ) begin : gnll_fifo_empty_both
     always @ (posedge RD_CLK or posedge rd_rst_i) begin
        if (rd_rst_i) begin
           // asynchronous reset (active high)
           empty_i <= #`TCQ 1'b1;
        end else begin
           if (srst_i) begin
              // synchronous reset (active high)
              empty_i <= #`TCQ 1'b1;
           end else begin
              // rising clock edge
              empty_i <= #`TCQ (~fab_valid & ~fab_read_data_valid_i) | (~fab_valid & RD_EN);
           end
        end
     end //always
   end endgenerate // gnll_fifo_empty_both
   
   // Register RD_EN from user to calculate USERUNDERFLOW.
   // Register empty_i to calculate USERUNDERFLOW.
   always @ (posedge RD_CLK) begin
     rd_en_q <= #`TCQ RD_EN;
     empty_q <= #`TCQ empty_i;
   end //always
   
   
   //***************************************************************************
   // Calculate user_almost_empty
   //  user_almost_empty is defined such that, unless more words are written
   //  to the FIFO, the next read will cause the FIFO to go EMPTY.
   //
   //  In most cases, whenever the output registers are updated (due to a user
   // read or a preload condition), then user_almost_empty will update to
   // whatever RAM_EMPTY is.
   //
   //  The exception is when the output is valid, the user is not reading, and
   // Stage1 is not empty. In this condition, Stage1 will be preloaded from the
   // memory, so we need to make sure user_almost_empty deasserts properly under
   // this condition.
   //***************************************************************************
   reg FIFOEMPTY_1;
   generate if (C_USE_EMBEDDED_REG == 3 ) begin
    always @(posedge RD_CLK) begin
            FIFOEMPTY_1 <= #`TCQ FIFOEMPTY;
           end
    end
endgenerate
    generate if (C_USE_EMBEDDED_REG == 3 ) begin
   always @ (posedge RD_CLK or posedge rd_rst_i)
   begin
      if (rd_rst_i) begin         // asynchronous reset (active high)
           almost_empty_i <= #`TCQ 1'b1;
             almost_empty_q <= #`TCQ 1'b1;
        end else begin // rising clock edge
           if (srst_i) begin          // synchronous reset (active high)
              almost_empty_i <= #`TCQ 1'b1;
              almost_empty_q <= #`TCQ 1'b1;
           end else begin
              if ((fab_regout_en) | (ram_valid_i & fab_read_data_valid_i & ~RD_EN)) begin
                 almost_empty_i <= #`TCQ (~ram_valid_i);
              end
              almost_empty_q   <= #`TCQ empty_i;
           end
        end
     end //always
end
endgenerate
     always @ (posedge RD_CLK or posedge rd_rst_i) begin
        if (rd_rst_i) begin
           empty_sckt <= #`TCQ 1'b1;
           sckt_rrst_q <= #`TCQ 1'b0;
           sckt_rrst_done <= #`TCQ 1'b0;
        end else begin
           sckt_rrst_q <= #`TCQ SAFETY_CKT_RD_RST;
           if (sckt_rrst_q && ~SAFETY_CKT_RD_RST) begin
              sckt_rrst_done <= #`TCQ 1'b1;
           end else if (sckt_rrst_done) begin
              // rising clock edge
              empty_sckt <= #`TCQ 1'b0;
           end
        end
     end //always
   
   
//   assign USEREMPTY       = C_EN_SAFETY_CKT ? (sckt_rrst_done ? empty_i : empty_sckt) : empty_i;
   assign USEREMPTY       = empty_i;
   assign USERALMOSTEMPTY = almost_empty_i;
   assign FIFORDEN        = ram_rd_en;
   assign RAMVALID        = (C_USE_EMBEDDED_REG == 3)? fab_valid : ram_valid_i;
   assign uservalid_both       = (C_USERVALID_LOW && C_USE_EMBEDDED_REG == 3)  ? ~fab_read_data_valid_i : ((C_USERVALID_LOW == 0 && C_USE_EMBEDDED_REG == 3) ? fab_read_data_valid_i : 1'b0);
   assign uservalid_one       = (C_USERVALID_LOW && C_USE_EMBEDDED_REG < 3)  ? ~read_data_valid_i :((C_USERVALID_LOW == 0 && C_USE_EMBEDDED_REG < 3) ? read_data_valid_i : 1'b0);
   assign USERVALID = (C_USE_EMBEDDED_REG == 3) ? uservalid_both : uservalid_one;
   assign USERUNDERFLOW   = C_USERUNDERFLOW_LOW ? ~(empty_q & rd_en_q) : empty_q & rd_en_q;
//no safety ckt with both reg
generate 
        if (C_EN_SAFETY_CKT==0 && C_USE_EMBEDDED_REG == 3 ) begin
   always @ (posedge RD_CLK)
     begin
        if (rd_rst_i || srst_i) begin
          if (C_USE_DOUT_RST == 1 && C_MEMORY_TYPE < 2)
            USERDATA          <= #`TCQ hexstr_conv(C_DOUT_RST_VAL);
            userdata_both     <= #`TCQ hexstr_conv(C_DOUT_RST_VAL);
            user_sbiterr_both <= #`TCQ 0;
            user_dbiterr_both <= #`TCQ 0;
        end
     end //always

 
   always @ (posedge RD_CLK or posedge rd_rst_i)
     begin
        if (rd_rst_i) begin //asynchronous reset (active high)
          if (C_USE_ECC == 0) begin // Reset S/DBITERR only if ECC is OFF
            USERSBITERR    <= #`TCQ 0;
            USERDBITERR    <= #`TCQ 0;
            user_sbiterr_both <= #`TCQ 0;
            user_dbiterr_both <= #`TCQ 0;
          end
          // DRAM resets asynchronously
          if (C_USE_DOUT_RST == 1 && C_MEMORY_TYPE == 2) begin  //asynchronous reset (active high)
            USERDATA     <= #`TCQ hexstr_conv(C_DOUT_RST_VAL);
            userdata_both     <= #`TCQ hexstr_conv(C_DOUT_RST_VAL);
            user_sbiterr_both <= #`TCQ 0;
            user_dbiterr_both <= #`TCQ 0;
        end
        end  else begin // rising clock edge
          if (srst_i) begin
            if (C_USE_ECC == 0) begin // Reset S/DBITERR only if ECC is OFF
              USERSBITERR  <= #`TCQ 0;
              USERDBITERR  <= #`TCQ 0;
              user_sbiterr_both <= #`TCQ 0;
              user_dbiterr_both <= #`TCQ 0;
            end
            if (C_USE_DOUT_RST == 1 && C_MEMORY_TYPE == 2) begin
              USERDATA   <= #`TCQ hexstr_conv(C_DOUT_RST_VAL);
              userdata_both   <= #`TCQ hexstr_conv(C_DOUT_RST_VAL);
              user_sbiterr_both <= #`TCQ 0;
              user_dbiterr_both <= #`TCQ 0;
            end
          end else begin
            if (fwft_rst_done) begin
              if (ram_regout_en) begin
                 userdata_both     <= #`TCQ FIFODATA; 
                 user_dbiterr_both <= #`TCQ FIFODBITERR;
                 user_sbiterr_both <= #`TCQ FIFOSBITERR; 
              end
              if (fab_regout_en) begin
                 USERDATA     <= #`TCQ userdata_both;
                 USERDBITERR  <= #`TCQ user_dbiterr_both;
                 USERSBITERR  <= #`TCQ user_sbiterr_both; 
              end             
            end             
          end
        end
     end //always
   end   //if
  endgenerate

//safety_ckt with both registers
 generate
       if (C_EN_SAFETY_CKT==1 && C_USE_EMBEDDED_REG == 3) begin
         reg [C_DOUT_WIDTH-1:0]     dout_rst_val_d1;
         reg [C_DOUT_WIDTH-1:0]     dout_rst_val_d2;
         reg [1:0] rst_delayed_sft1              =1;
         reg [1:0] rst_delayed_sft2              =1;
         reg [1:0] rst_delayed_sft3              =1;
         reg [1:0] rst_delayed_sft4              =1;
         
        always@(posedge RD_CLK) begin
          rst_delayed_sft1 <= #`TCQ rd_rst_i;
          rst_delayed_sft2 <= #`TCQ rst_delayed_sft1;
          rst_delayed_sft3 <= #`TCQ rst_delayed_sft2; 
          rst_delayed_sft4 <= #`TCQ rst_delayed_sft3;
        end
        always @ (posedge RD_CLK) begin
          if (rd_rst_i || srst_i) begin
            if (C_USE_DOUT_RST == 1 && C_MEMORY_TYPE < 2 && rst_delayed_sft1 == 1'b1) begin
              @(posedge RD_CLK)
              USERDATA     <= #`TCQ hexstr_conv(C_DOUT_RST_VAL);
               userdata_both     <= #`TCQ hexstr_conv(C_DOUT_RST_VAL);
              user_sbiterr_both <= #`TCQ 0;
              user_dbiterr_both <= #`TCQ 0;
            end
          end
        end //always
 
   always @ (posedge RD_CLK or posedge rd_rst_i) begin
     if (rd_rst_i) begin //asynchronous reset (active high)
       if (C_USE_ECC == 0) begin // Reset S/DBITERR only if ECC is OFF
         USERSBITERR       <= #`TCQ 0;
         USERDBITERR       <= #`TCQ 0;
         user_sbiterr_both <= #`TCQ 0;
         user_dbiterr_both <= #`TCQ 0;
       end
       // DRAM resets asynchronously
       if (C_USE_DOUT_RST == 1 && C_MEMORY_TYPE == 2)begin  //asynchronous reset (active high)
         USERDATA          <= #`TCQ hexstr_conv(C_DOUT_RST_VAL);
         userdata_both     <= #`TCQ hexstr_conv(C_DOUT_RST_VAL);
         user_sbiterr_both <= #`TCQ 0;
         user_dbiterr_both <= #`TCQ 0;
       end 
     end else begin // rising clock edge
       if (srst_i) begin
         if (C_USE_ECC == 0) begin // Reset S/DBITERR only if ECC is OFF
           USERSBITERR       <= #`TCQ 0;
           USERDBITERR       <= #`TCQ 0;
           user_sbiterr_both <= #`TCQ 0;
           user_dbiterr_both <= #`TCQ 0;
         end
         if (C_USE_DOUT_RST == 1 && C_MEMORY_TYPE == 2) begin
           USERDATA   <= #`TCQ hexstr_conv(C_DOUT_RST_VAL);
         end
       end else if (fwft_rst_done) begin
         if (ram_regout_en == 1'b1 && rd_rst_i == 1'b0) begin
            userdata_both     <= #`TCQ FIFODATA;
            user_dbiterr_both <= #`TCQ FIFODBITERR;
            user_sbiterr_both <= #`TCQ FIFOSBITERR; 
         end
         if (fab_regout_en == 1'b1 && rd_rst_i == 1'b0) begin
            USERDATA          <= #`TCQ userdata_both;
            USERDBITERR       <= #`TCQ user_dbiterr_both;
            USERSBITERR       <= #`TCQ user_sbiterr_both;
         end
       end
     end
   end //always
  end //if
endgenerate

endmodule //fifo_generator_v13_1_2_bhv_ver_preload0


//-----------------------------------------------------------------------------
//
// Register Slice
//   Register one AXI channel on forward and/or reverse signal path
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   reg_slice
//
//--------------------------------------------------------------------------

module fifo_generator_v13_1_2_axic_reg_slice #
  (
   parameter C_FAMILY     = "virtex7",
   parameter C_DATA_WIDTH = 32,
   parameter C_REG_CONFIG = 32'h00000000
   )
  (
   // System Signals
   input  wire                      ACLK,
   input  wire                      ARESET,

   // Slave side
   input  wire [C_DATA_WIDTH-1:0]   S_PAYLOAD_DATA,
   input  wire                      S_VALID,
   output wire                      S_READY,

   // Master side
   output wire [C_DATA_WIDTH-1:0]   M_PAYLOAD_DATA,
   output wire                      M_VALID,
   input  wire                      M_READY
   );

  generate
  ////////////////////////////////////////////////////////////////////
  //
  // Both FWD and REV mode
  //
  ////////////////////////////////////////////////////////////////////
    if (C_REG_CONFIG == 32'h00000000)
    begin
      reg [1:0] state;
      localparam [1:0] 
        ZERO = 2'b10,
        ONE  = 2'b11,
        TWO  = 2'b01;
      
      reg [C_DATA_WIDTH-1:0] storage_data1 = 0;
      reg [C_DATA_WIDTH-1:0] storage_data2 = 0;
      reg                    load_s1;
      wire                   load_s2;
      wire                   load_s1_from_s2;
      reg                    s_ready_i; //local signal of output
      wire                   m_valid_i; //local signal of output

      // assign local signal to its output signal
      assign S_READY = s_ready_i;
      assign M_VALID = m_valid_i;

      reg  areset_d1; // Reset delay register
      always @(posedge ACLK) begin
        areset_d1 <= ARESET;
      end
      
      // Load storage1 with either slave side data or from storage2
      always @(posedge ACLK) 
      begin
        if (load_s1)
          if (load_s1_from_s2)
            storage_data1 <= storage_data2;
          else
            storage_data1 <= S_PAYLOAD_DATA;        
      end

      // Load storage2 with slave side data
      always @(posedge ACLK) 
      begin
        if (load_s2)
          storage_data2 <= S_PAYLOAD_DATA;
      end

      assign M_PAYLOAD_DATA = storage_data1;

      // Always load s2 on a valid transaction even if it's unnecessary
      assign load_s2 = S_VALID & s_ready_i;

      // Loading s1
      always @ *
      begin
        if ( ((state == ZERO) && (S_VALID == 1)) || // Load when empty on slave transaction
             // Load when ONE if we both have read and write at the same time
             ((state == ONE) && (S_VALID == 1) && (M_READY == 1)) ||
             // Load when TWO and we have a transaction on Master side
             ((state == TWO) && (M_READY == 1)))
          load_s1 = 1'b1;
        else
          load_s1 = 1'b0;
      end // always @ *

      assign load_s1_from_s2 = (state == TWO);
                       
      // State Machine for handling output signals
      always @(posedge ACLK) begin
        if (ARESET) begin
          s_ready_i <= 1'b0;
          state <= ZERO;
        end else if (areset_d1) begin
          s_ready_i <= 1'b1;
        end else begin
          case (state)
            // No transaction stored locally
            ZERO: if (S_VALID) state <= ONE; // Got one so move to ONE

            // One transaction stored locally
            ONE: begin
              if (M_READY & ~S_VALID) state <= ZERO; // Read out one so move to ZERO
              if (~M_READY & S_VALID) begin
                state <= TWO;  // Got another one so move to TWO
                s_ready_i <= 1'b0;
              end
            end

            // TWO transaction stored locally
            TWO: if (M_READY) begin
              state <= ONE; // Read out one so move to ONE
              s_ready_i <= 1'b1;
            end
          endcase // case (state)
        end
      end // always @ (posedge ACLK)
      
      assign m_valid_i = state[0];

    end // if (C_REG_CONFIG == 1)
  ////////////////////////////////////////////////////////////////////
  //
  // 1-stage pipeline register with bubble cycle, both FWD and REV pipelining
  // Operates same as 1-deep FIFO
  //
  ////////////////////////////////////////////////////////////////////
    else if (C_REG_CONFIG == 32'h00000001)
    begin
      reg [C_DATA_WIDTH-1:0] storage_data1 = 0;
      reg                    s_ready_i; //local signal of output
      reg                    m_valid_i; //local signal of output

      // assign local signal to its output signal
      assign S_READY = s_ready_i;
      assign M_VALID = m_valid_i;

      reg  areset_d1; // Reset delay register
      always @(posedge ACLK) begin
        areset_d1 <= ARESET;
      end
      
      // Load storage1 with slave side data
      always @(posedge ACLK) 
      begin
        if (ARESET) begin
          s_ready_i <= 1'b0;
          m_valid_i <= 1'b0;
        end else if (areset_d1) begin
          s_ready_i <= 1'b1;
        end else if (m_valid_i & M_READY) begin
          s_ready_i <= 1'b1;
          m_valid_i <= 1'b0;
        end else if (S_VALID & s_ready_i) begin
          s_ready_i <= 1'b0;
          m_valid_i <= 1'b1;
        end
        if (~m_valid_i) begin
          storage_data1 <= S_PAYLOAD_DATA;        
        end
      end
      assign M_PAYLOAD_DATA = storage_data1;
    end // if (C_REG_CONFIG == 7)
    
    else begin : default_case
      // Passthrough
      assign M_PAYLOAD_DATA = S_PAYLOAD_DATA;
      assign M_VALID        = S_VALID;
      assign S_READY        = M_READY;      
    end

  endgenerate
endmodule // reg_slice
