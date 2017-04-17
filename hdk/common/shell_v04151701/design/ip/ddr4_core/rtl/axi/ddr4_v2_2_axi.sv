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
//  /   /         Filename           : ddr4_v2_2_0_axi.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 17 2014
//  \___\/\___\
//
//Device: UltraScale
//Design Name: AXI Upsizer
//Purpose:
//
// Description: 
// To handle AXI4 transactions to external memory on Virtex-6 architectures 
// requires a bridge to convert the AXI4 transactions to the memory
// controller(MC) user interface.  The MC user interface has bidirectional 
// data path and supports data width of 256/128/64/32 bits.  
// The bridge is designed to allow AXI4 IP masters to communicate with 
// the MC user interface. 
//
//
// Specifications:
// AXI4 Slave Side:
// Configurable data width of 32, 64, 128, 256
// Read acceptance depth is:
// Write acceptance depth is:
//
//Reference:
//Revision History:
//*****************************************************************************
`timescale 1ps/1ps
`default_nettype none

module ddr4_v2_2_0_axi #
(
///////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
///////////////////////////////////////////////////////////////////////////////
                    // FPGA Family. Current version: virtex6.
  parameter         C_FAMILY                        = "rtl", 
                    // Width of all master and slave ID signals.
                    // Range: >= 1.
  parameter integer C_S_AXI_ID_WIDTH                = 4, 
                    // Width of S_AXI_AWADDR, S_AXI_ARADDR, M_AXI_AWADDR and 
                    // M_AXI_ARADDR for all SI/MI slots.
                    // Range: 32.
  parameter integer C_S_AXI_ADDR_WIDTH              = 30, 
                    // Width of WDATA and RDATA on SI slot.
                    // Must be <= C_MC_DATA_WIDTH
                    // Range: 32, 64, 128, 256.
  parameter integer C_S_AXI_DATA_WIDTH              = 32, 
                    // Memory controller address width, range 28-32
  parameter integer C_MC_ADDR_WIDTH                 = 30, 
                    // Width of wr_data and rd_data.
                    // Range: 32, 64, 128, 256.
  parameter integer C_MC_DATA_WIDTH                 = 32,
                    // Memory controller burst mode,
                    // values "8", "4" & "OTF"
  parameter         C_MC_BURST_MODE      = "8",
                    // Number of memory clocks per fabric clock
                    // = 2 for DDR2 or low frequency designs
                    // = 4 for DDR3 or high frequency designs 
  parameter         C_MC_nCK_PER_CLK     = 2,
                    // Indicates whether to instatiate upsizer
                    // Range: 0, 1
  parameter integer C_S_AXI_SUPPORTS_NARROW_BURST   = 1, 
                    // C_S_AXI_REG_EN0[00] = Reserved
                    // C_S_AXI_REG_EN0[04] = AW CHANNEL REGISTER SLICE 
                    // C_S_AXI_REG_EN0[05] =  W CHANNEL REGISTER SLICE
                    // C_S_AXI_REG_EN0[06] =  B CHANNEL REGISTER SLICE
                    // C_S_AXI_REG_EN0[07] =  R CHANNEL REGISTER SLICE
                    // C_S_AXI_REG_EN0[08] = AW CHANNEL UPSIZER REGISTER SLICE 
                    // C_S_AXI_REG_EN0[09] =  W CHANNEL UPSIZER REGISTER SLICE
                    // C_S_AXI_REG_EN0[10] = AR CHANNEL UPSIZER REGISTER SLICE
                    // C_S_AXI_REG_EN0[11] =  R CHANNEL UPSIZER REGISTER SLICE
  parameter         C_S_AXI_REG_EN0                 = 20'h00000, 
                    // Instatiates register slices after the upsizer.
                    // The type of register is specified for each channel
                    // in a vector. 4 bits per channel are used.  
                    // C_S_AXI_REG_EN1[03:00] = AW CHANNEL REGISTER SLICE
                    // C_S_AXI_REG_EN1[07:04] =  W CHANNEL REGISTER SLICE
                    // C_S_AXI_REG_EN1[11:08] =  B CHANNEL REGISTER SLICE
                    // C_S_AXI_REG_EN1[15:12] = AR CHANNEL REGISTER SLICE
                    // C_S_AXI_REG_EN1[20:16] =  R CHANNEL REGISTER SLICE
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
                    //   7 => ADDRESS   = Optimized for address channel
                    //                                     A  A
                    //                                    RRBWW 
  parameter         C_S_AXI_REG_EN1                 = 20'h00000,
  parameter         C_RD_WR_ARB_ALGORITHM            = "RD_PRI_REG",
                    // Indicates the Arbitration
                    // Allowed values - "TDM", "ROUND_ROBIN",
                    // "RD_PRI_REG", "RD_PRI_REG_STARVE_LIMIT"
  parameter         C_ECC                           = "OFF"
                    // Output RMW if ECC is on.
)
(
///////////////////////////////////////////////////////////////////////////////
// Port Declarations     
///////////////////////////////////////////////////////////////////////////////
  // AXI Slave Interface
  // Slave Interface System Signals           
  input  wire                               aclk              , 
  input  wire                               aresetn           , 
  // Slave Interface Write Address Ports
  input  wire [C_S_AXI_ID_WIDTH-1:0]        s_axi_awid        , 
  input  wire [C_S_AXI_ADDR_WIDTH-1:0]      s_axi_awaddr      , 
  input  wire [7:0]                         s_axi_awlen       , 
  input  wire [2:0]                         s_axi_awsize      , 
  input  wire [1:0]                         s_axi_awburst     , 
  input  wire [0:0]                         s_axi_awlock      , 
  input  wire [3:0]                         s_axi_awcache     , 
  input  wire [2:0]                         s_axi_awprot      , 
  input  wire [3:0]                         s_axi_awqos       , 
  input  wire                               s_axi_awvalid     , 
  output wire                               s_axi_awready     , 
  // Slave Interface Write Data Ports
  input  wire [C_S_AXI_DATA_WIDTH-1:0]      s_axi_wdata       , 
  input  wire [C_S_AXI_DATA_WIDTH/8-1:0]    s_axi_wstrb       , 
  input  wire                               s_axi_wlast       , 
  input  wire                               s_axi_wvalid      , 
  output wire                               s_axi_wready      , 
  // Slave Interface Write Response Ports
  output wire [C_S_AXI_ID_WIDTH-1:0]        s_axi_bid         , 
  output wire [1:0]                         s_axi_bresp       , 
  output wire                               s_axi_bvalid      , 
  input  wire                               s_axi_bready      , 
  // Slave Interface Read Address Ports
  input  wire [C_S_AXI_ID_WIDTH-1:0]        s_axi_arid        , 
  input  wire [C_S_AXI_ADDR_WIDTH-1:0]      s_axi_araddr      , 
  input  wire [7:0]                         s_axi_arlen       , 
  input  wire [2:0]                         s_axi_arsize      , 
  input  wire [1:0]                         s_axi_arburst     , 
  input  wire [0:0]                         s_axi_arlock      , 
  input  wire [3:0]                         s_axi_arcache     , 
  input  wire [2:0]                         s_axi_arprot      , 
  input  wire [3:0]                         s_axi_arqos       , 
  input  wire                               s_axi_arvalid     , 
  output wire                               s_axi_arready     , 
  // Slave Interface Read Data Ports
  output wire [C_S_AXI_ID_WIDTH-1:0]        s_axi_rid         , 
  output wire [C_S_AXI_DATA_WIDTH-1:0]      s_axi_rdata       , 
  output wire [1:0]                         s_axi_rresp       , 
  output wire                               s_axi_rlast       , 
  output wire                               s_axi_rvalid      , 
  input  wire                               s_axi_rready      , 

  // MC Master Interface
  //CMD PORT
  output wire                               mc_app_en         , 
  output wire [2:0]                         mc_app_cmd        , 
  output wire                               mc_app_sz         , 
  output wire [C_MC_ADDR_WIDTH-1:0]         mc_app_addr       ,    
  output wire                               mc_app_hi_pri     , 
  output wire                               mc_app_autoprecharge, 
  input  wire                               mc_app_rdy        ,
  input  wire                               mc_init_complete  ,
                                                
  //DATA PORT
  output wire                               mc_app_wdf_wren   , 
  output wire [C_MC_DATA_WIDTH/8-1:0]       mc_app_wdf_mask   , 
  output wire [C_MC_DATA_WIDTH-1:0]         mc_app_wdf_data   ,
  output wire                               mc_app_wdf_end    ,                      
  input  wire                               mc_app_wdf_rdy    , 
                                              
  input  wire                               mc_app_rd_valid   , 
  input  wire [C_MC_DATA_WIDTH-1:0]         mc_app_rd_data    ,
  input  wire                               mc_app_rd_end     ,
  input  wire [2*C_MC_nCK_PER_CLK-1:0]      mc_app_ecc_multiple_err
);

////////////////////////////////////////////////////////////////////////////////
// Local parameters
////////////////////////////////////////////////////////////////////////////////
localparam integer P_AXSIZE = (C_MC_DATA_WIDTH == 32) ? 3'd2 :
                              (C_MC_DATA_WIDTH == 64) ? 3'd3 : 
                              (C_MC_DATA_WIDTH == 128)? 3'd4 :
                              (C_MC_DATA_WIDTH == 256)? 3'd5 :
                              (C_MC_DATA_WIDTH == 512)? 3'd6 : 3'd7;
   
// C_D?_REG_CONFIG_*:

//   0 => BYPASS    = The channel is just wired through the module.
//   1 => FWD       = The master VALID and payload signals are registrated. 
//   2 => REV       = The slave ready signal is registrated
//   3 => FWD_REV   = Both FWD and REV
//   4 => SLAVE_FWD = All slave side signals and master VALID and payload are registrated.
//   5 => SLAVE_RDY = All slave side signals and master READY are registrated.
//   6 => INPUTS    = Slave and Master side inputs are registrated.
localparam integer P_D1_REG_CONFIG_AW = 0;
localparam integer P_D1_REG_CONFIG_W  = 0;
localparam integer P_D1_REG_CONFIG_B  = 0;
localparam integer P_D1_REG_CONFIG_AR = 0;
localparam integer P_D1_REG_CONFIG_R  = 0;

// Upsizer
localparam integer P_USE_UPSIZER = ( C_S_AXI_DATA_WIDTH < C_MC_DATA_WIDTH) ? 1'b1
                                   : C_S_AXI_SUPPORTS_NARROW_BURST;

localparam integer P_D2_REG_CONFIG_AW = P_USE_UPSIZER ? 1 : C_S_AXI_REG_EN0[8];
localparam integer P_D2_REG_CONFIG_W  = C_S_AXI_REG_EN0[9];
localparam integer P_D2_REG_CONFIG_AR = P_USE_UPSIZER ? 1 : C_S_AXI_REG_EN0[10];
localparam integer P_D2_REG_CONFIG_R  = P_USE_UPSIZER ? 1 : C_S_AXI_REG_EN0[11];


// localparam integer P_D3_REG_CONFIG_AW = (C_S_AXI_DATA_WIDTH < C_MC_DATA_WIDTH)? 
//                                         (C_S_AXI_REG_EN0[4] ? 1 : C_S_AXI_REG_EN1[ 0 +: 4]) : 1;
// localparam integer P_D3_REG_CONFIG_W  = C_S_AXI_REG_EN0[5] ? 2 : C_S_AXI_REG_EN1[ 4 +: 4];
// localparam integer P_D3_REG_CONFIG_B  = C_S_AXI_REG_EN0[6] ? 7 : C_S_AXI_REG_EN1[ 8 +: 4];
// // AR channel must always have a register slice.
// localparam integer P_D3_REG_CONFIG_AR = (C_S_AXI_DATA_WIDTH < C_MC_DATA_WIDTH)? 0 : 1;
// localparam integer P_D3_REG_CONFIG_R  = C_S_AXI_REG_EN0[7] ? 6 : C_S_AXI_REG_EN1[16 +: 4];

localparam integer P_D3_REG_CONFIG_AW = 0;
localparam integer P_D3_REG_CONFIG_W  = 0;
localparam integer P_D3_REG_CONFIG_B  = 0;
localparam integer P_D3_REG_CONFIG_AR = 0;
localparam integer P_D3_REG_CONFIG_R  = 0;


localparam integer P_UPSIZER_PACKING_LEVEL = 2;
localparam integer P_SUPPORTS_USER_SIGNALS = 0;
// Set this parameter to 1 if data can be returned out of order
localparam integer P_SINGLE_THREAD = 0;
   

// BURST LENGTH
// In 4:1 mode the only burst mode that is supported is BL8.
// The BL8 in 4:1 mode will be treated as BL4 by the shim.
// In 2:1 mode both the burst modes BL4 & BL8 are supported. 

localparam integer C_MC_BURST_LEN = (C_MC_nCK_PER_CLK == 4)  ? 1:
                                    (C_MC_BURST_MODE == "4") ? 1 : 2;

////////////////////////////////////////////////////////////////////////////////
// Wires/Reg declarations
////////////////////////////////////////////////////////////////////////////////

// AXI Slave signals from Reg Slice, Upsizer, at MC data width, internal signals


////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
///////////////////////////////////////////////////////////////////////////////

// First reg slice slave side output/inputs
wire  [C_S_AXI_ID_WIDTH-1:0]   awid_d1          ;
wire  [C_S_AXI_ADDR_WIDTH-1:0] awaddr_d1        ;
wire  [7:0]                    awlen_d1         ;
wire  [2:0]                    awsize_d1        ;
wire  [1:0]                    awburst_d1       ;
wire  [1:0]                    awlock_d1        ;
wire  [3:0]                    awcache_d1       ;
wire  [2:0]                    awprot_d1        ;
wire  [3:0]                    awqos_d1         ;
wire                           awvalid_d1       ;
wire                           awready_d1       ;
wire  [C_S_AXI_DATA_WIDTH-1:0] wdata_d1         ;
wire  [C_S_AXI_DATA_WIDTH/8-1:0] wstrb_d1       ;
wire                           wlast_d1         ;
wire                           wvalid_d1        ;
wire                           wready_d1        ;
wire  [C_S_AXI_ID_WIDTH-1:0]   bid_d1           ;
wire  [1:0]                    bresp_d1         ;
wire                           bvalid_d1        ;
wire                           bready_d1        ;
wire  [C_S_AXI_ID_WIDTH-1:0]   arid_d1          ;
wire  [C_S_AXI_ADDR_WIDTH-1:0] araddr_d1        ;
wire  [7:0]                    arlen_d1         ;
wire  [2:0]                    arsize_d1        ;
wire  [1:0]                    arburst_d1       ;
wire  [1:0]                    arlock_d1        ;
wire  [3:0]                    arcache_d1       ;
wire  [2:0]                    arprot_d1        ;
wire  [3:0]                    arqos_d1         ;
wire                           arvalid_d1       ;
wire                           arready_d1       ;
wire  [C_S_AXI_ID_WIDTH-1:0]   rid_d1           ;
wire  [C_S_AXI_DATA_WIDTH-1:0] rdata_d1         ;
wire  [1:0]                    rresp_d1         ;
wire                           rlast_d1         ;
wire                           rvalid_d1        ;
wire                           rready_d1        ;
// Upsizer slave side outputs/inputs
wire  [C_S_AXI_ID_WIDTH-1:0]   awid_d2          ;
wire  [C_S_AXI_ADDR_WIDTH-1:0] awaddr_d2        ;
wire  [7:0]                    awlen_d2         ;
wire  [2:0]                    awsize_d2        ;
wire  [1:0]                    awburst_d2       ;
wire  [1:0]                    awlock_d2        ;
wire  [3:0]                    awcache_d2       ;
wire  [2:0]                    awprot_d2        ;
wire  [3:0]                    awqos_d2         ;
wire                           awvalid_d2       ;
wire                           awready_d2       ;
wire  [C_MC_DATA_WIDTH-1:0]    wdata_d2         ;
wire  [C_MC_DATA_WIDTH/8-1:0]  wstrb_d2         ;
wire                           wlast_d2         ;
wire                           wvalid_d2        ;
wire                           wready_d2        ;
wire  [C_S_AXI_ID_WIDTH-1:0]   bid_d2           ;
wire  [1:0]                    bresp_d2         ;
wire                           bvalid_d2        ;
wire                           bready_d2        ;
wire  [C_S_AXI_ID_WIDTH-1:0]   arid_d2          ;
wire  [C_S_AXI_ADDR_WIDTH-1:0] araddr_d2        ;
wire  [7:0]                    arlen_d2         ;
wire  [2:0]                    arsize_d2        ;
wire  [1:0]                    arburst_d2       ;
wire  [1:0]                    arlock_d2        ;
wire  [3:0]                    arcache_d2       ;
wire  [2:0]                    arprot_d2        ;
wire  [3:0]                    arqos_d2         ;
wire                           arvalid_d2       ;
wire                           arready_d2       ;
wire  [C_S_AXI_ID_WIDTH-1:0]   rid_d2           ;
wire  [C_MC_DATA_WIDTH-1:0]    rdata_d2         ;
wire  [1:0]                    rresp_d2         ;
wire                           rlast_d2         ;
wire                           rvalid_d2        ;
wire                           rready_d2        ;
// Registe Slice 2 slave side outputs/inputs
wire  [C_S_AXI_ID_WIDTH-1:0]   awid_d3          ;
wire  [C_S_AXI_ADDR_WIDTH-1:0] awaddr_d3        ;
wire  [7:0]                    awlen_d3         ;
// AxSIZE hardcoded with static value
// wire  [2:0]                    awsize_d3        ;
wire  [1:0]                    awburst_d3       ;
wire  [1:0]                    awlock_d3        ;
wire  [3:0]                    awcache_d3       ;
wire  [2:0]                    awprot_d3        ;
wire  [3:0]                    awqos_d3         ;
wire                           awvalid_d3       ;
wire                           awready_d3       ;
wire  [C_MC_DATA_WIDTH-1:0]    wdata_d3         ;
wire  [C_MC_DATA_WIDTH/8-1:0]  wstrb_d3         ;
wire                           wlast_d3         ;
wire                           wvalid_d3        ;
wire                           wready_d3        ;
wire  [C_S_AXI_ID_WIDTH-1:0]   bid_d3           ;
wire  [1:0]                    bresp_d3         ;
wire                           bvalid_d3        ;
wire                           bready_d3        ;
wire  [C_S_AXI_ID_WIDTH-1:0]   arid_d3          ;
wire  [C_S_AXI_ADDR_WIDTH-1:0] araddr_d3        ;
wire  [7:0]                    arlen_d3         ;
// AxSIZE hardcoded with static value
// wire  [2:0]                    arsize_d3        ;
wire  [1:0]                    arburst_d3       ;
wire  [1:0]                    arlock_d3        ;
wire  [3:0]                    arcache_d3       ;
wire  [2:0]                    arprot_d3        ;
wire  [3:0]                    arqos_d3         ;
wire                           arvalid_d3       ;
wire                           arready_d3       ;
wire  [C_S_AXI_ID_WIDTH-1:0]   rid_d3           ;
wire  [C_MC_DATA_WIDTH-1:0]    rdata_d3         ;
wire  [1:0]                    rresp_d3         ;
wire                           rlast_d3         ;
wire                           rvalid_d3        ;
wire                           rready_d3        ;

// AW/AR module outputs to arbiter.
wire                           wr_cmd_en        ;
wire                           wr_cmd_en_last   ;
wire  [2:0]                    wr_cmd_instr     ;
wire  [C_MC_ADDR_WIDTH-1:0]    wr_cmd_byte_addr ;
wire                           wr_cmd_full      ;
wire                           rd_cmd_en        ;
wire                           rd_cmd_en_last   ;
wire  [2:0]                    rd_cmd_instr     ;
wire  [C_MC_ADDR_WIDTH-1:0]    rd_cmd_byte_addr ;
wire                           rd_cmd_full      ;
wire                           aresetn_int      ;

wire                           cmd_wr_bytes;

reg                            areset_d1;
reg                            mc_init_complete_r;

////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
///////////////////////////////////////////////////////////////////////////////
assign aresetn_int = aresetn & mc_init_complete_r;

always @(posedge aclk)
  areset_d1 <= ~aresetn_int;

always @(posedge aclk)
  mc_init_complete_r <= mc_init_complete ;

ddr4_v2_2_0_axi_register_slice #
(
  .C_FAMILY                    ( C_FAMILY                ) ,
  .C_AXI_ID_WIDTH              ( C_S_AXI_ID_WIDTH        ) ,
  .C_AXI_ADDR_WIDTH            ( C_S_AXI_ADDR_WIDTH      ) ,
  .C_AXI_DATA_WIDTH            ( C_S_AXI_DATA_WIDTH      ) ,
  .C_AXI_SUPPORTS_USER_SIGNALS ( P_SUPPORTS_USER_SIGNALS ) ,
  .C_AXI_AWUSER_WIDTH          ( 1                       ) ,
  .C_AXI_ARUSER_WIDTH          ( 1                       ) ,
  .C_AXI_WUSER_WIDTH           ( 1                       ) ,
  .C_AXI_RUSER_WIDTH           ( 1                       ) ,
  .C_AXI_BUSER_WIDTH           ( 1                       ) ,
  .C_REG_CONFIG_AW             ( P_D1_REG_CONFIG_AW      ) ,
  .C_REG_CONFIG_W              ( P_D1_REG_CONFIG_W       ) ,
  .C_REG_CONFIG_B              ( P_D1_REG_CONFIG_B       ) ,
  .C_REG_CONFIG_AR             ( P_D1_REG_CONFIG_AR      ) ,
  .C_REG_CONFIG_R              ( P_D1_REG_CONFIG_R       ) 
)
axi_register_slice_d1
(
  .ACLK          ( aclk          ) ,
  .ARESETN       ( aresetn_int   ) ,
  .S_AXI_AWID    ( s_axi_awid    ) ,
  .S_AXI_AWADDR  ( s_axi_awaddr  ) ,
  .S_AXI_AWLEN   ( s_axi_awlen   ) ,
  .S_AXI_AWSIZE  ( s_axi_awsize  ) ,
  .S_AXI_AWBURST ( s_axi_awburst ) ,
  .S_AXI_AWLOCK  ( {1'b0, s_axi_awlock}) ,
  .S_AXI_AWCACHE ( s_axi_awcache ) ,
  .S_AXI_AWPROT  ( s_axi_awprot  ) ,
  .S_AXI_AWREGION( 4'b0          ) ,
  .S_AXI_AWQOS   ( s_axi_awqos   ) ,
  .S_AXI_AWUSER  ( 1'b0          ) ,
  .S_AXI_AWVALID ( s_axi_awvalid ) ,
  .S_AXI_AWREADY ( s_axi_awready ) ,
  .S_AXI_WDATA   ( s_axi_wdata   ) ,
  .S_AXI_WID     ( {C_S_AXI_ID_WIDTH{1'b0}} ) ,
  .S_AXI_WSTRB   ( s_axi_wstrb   ) ,
  .S_AXI_WLAST   ( s_axi_wlast   ) ,
  .S_AXI_WUSER   ( 1'b0          ) ,
  .S_AXI_WVALID  ( s_axi_wvalid  ) ,
  .S_AXI_WREADY  ( s_axi_wready  ) ,
  .S_AXI_BID     ( s_axi_bid     ) ,
  .S_AXI_BRESP   ( s_axi_bresp   ) ,
  .S_AXI_BUSER   (               ) ,
  .S_AXI_BVALID  ( s_axi_bvalid  ) ,
  .S_AXI_BREADY  ( s_axi_bready  ) ,
  .S_AXI_ARID    ( s_axi_arid    ) ,
  .S_AXI_ARADDR  ( s_axi_araddr  ) ,
  .S_AXI_ARLEN   ( s_axi_arlen   ) ,
  .S_AXI_ARSIZE  ( s_axi_arsize  ) ,
  .S_AXI_ARBURST ( s_axi_arburst ) ,
  .S_AXI_ARLOCK  ( {1'b0, s_axi_arlock}) ,
  .S_AXI_ARCACHE ( s_axi_arcache ) ,
  .S_AXI_ARPROT  ( s_axi_arprot  ) ,
  .S_AXI_ARREGION( 4'b0          ) ,
  .S_AXI_ARQOS   ( s_axi_arqos   ) ,
  .S_AXI_ARUSER  ( 1'b0          ) ,
  .S_AXI_ARVALID ( s_axi_arvalid ) ,
  .S_AXI_ARREADY ( s_axi_arready ) ,
  .S_AXI_RID     ( s_axi_rid     ) ,
  .S_AXI_RDATA   ( s_axi_rdata   ) ,
  .S_AXI_RRESP   ( s_axi_rresp   ) ,
  .S_AXI_RLAST   ( s_axi_rlast   ) ,
  .S_AXI_RUSER   (               ) ,
  .S_AXI_RVALID  ( s_axi_rvalid  ) ,
  .S_AXI_RREADY  ( s_axi_rready  ) ,
  .M_AXI_AWID    ( awid_d1       ) ,
  .M_AXI_AWADDR  ( awaddr_d1     ) ,
  .M_AXI_AWLEN   ( awlen_d1      ) ,
  .M_AXI_AWSIZE  ( awsize_d1     ) ,
  .M_AXI_AWBURST ( awburst_d1    ) ,
  .M_AXI_AWLOCK  ( awlock_d1     ) ,
  .M_AXI_AWCACHE ( awcache_d1    ) ,
  .M_AXI_AWREGION(               ) ,
  .M_AXI_AWPROT  ( awprot_d1     ) ,
  .M_AXI_AWQOS   ( awqos_d1      ) ,
  .M_AXI_AWUSER  (               ) ,
  .M_AXI_AWVALID ( awvalid_d1    ) ,
  .M_AXI_AWREADY ( awready_d1    ) ,
  .M_AXI_WID     (               ) ,
  .M_AXI_WDATA   ( wdata_d1      ) ,
  .M_AXI_WSTRB   ( wstrb_d1      ) ,
  .M_AXI_WLAST   ( wlast_d1      ) ,
  .M_AXI_WUSER   (               ) ,
  .M_AXI_WVALID  ( wvalid_d1     ) ,
  .M_AXI_WREADY  ( wready_d1     ) ,
  .M_AXI_BID     ( bid_d1        ) ,
  .M_AXI_BRESP   ( bresp_d1      ) ,
  .M_AXI_BUSER   ( 1'b0          ) ,
  .M_AXI_BVALID  ( bvalid_d1     ) ,
  .M_AXI_BREADY  ( bready_d1     ) ,
  .M_AXI_ARID    ( arid_d1       ) ,
  .M_AXI_ARADDR  ( araddr_d1     ) ,
  .M_AXI_ARLEN   ( arlen_d1      ) ,
  .M_AXI_ARSIZE  ( arsize_d1     ) ,
  .M_AXI_ARBURST ( arburst_d1    ) ,
  .M_AXI_ARLOCK  ( arlock_d1     ) ,
  .M_AXI_ARCACHE ( arcache_d1    ) ,
  .M_AXI_ARPROT  ( arprot_d1     ) ,
  .M_AXI_ARREGION(               ) ,
  .M_AXI_ARQOS   ( arqos_d1      ) ,
  .M_AXI_ARUSER  (               ) ,
  .M_AXI_ARVALID ( arvalid_d1    ) ,
  .M_AXI_ARREADY ( arready_d1    ) ,
  .M_AXI_RID     ( rid_d1        ) ,
  .M_AXI_RDATA   ( rdata_d1      ) ,
  .M_AXI_RRESP   ( rresp_d1      ) ,
  .M_AXI_RLAST   ( rlast_d1      ) ,
  .M_AXI_RUSER   ( 1'b0          ) ,
  .M_AXI_RVALID  ( rvalid_d1     ) ,
  .M_AXI_RREADY  ( rready_d1     ) 
);

generate 
  if (P_USE_UPSIZER) begin : USE_UPSIZER
    ddr4_v2_2_0_axi_upsizer #
      (
      .C_FAMILY                    ( C_FAMILY                ) ,
      .C_AXI_ID_WIDTH              ( C_S_AXI_ID_WIDTH        ) ,
      .C_AXI_ADDR_WIDTH            ( C_S_AXI_ADDR_WIDTH      ) ,
      .C_S_AXI_DATA_WIDTH          ( C_S_AXI_DATA_WIDTH      ) ,
      .C_M_AXI_DATA_WIDTH          ( C_MC_DATA_WIDTH         ) ,
      .C_M_AXI_AW_REGISTER         ( P_D2_REG_CONFIG_AW      ) ,
      .C_M_AXI_W_REGISTER          ( P_D2_REG_CONFIG_W       ) ,
      .C_M_AXI_AR_REGISTER         ( P_D2_REG_CONFIG_AR      ) ,
      .C_S_AXI_R_REGISTER          ( P_D2_REG_CONFIG_R       ) ,
      .C_AXI_SUPPORTS_USER_SIGNALS ( P_SUPPORTS_USER_SIGNALS ) ,
      .C_AXI_AWUSER_WIDTH          ( 1                       ) ,
      .C_AXI_ARUSER_WIDTH          ( 1                       ) ,
      .C_AXI_WUSER_WIDTH           ( 1                       ) ,
      .C_AXI_RUSER_WIDTH           ( 1                       ) ,
      .C_AXI_BUSER_WIDTH           ( 1                       ) ,
      .C_AXI_SUPPORTS_WRITE        ( 1                       ) ,
      .C_AXI_SUPPORTS_READ         ( 1                       ) ,
      .C_PACKING_LEVEL             ( P_UPSIZER_PACKING_LEVEL ) ,
      .C_SUPPORT_BURSTS            ( 1                       ) ,
      .C_SINGLE_THREAD             ( P_SINGLE_THREAD         ) 
    )
    upsizer_d2
    (
      .ACLK          ( aclk          ) ,
      .ARESETN       ( aresetn_int   ) ,
      .S_AXI_AWID    ( awid_d1       ) ,
      .S_AXI_AWADDR  ( awaddr_d1     ) ,
      .S_AXI_AWLEN   ( awlen_d1      ) ,
      .S_AXI_AWSIZE  ( awsize_d1     ) ,
      .S_AXI_AWBURST ( awburst_d1    ) ,
      .S_AXI_AWLOCK  ( awlock_d1     ) ,
      .S_AXI_AWCACHE ( awcache_d1    ) ,
      .S_AXI_AWPROT  ( awprot_d1     ) ,
      .S_AXI_AWREGION( 4'b0          ) ,
      .S_AXI_AWQOS   ( awqos_d1      ) ,
      .S_AXI_AWUSER  ( 1'b0          ) ,
      .S_AXI_AWVALID ( awvalid_d1    ) ,
      .S_AXI_AWREADY ( awready_d1    ) ,
      .S_AXI_WDATA   ( wdata_d1      ) ,
      .S_AXI_WSTRB   ( wstrb_d1      ) ,
      .S_AXI_WLAST   ( wlast_d1      ) ,
      .S_AXI_WUSER   ( 1'b0          ) ,
      .S_AXI_WVALID  ( wvalid_d1     ) ,
      .S_AXI_WREADY  ( wready_d1     ) ,
      .S_AXI_BID     ( bid_d1        ) ,
      .S_AXI_BRESP   ( bresp_d1      ) ,
      .S_AXI_BUSER   (               ) ,
      .S_AXI_BVALID  ( bvalid_d1     ) ,
      .S_AXI_BREADY  ( bready_d1     ) ,
      .S_AXI_ARID    ( arid_d1       ) ,
      .S_AXI_ARADDR  ( araddr_d1     ) ,
      .S_AXI_ARLEN   ( arlen_d1      ) ,
      .S_AXI_ARSIZE  ( arsize_d1     ) ,
      .S_AXI_ARBURST ( arburst_d1    ) ,
      .S_AXI_ARLOCK  ( arlock_d1     ) ,
      .S_AXI_ARCACHE ( arcache_d1    ) ,
      .S_AXI_ARPROT  ( arprot_d1     ) ,
      .S_AXI_ARREGION( 4'b0          ) ,
      .S_AXI_ARQOS   ( arqos_d1      ) ,
      .S_AXI_ARUSER  ( 1'b0          ) ,
      .S_AXI_ARVALID ( arvalid_d1    ) ,
      .S_AXI_ARREADY ( arready_d1    ) ,
      .S_AXI_RID     ( rid_d1        ) ,
      .S_AXI_RDATA   ( rdata_d1      ) ,
      .S_AXI_RRESP   ( rresp_d1      ) ,
      .S_AXI_RLAST   ( rlast_d1      ) ,
      .S_AXI_RUSER   (               ) ,
      .S_AXI_RVALID  ( rvalid_d1     ) ,
      .S_AXI_RREADY  ( rready_d1     ) ,
      .M_AXI_AWID    ( awid_d2       ) ,
      .M_AXI_AWADDR  ( awaddr_d2     ) ,
      .M_AXI_AWLEN   ( awlen_d2      ) ,
      .M_AXI_AWSIZE  ( awsize_d2     ) ,
      .M_AXI_AWBURST ( awburst_d2    ) ,
      .M_AXI_AWLOCK  ( awlock_d2     ) ,
      .M_AXI_AWCACHE ( awcache_d2    ) ,
      .M_AXI_AWPROT  ( awprot_d2     ) ,
      .M_AXI_AWREGION(               ) ,
      .M_AXI_AWQOS   ( awqos_d2      ) ,
      .M_AXI_AWUSER  (               ) ,
      .M_AXI_AWVALID ( awvalid_d2    ) ,
      .M_AXI_AWREADY ( awready_d2    ) ,
      .M_AXI_WDATA   ( wdata_d2      ) ,
      .M_AXI_WSTRB   ( wstrb_d2      ) ,
      .M_AXI_WLAST   ( wlast_d2      ) ,
      .M_AXI_WUSER   (               ) ,
      .M_AXI_WVALID  ( wvalid_d2     ) ,
      .M_AXI_WREADY  ( wready_d2     ) ,
      .M_AXI_BID     ( bid_d2        ) ,
      .M_AXI_BRESP   ( bresp_d2      ) ,
      .M_AXI_BUSER   ( 1'b0          ) ,
      .M_AXI_BVALID  ( bvalid_d2     ) ,
      .M_AXI_BREADY  ( bready_d2     ) ,
      .M_AXI_ARID    ( arid_d2       ) ,
      .M_AXI_ARADDR  ( araddr_d2     ) ,
      .M_AXI_ARLEN   ( arlen_d2      ) ,
      .M_AXI_ARSIZE  ( arsize_d2     ) ,
      .M_AXI_ARBURST ( arburst_d2    ) ,
      .M_AXI_ARLOCK  ( arlock_d2     ) ,
      .M_AXI_ARCACHE ( arcache_d2    ) ,
      .M_AXI_ARPROT  ( arprot_d2     ) ,
      .M_AXI_ARREGION(               ) ,
      .M_AXI_ARQOS   ( arqos_d2      ) ,
      .M_AXI_ARUSER  (               ) ,
      .M_AXI_ARVALID ( arvalid_d2    ) ,
      .M_AXI_ARREADY ( arready_d2    ) ,
      .M_AXI_RID     ( rid_d2        ) ,
      .M_AXI_RDATA   ( rdata_d2      ) ,
      .M_AXI_RRESP   ( rresp_d2      ) ,
      .M_AXI_RLAST   ( rlast_d2      ) ,
      .M_AXI_RUSER   ( 1'b0          ) ,
      .M_AXI_RVALID  ( rvalid_d2     ) ,
      .M_AXI_RREADY  ( rready_d2     ) 
    );
  end
  else begin : NO_UPSIZER
      assign awid_d2    = awid_d1    ; 
      assign awaddr_d2  = awaddr_d1  ; 
      assign awlen_d2   = awlen_d1   ; 
      assign awsize_d2  = awsize_d1  ; 
      assign awburst_d2 = awburst_d1 ; 
      assign awlock_d2  = awlock_d1  ; 
      assign awcache_d2 = awcache_d1 ; 
      assign awprot_d2  = awprot_d1  ; 
      assign awqos_d2   = awqos_d1   ; 
      assign awvalid_d2 = awvalid_d1 ; 
      assign awready_d1 = awready_d2 ; 
      assign wdata_d2   = wdata_d1   ; 
      assign wstrb_d2   = wstrb_d1   ; 
      assign wlast_d2   = wlast_d1   ; 
      assign wvalid_d2  = wvalid_d1  ; 
      assign wready_d1  = wready_d2  ; 
      assign bid_d1     = bid_d2     ; 
      assign bresp_d1   = bresp_d2   ; 
      assign bvalid_d1  = bvalid_d2  ; 
      assign bready_d2  = bready_d1  ; 
      assign arid_d2    = arid_d1    ; 
      assign araddr_d2  = araddr_d1  ; 
      assign arlen_d2   = arlen_d1   ; 
      assign arsize_d2  = arsize_d1  ; 
      assign arburst_d2 = arburst_d1 ; 
      assign arlock_d2  = arlock_d1  ; 
      assign arcache_d2 = arcache_d1 ; 
      assign arprot_d2  = arprot_d1  ; 
      assign arqos_d2   = arqos_d1   ; 
      assign arvalid_d2 = arvalid_d1 ; 
      assign arready_d1 = arready_d2 ; 
      assign rid_d1     = rid_d2     ; 
      assign rdata_d1   = rdata_d2   ; 
      assign rresp_d1   = rresp_d2   ; 
      assign rlast_d1   = rlast_d2   ; 
      assign rvalid_d1  = rvalid_d2  ; 
      assign rready_d2  = rready_d1  ; 
  end
endgenerate

ddr4_v2_2_0_axi_register_slice #
(
  .C_FAMILY                    ( C_FAMILY                ) ,
  .C_AXI_ID_WIDTH              ( C_S_AXI_ID_WIDTH        ) ,
  .C_AXI_ADDR_WIDTH            ( C_S_AXI_ADDR_WIDTH      ) ,
  .C_AXI_DATA_WIDTH            ( C_MC_DATA_WIDTH         ) ,
  .C_AXI_SUPPORTS_USER_SIGNALS ( P_SUPPORTS_USER_SIGNALS ) ,
  .C_AXI_AWUSER_WIDTH          ( 1                       ) ,
  .C_AXI_ARUSER_WIDTH          ( 1                       ) ,
  .C_AXI_WUSER_WIDTH           ( 1                       ) ,
  .C_AXI_RUSER_WIDTH           ( 1                       ) ,
  .C_AXI_BUSER_WIDTH           ( 1                       ) ,
  .C_REG_CONFIG_AW             ( P_D3_REG_CONFIG_AW      ) ,
  .C_REG_CONFIG_W              ( P_D3_REG_CONFIG_W       ) ,
  .C_REG_CONFIG_B              ( P_D3_REG_CONFIG_B       ) ,
  .C_REG_CONFIG_AR             ( P_D3_REG_CONFIG_AR      ) ,
  .C_REG_CONFIG_R              ( P_D3_REG_CONFIG_R       ) 
)
axi_register_slice_d3
(
  .ACLK          ( aclk          ) ,
  .ARESETN       ( aresetn_int   ) ,
  .S_AXI_AWID    ( awid_d2       ) ,
  .S_AXI_AWADDR  ( awaddr_d2     ) ,
  .S_AXI_AWLEN   ( awlen_d2      ) ,
  .S_AXI_AWSIZE  ( P_AXSIZE[2:0] ) ,
  .S_AXI_AWBURST ( awburst_d2    ) ,
  .S_AXI_AWLOCK  ( awlock_d2     ) ,
  .S_AXI_AWCACHE ( awcache_d2    ) ,
  .S_AXI_AWPROT  ( awprot_d2     ) ,
  .S_AXI_AWREGION( 4'b0          ) ,
  .S_AXI_AWQOS   ( awqos_d2      ) ,
  .S_AXI_AWUSER  ( 1'b0          ) ,
  .S_AXI_AWVALID ( awvalid_d2    ) ,
  .S_AXI_AWREADY ( awready_d2    ) ,
  .S_AXI_WID     ( {C_S_AXI_ID_WIDTH{1'b0}} ) ,
  .S_AXI_WDATA   ( wdata_d2      ) ,
  .S_AXI_WSTRB   ( wstrb_d2      ) ,
  .S_AXI_WLAST   ( wlast_d2      ) ,
  .S_AXI_WUSER   ( 1'b0          ) ,
  .S_AXI_WVALID  ( wvalid_d2     ) ,
  .S_AXI_WREADY  ( wready_d2     ) ,
  .S_AXI_BID     ( bid_d2        ) ,
  .S_AXI_BRESP   ( bresp_d2      ) ,
  .S_AXI_BUSER   (               ) ,
  .S_AXI_BVALID  ( bvalid_d2     ) ,
  .S_AXI_BREADY  ( bready_d2     ) ,
  .S_AXI_ARID    ( arid_d2       ) ,
  .S_AXI_ARADDR  ( araddr_d2     ) ,
  .S_AXI_ARLEN   ( arlen_d2      ) ,
  .S_AXI_ARSIZE  ( P_AXSIZE[2:0] ) ,
  .S_AXI_ARBURST ( arburst_d2    ) ,
  .S_AXI_ARLOCK  ( arlock_d2     ) ,
  .S_AXI_ARCACHE ( arcache_d2    ) ,
  .S_AXI_ARPROT  ( arprot_d2     ) ,
  .S_AXI_ARREGION( 4'b0          ) ,
  .S_AXI_ARQOS   ( arqos_d2      ) ,
  .S_AXI_ARUSER  ( 1'b0          ) ,
  .S_AXI_ARVALID ( arvalid_d2    ) ,
  .S_AXI_ARREADY ( arready_d2    ) ,
  .S_AXI_RID     ( rid_d2        ) ,
  .S_AXI_RDATA   ( rdata_d2      ) ,
  .S_AXI_RRESP   ( rresp_d2      ) ,
  .S_AXI_RLAST   ( rlast_d2      ) ,
  .S_AXI_RUSER   (               ) ,
  .S_AXI_RVALID  ( rvalid_d2     ) ,
  .S_AXI_RREADY  ( rready_d2     ) ,
  .M_AXI_AWID    ( awid_d3       ) ,
  .M_AXI_AWADDR  ( awaddr_d3     ) ,
  .M_AXI_AWLEN   ( awlen_d3      ) ,
// AxSIZE hardcoded with static value
//  .M_AXI_AWSIZE  ( awsize_d3     ) ,
  .M_AXI_AWSIZE  (               ) ,
  .M_AXI_AWBURST ( awburst_d3    ) ,
  .M_AXI_AWLOCK  ( awlock_d3     ) ,
  .M_AXI_AWCACHE ( awcache_d3    ) ,
  .M_AXI_AWPROT  ( awprot_d3     ) ,
  .M_AXI_AWREGION(               ) ,
  .M_AXI_AWQOS   ( awqos_d3      ) ,
  .M_AXI_AWUSER  (               ) ,
  .M_AXI_AWVALID ( awvalid_d3    ) ,
  .M_AXI_AWREADY ( awready_d3    ) ,
  .M_AXI_WID     (               ) ,
  .M_AXI_WDATA   ( wdata_d3      ) ,
  .M_AXI_WSTRB   ( wstrb_d3      ) ,
  .M_AXI_WLAST   ( wlast_d3      ) ,
  .M_AXI_WUSER   (               ) ,
  .M_AXI_WVALID  ( wvalid_d3     ) ,
  .M_AXI_WREADY  ( wready_d3     ) ,
  .M_AXI_BID     ( bid_d3        ) ,
  .M_AXI_BRESP   ( bresp_d3      ) ,
  .M_AXI_BUSER   ( 1'b0          ) ,
  .M_AXI_BVALID  ( bvalid_d3     ) ,
  .M_AXI_BREADY  ( bready_d3     ) ,
  .M_AXI_ARID    ( arid_d3       ) ,
  .M_AXI_ARADDR  ( araddr_d3     ) ,
  .M_AXI_ARLEN   ( arlen_d3      ) ,
// AxSIZE hardcoded with static value
//  .M_AXI_ARSIZE  ( arsize_d3     ) ,
  .M_AXI_ARSIZE  (               ) ,
  .M_AXI_ARBURST ( arburst_d3    ) ,
  .M_AXI_ARLOCK  ( arlock_d3     ) ,
  .M_AXI_ARCACHE ( arcache_d3    ) ,
  .M_AXI_ARPROT  ( arprot_d3     ) ,
  .M_AXI_ARREGION(               ) ,
  .M_AXI_ARQOS   ( arqos_d3      ) ,
  .M_AXI_ARUSER  (               ) ,
  .M_AXI_ARVALID ( arvalid_d3    ) ,
  .M_AXI_ARREADY ( arready_d3    ) ,
  .M_AXI_RID     ( rid_d3        ) ,
  .M_AXI_RDATA   ( rdata_d3      ) ,
  .M_AXI_RRESP   ( rresp_d3      ) ,
  .M_AXI_RLAST   ( rlast_d3      ) ,
  .M_AXI_RUSER   ( 1'b0          ) ,
  .M_AXI_RVALID  ( rvalid_d3     ) ,
  .M_AXI_RREADY  ( rready_d3     ) 
);
 
 
// AW/W/B channel internal communication
wire                                w_ignore_begin;
wire                                w_ignore_end;
wire                                w_cmd_rdy;    
wire                                awvalid_int;    
wire  [3:0]                         awqos_int     ;
wire                                w_data_rdy  ;
wire                                b_push;
wire [C_S_AXI_ID_WIDTH-1:0]         b_awid;
wire                                b_full;
   
ddr4_v2_2_0_axi_aw_channel #
(
  .C_ID_WIDTH                       ( C_S_AXI_ID_WIDTH   ),
  .C_AXI_ADDR_WIDTH                 ( C_S_AXI_ADDR_WIDTH ),
  .C_MC_ADDR_WIDTH                  ( C_MC_ADDR_WIDTH    ),
  .C_DATA_WIDTH                     ( C_MC_DATA_WIDTH    ),
  .C_AXSIZE                         ( P_AXSIZE           ),
  .C_MC_nCK_PER_CLK                 ( C_MC_nCK_PER_CLK   ),
  .C_MC_BURST_LEN                   ( C_MC_BURST_LEN     ),
  .C_ECC                            ( C_ECC              )
)
axi_aw_channel_0
(
  .clk                              ( aclk              ) ,
  .reset                            ( areset_d1         ) ,
  .awid                             ( awid_d3           ) ,
  .awaddr                           ( awaddr_d3         ) ,
  .awlen                            ( awlen_d3          ) ,
  .awsize                           ( P_AXSIZE[2:0]     ) ,
  .awburst                          ( awburst_d3        ) ,
  .awlock                           ( awlock_d3         ) ,
  .awcache                          ( awcache_d3        ) ,
  .awprot                           ( awprot_d3         ) ,
  .awqos                            ( awqos_d3          ) ,
  .awvalid                          ( awvalid_d3        ) ,
  .awready                          ( awready_d3        ) ,
  .cmd_en                           ( wr_cmd_en         ) ,
  .cmd_instr                        ( wr_cmd_instr      ) ,
  .cmd_byte_addr                    ( wr_cmd_byte_addr  ) ,
  .cmd_full                         ( wr_cmd_full       ) ,
  .cmd_en_last                      ( wr_cmd_en_last    ) ,
  .w_ignore_begin                   ( w_ignore_begin    ) ,
  .w_ignore_end                     ( w_ignore_end      ) ,
  .w_cmd_rdy                        ( w_cmd_rdy         ) ,
  .awvalid_int                      ( awvalid_int       ) ,
  .awqos_int                        ( awqos_int         ) ,
  .w_data_rdy                       ( w_data_rdy        ) ,
  .cmd_wr_bytes                     ( cmd_wr_bytes      ) ,
  .b_push                           ( b_push            ) ,
  .b_awid                           ( b_awid            ) ,
  .b_full                           ( b_full            )
);

ddr4_v2_2_0_axi_w_channel #
(
  .C_DATA_WIDTH                     ( C_MC_DATA_WIDTH    ), 
  .C_AXI_ADDR_WIDTH                 ( C_S_AXI_ADDR_WIDTH ),
  .C_MC_BURST_LEN                   ( C_MC_BURST_LEN     ),
  .C_ECC                            ( C_ECC              )
)
axi_w_channel_0
(
  .clk                              ( aclk            ) ,
  .reset                            ( areset_d1       ) ,
  .wdata                            ( wdata_d3        ) ,
  .wstrb                            ( wstrb_d3        ) ,
  .wvalid                           ( wvalid_d3       ) ,
  .wready                           ( wready_d3       ) ,
  .awvalid                          ( awvalid_int     ) ,
  .w_ignore_begin                   ( w_ignore_begin  ) ,
  .w_ignore_end                     ( w_ignore_end    ) ,
  .w_cmd_rdy                        ( w_cmd_rdy       ) ,
  .cmd_wr_bytes                     ( cmd_wr_bytes    ) ,
  .mc_app_wdf_wren                  ( mc_app_wdf_wren ) ,
  .mc_app_wdf_mask                  ( mc_app_wdf_mask ) ,
  .mc_app_wdf_data                  ( mc_app_wdf_data ) ,
  .mc_app_wdf_last                  ( mc_app_wdf_end  ) , 
  .mc_app_wdf_rdy                   ( mc_app_wdf_rdy  ) ,
  .w_data_rdy                       ( w_data_rdy      )
);

ddr4_v2_2_0_axi_b_channel #
(
  .C_ID_WIDTH                       ( C_S_AXI_ID_WIDTH   )
)
axi_b_channel_0
(
  .clk                              ( aclk            ) ,
  .reset                            ( areset_d1       ) ,
  .bid                              ( bid_d3          ) ,
  .bresp                            ( bresp_d3        ) ,
  .bvalid                           ( bvalid_d3       ) ,
  .bready                           ( bready_d3       ) ,
  .b_push                           ( b_push          ) ,
  .b_awid                           ( b_awid          ) ,
  .b_full                           ( b_full          ) ,
  .b_resp_rdy                       ( awready_d3      )  
);
  
  
// AR/R channel communication
wire                                r_push        ; 
wire [C_S_AXI_ID_WIDTH-1:0]         r_arid        ; 
wire                                r_rlast       ; 
wire                                r_data_rdy    ;
wire                                r_ignore_begin;
wire                                r_ignore_end  ;
wire                                arvalid_int   ;
wire  [3:0]                         arqos_int     ;
   
   
   
 


ddr4_v2_2_0_axi_ar_channel #
(
  .C_ID_WIDTH                       ( C_S_AXI_ID_WIDTH   ),
  .C_AXI_ADDR_WIDTH                 ( C_S_AXI_ADDR_WIDTH ),
  .C_MC_ADDR_WIDTH                  ( C_MC_ADDR_WIDTH    ),
  .C_DATA_WIDTH                     ( C_MC_DATA_WIDTH    ),
  .C_AXSIZE                         ( P_AXSIZE           ),
  .C_MC_nCK_PER_CLK                 ( C_MC_nCK_PER_CLK   ),
  .C_MC_BURST_LEN                   ( C_MC_BURST_LEN     )

)
axi_ar_channel_0
(
  .clk                              ( aclk              ) ,
  .reset                            ( areset_d1         ) ,
  .arid                             ( arid_d3           ) ,
  .araddr                           ( araddr_d3         ) ,
  .arlen                            ( arlen_d3          ) ,
  .arsize                           ( P_AXSIZE[2:0]     ) ,
  .arburst                          ( arburst_d3        ) ,
  .arlock                           ( arlock_d3         ) ,
  .arcache                          ( arcache_d3        ) ,
  .arprot                           ( arprot_d3         ) ,
  .arqos                            ( arqos_d3          ) ,
  .arvalid                          ( arvalid_d3        ) ,
  .arready                          ( arready_d3        ) ,
  .cmd_en                           ( rd_cmd_en         ) ,
  .cmd_instr                        ( rd_cmd_instr      ) ,
  .cmd_byte_addr                    ( rd_cmd_byte_addr  ) ,
  .cmd_full                         ( rd_cmd_full       ) ,
  .cmd_en_last                      ( rd_cmd_en_last    ) ,
  .r_push                           ( r_push            ) ,
  .r_arid                           ( r_arid            ) ,
  .r_rlast                          ( r_rlast           ) ,
  .r_data_rdy                       ( r_data_rdy        ) ,
  .r_ignore_begin                   ( r_ignore_begin    ) ,
  .r_ignore_end                     ( r_ignore_end      ) ,
  .arvalid_int                      ( arvalid_int       ) ,
  .arqos_int                        ( arqos_int         ) 
);

ddr4_v2_2_0_axi_r_channel #
(
  .C_ID_WIDTH                       ( C_S_AXI_ID_WIDTH   ), 
  .C_DATA_WIDTH                     ( C_MC_DATA_WIDTH    ),
  .C_AXI_ADDR_WIDTH                 ( C_S_AXI_ADDR_WIDTH ),
  .C_MC_BURST_MODE                  ( C_MC_BURST_MODE    ),
  .C_MC_BURST_LEN                   ( C_MC_BURST_LEN     )
)
axi_r_channel_0
(
  .clk                              ( aclk            ) ,
  .reset                            ( areset_d1       ) ,
  .rid                              ( rid_d3          ) ,
  .rdata                            ( rdata_d3        ) ,
  .rresp                            ( rresp_d3        ) ,
  .rlast                            ( rlast_d3        ) ,
  .rvalid                           ( rvalid_d3       ) ,
  .rready                           ( rready_d3       ) ,
  .mc_app_rd_valid                  ( mc_app_rd_valid ) ,
  .mc_app_rd_data                   ( mc_app_rd_data  ) ,
  .mc_app_rd_last                   ( mc_app_rd_end   ) ,
  .mc_app_ecc_multiple_err          ( |mc_app_ecc_multiple_err ) ,
  .r_push                           ( r_push          ) ,
  .r_data_rdy                       ( r_data_rdy      ) ,
  .r_arid                           ( r_arid          ) ,
  .r_rlast                          ( r_rlast         ) ,
  .r_ignore_begin                   ( r_ignore_begin  ) ,
  .r_ignore_end                     ( r_ignore_end    ) 
);

// Arbiter    
ddr4_v2_2_0_axi_cmd_arbiter #
(
  .C_MC_ADDR_WIDTH           ( C_MC_ADDR_WIDTH  ) ,
  .C_MC_BURST_LEN            ( C_MC_BURST_LEN   ) ,
  .C_RD_WR_ARB_ALGORITHM      ( C_RD_WR_ARB_ALGORITHM ) 
)
axi_cmd_arbiter_0
(
  .clk                       ( aclk              ) ,
  .reset                     ( areset_d1         ) ,
  // Write commands from AXI
  .wr_cmd_en                 ( wr_cmd_en         ) ,
  .wr_cmd_en_last            ( wr_cmd_en_last    ) , 
  .wr_cmd_instr              ( wr_cmd_instr      ) ,
  .wr_cmd_byte_addr          ( wr_cmd_byte_addr  ) ,
  .wr_cmd_full               ( wr_cmd_full       ) ,
  // Read commands from AXI
  .rd_cmd_en                 ( rd_cmd_en         ) ,
  .rd_cmd_en_last            ( rd_cmd_en_last    ) ,
  .rd_cmd_instr              ( rd_cmd_instr      ) ,
  .rd_cmd_byte_addr          ( rd_cmd_byte_addr  ) ,
  .rd_cmd_full               ( rd_cmd_full       ) ,
  // Next Command info
  .arvalid                   ( arvalid_int       ) ,
  .arqos                     ( arqos_int         ) ,
  .awvalid                   ( awvalid_int       ) ,
  .awqos                     ( awqos_int         ) ,
  // To MC
  .mc_app_en                 ( mc_app_en         ) ,
  .mc_app_cmd                ( mc_app_cmd        ) ,
  .mc_app_size               ( mc_app_sz         ) ,
  .mc_app_addr               ( mc_app_addr       ) ,
  .mc_app_hi_pri             ( mc_app_hi_pri     ) , 
  .mc_app_autoprecharge      ( mc_app_autoprecharge) , 
  .mc_app_rdy                ( mc_app_rdy       ) 
);

endmodule

`default_nettype wire

