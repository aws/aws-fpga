// -- (c) Copyright 2013 Xilinx, Inc. All rights reserved. 
// --                                                             
// -- This file contains confidential and proprietary information 
// -- of Xilinx, Inc. and is protected under U.S. and             
// -- international copyright and other intellectual property     
// -- laws.                                                       
// --                                                             
// -- DISCLAIMER                                                  
// -- This disclaimer is not a license and does not grant any     
// -- rights to the materials distributed herewith. Except as     
// -- otherwise provided in a valid license issued to you by      
// -- Xilinx, and to the maximum extent permitted by applicable   
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND     
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES 
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING   
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-      
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and    
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of          
// -- liability) for any loss or damage of any kind or nature     
// -- related to, arising under or in connection with these       
// -- materials, including for any direct, or any indirect,       
// -- special, incidental, or consequential loss or damage        
// -- (including loss of data, profits, goodwill, or any type of  
// -- loss or damage suffered as a result of any action brought   
// -- by a third party) even if such damage or loss was           
// -- reasonably foreseeable or Xilinx had been advised of the    
// -- possibility of the same.                                    
// --                                                             
// -- CRITICAL APPLICATIONS                                       
// -- Xilinx products are not designed or intended to be fail-    
// -- safe, or for use in any application requiring fail-safe     
// -- performance, such as life-support or safety devices or      
// -- systems, Class III medical devices, nuclear facilities,     
// -- applications related to the deployment of airbags, or any   
// -- other applications that could lead to death, personal       
// -- injury, or severe property or environmental damage          
// -- (individually and collectively, "Critical                   
// -- Applications"). Customer assumes the sole risk and          
// -- liability of any use of Xilinx products in Critical         
// -- Applications, subject only to applicable laws and           
// -- regulations governing limitations on product liability.     
// --                                                             
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS    
// -- PART OF THIS FILE AT ALL TIMES.                             
// --  
///////////////////////////////////////////////////////////////////////////////
//
// File name: ddr4_v2_2_0_axi_ctrl_top.v
//
// Description: AXI Lite Controller
//
// Specifications:
//
// Structure:
// axi_ctrl_top
//   axi_ctrl_write
//     axi_ctrl_addr_decode
//   axi_ctrl_read
//     axi_ctrl_addr_decode
//   axi_ctrl_reg_bank
//     axi_ctrl_reg
//
///////////////////////////////////////////////////////////////////////////////
`timescale 1ps/1ps
`default_nettype none

module ddr4_v2_2_0_axi_ctrl_top #
(
///////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
///////////////////////////////////////////////////////////////////////////////
  // Width of AXI-4-Lite address bus
  parameter integer C_S_AXI_CTRL_ADDR_WIDTH              = 32, 
  // Width of AXI-4-Lite data buses
  parameter integer C_S_AXI_CTRL_DATA_WIDTH              = 32, 
  // Width of AXI-4 Memory Mapped address bus
  parameter integer C_S_AXI_ADDR_WIDTH                   = 32, 
  // Width of AXI-4 Memory Mapped address bus
  parameter integer C_S_AXI_BASEADDR                     = 32'h0000_0000, 
  // Enable or disable fault injection logic test hardware.
  parameter         C_ECC_TEST                           = "ON",
  // External Memory Data Width
  parameter integer C_DQ_WIDTH                           = 72,
  // Memory ECC Width             
  parameter integer C_ECC_WIDTH                          = 8,
  // Memory Address Order         
  parameter         C_MEM_ADDR_ORDER                     = "BANK_ROW_COLUMN",
  // # of memory Bank Address bits.
  parameter         C_BANK_WIDTH                         = 3,
  // # of memory Row Address bits.           
  parameter         C_ROW_WIDTH                          = 14,
  // # of memory Column Address bits.        
  parameter         C_COL_WIDTH                          = 10,

  // Controls ECC on/off value at startup/reset
  parameter integer C_ECC_ONOFF_RESET_VALUE              = 1,
  // Controls CE counter width                   
  parameter integer C_ECC_CE_COUNTER_WIDTH               = 8,
  // The external memory to controller clock ratio.
  parameter integer C_NCK_PER_CLK                        = 2,
  parameter         C_MC_ERR_ADDR_WIDTH                  = 28
)
(
///////////////////////////////////////////////////////////////////////////////
// Port Declarations     
///////////////////////////////////////////////////////////////////////////////
  // AXI4-Lite Slave Interface
  // Slave Interface System Signals           
  input  wire                               aclk              , 
  input  wire                               aresetn           , 
  // Slave Interface Write Address Ports
  input  wire                               s_axi_awvalid     , 
  output wire                               s_axi_awready     , 
  input  wire [C_S_AXI_CTRL_ADDR_WIDTH-1:0] s_axi_awaddr      , 
  // Slave Interface Write Data Ports
  input  wire                               s_axi_wvalid      , 
  output wire                               s_axi_wready      , 
  input  wire [C_S_AXI_CTRL_DATA_WIDTH-1:0] s_axi_wdata       , 
  // Slave Interface Write Response Ports
  output wire                               s_axi_bvalid      , 
  input  wire                               s_axi_bready      , 
  output wire [1:0]                         s_axi_bresp       , 
  // Slave Interface Read Address Ports
  input  wire                               s_axi_arvalid     , 
  output wire                               s_axi_arready     , 
  input  wire [C_S_AXI_CTRL_ADDR_WIDTH-1:0] s_axi_araddr      , 
  // Slave Interface Read Data Ports
  output wire                               s_axi_rvalid      , 
  input  wire                               s_axi_rready      , 
  output wire [C_S_AXI_CTRL_DATA_WIDTH-1:0] s_axi_rdata       , 
  output wire [1:0]                         s_axi_rresp       , 

  // Interrupt output
  output wire                               interrupt         ,

  // MC Internal Signals
  input  wire                               init_complete     , 
  input  wire [2*C_NCK_PER_CLK-1:0]         ecc_single        ,
  input  wire [2*C_NCK_PER_CLK-1:0]         ecc_multiple      ,
  input  wire [C_MC_ERR_ADDR_WIDTH-1:0]     ecc_err_addr      ,
  output wire                               app_correct_en    , 
  input  wire [2*C_NCK_PER_CLK*C_DQ_WIDTH-1:0] dfi_rddata     , 
  output wire [C_DQ_WIDTH/8-1:0]            fi_xor_we         ,
  output wire [C_DQ_WIDTH-1:0]              fi_xor_wrdata     
);

/////////////////////////////////////////////////////////////////////////////
// Functions
/////////////////////////////////////////////////////////////////////////////

function integer lsb_mask_index (
  input [C_S_AXI_CTRL_DATA_WIDTH-1:0] mask
);
begin : my_lsb_mask_index
  lsb_mask_index = 0;
  while ((lsb_mask_index < C_S_AXI_CTRL_DATA_WIDTH-1) && ~mask[lsb_mask_index]) begin 
    lsb_mask_index = lsb_mask_index + 1;
  end
end
endfunction

function integer msb_mask_index (
  input [C_S_AXI_CTRL_DATA_WIDTH-1:0] mask
);
begin : my_msb_mask_index
  msb_mask_index = C_S_AXI_CTRL_DATA_WIDTH-1;
  while ((msb_mask_index > 0) && ~mask[msb_mask_index]) begin 
      msb_mask_index = msb_mask_index - 1;
  end
end
endfunction

function integer mask_width (
  input [C_S_AXI_CTRL_DATA_WIDTH-1:0] mask
);
begin : my_mask_width
  if (msb_mask_index(mask) > lsb_mask_index(mask)) begin
    mask_width = msb_mask_index(mask) - lsb_mask_index(mask) + 1;
  end
  else begin
    mask_width = 1;
  end
end
endfunction

// clog2.
function integer clog2;
  // Value to calculate clog2 on
  input integer value;
begin
  for (clog2=0; value>0; clog2=clog2+1) begin
    value = value >> 1;
  end
end
endfunction

////////////////////////////////////////////////////////////////////////////////
// Local parameters
////////////////////////////////////////////////////////////////////////////////

// BEGIN Auto-generated Register Mapping
localparam P_NUM_REG = 24;
localparam P_NUM_REG_WIDTH = clog2(P_NUM_REG);

localparam P_REG_FI_ECC_RDAC = 1'b0;
localparam P_REG_FI_ECC_INDX = 23;
localparam P_REG_FI_ECC_INIT = 32'h0000_0000;
localparam P_REG_FI_ECC_WRAC = 1'b1;//(C_ECC_TEST == "ON") ? 1'b1 : 1'b0;
localparam P_REG_FI_ECC_ADDR = 32'h0000_0380;
localparam P_REG_FI_ECC_MASK = 32'h0000_0000;

localparam P_REG_FI_D_127_96_RDAC = 1'b0;
localparam P_REG_FI_D_127_96_INDX = 22;
localparam P_REG_FI_D_127_96_INIT = 32'h0000_0000;
localparam P_REG_FI_D_127_96_WRAC = 1'b1;//(C_ECC_TEST == "ON") && (C_DQ_WIDTH > 72) ? 1'b1 : 1'b0;
localparam P_REG_FI_D_127_96_ADDR = 32'h0000_030C;
localparam P_REG_FI_D_127_96_MASK = 32'h0000_0000;

localparam P_REG_FI_D_95_64_RDAC = 1'b0;
localparam P_REG_FI_D_95_64_INDX = 21;
localparam P_REG_FI_D_95_64_INIT = 32'h0000_0000;
localparam P_REG_FI_D_95_64_WRAC = 1'b1;//(C_ECC_TEST == "ON") && (C_DQ_WIDTH > 72) ? 1'b1 : 1'b0;
localparam P_REG_FI_D_95_64_ADDR = 32'h0000_0308;
localparam P_REG_FI_D_95_64_MASK = 32'h0000_0000;

localparam P_REG_FI_D_63_32_RDAC = 1'b0;
localparam P_REG_FI_D_63_32_INDX = 20;
localparam P_REG_FI_D_63_32_INIT = 32'h0000_0000;
localparam P_REG_FI_D_63_32_WRAC = 1'b1;//(C_ECC_TEST == "ON") ? 1'b1 : 1'b0;
localparam P_REG_FI_D_63_32_ADDR = 32'h0000_0304;
localparam P_REG_FI_D_63_32_MASK = 32'h0000_0000;

localparam P_REG_FI_D_31_00_RDAC = 1'b0;
localparam P_REG_FI_D_31_00_INDX = 19;
localparam P_REG_FI_D_31_00_INIT = 32'h0000_0000;
localparam P_REG_FI_D_31_00_WRAC = 1'b1;//(C_ECC_TEST == "ON") ? 1'b1 : 1'b0;
localparam P_REG_FI_D_31_00_ADDR = 32'h0000_0300;
localparam P_REG_FI_D_31_00_MASK = 32'h0000_0000;

localparam P_REG_UE_FFA_63_32_RDAC = 1'b1;
localparam P_REG_UE_FFA_63_32_INDX = 18;
localparam P_REG_UE_FFA_63_32_INIT = 32'h0000_0000;
localparam P_REG_UE_FFA_63_32_WRAC = 1'b0;
localparam P_REG_UE_FFA_63_32_ADDR = 32'h0000_02C4;
localparam P_REG_UE_FFA_63_32_MASK = 32'hFFFF_FFFF;

localparam P_REG_UE_FFA_31_00_RDAC = 1'b1;
localparam P_REG_UE_FFA_31_00_INDX = 17;
localparam P_REG_UE_FFA_31_00_INIT = 32'h0000_0000;
localparam P_REG_UE_FFA_31_00_WRAC = 1'b0;
localparam P_REG_UE_FFA_31_00_ADDR = 32'h0000_02C0;
localparam P_REG_UE_FFA_31_00_MASK = 32'hFFFF_FFFF;

localparam P_REG_UE_FFE_RDAC = 1'b1;
localparam P_REG_UE_FFE_INDX = 16;
localparam P_REG_UE_FFE_INIT = 32'h0000_0000;
localparam P_REG_UE_FFE_WRAC = 1'b0;
localparam P_REG_UE_FFE_ADDR = 32'h0000_0280;
localparam P_REG_UE_FFE_MASK = 32'h0000_FFFF;

localparam P_REG_UE_FFD_127_96_RDAC = (C_DQ_WIDTH > 72) ? 1'b1 : 1'b0 ;
localparam P_REG_UE_FFD_127_96_INDX = 15;
localparam P_REG_UE_FFD_127_96_INIT = 32'h0000_0000;
localparam P_REG_UE_FFD_127_96_WRAC = 1'b0;
localparam P_REG_UE_FFD_127_96_ADDR = 32'h0000_020C;
localparam P_REG_UE_FFD_127_96_MASK = 32'hFFFF_FFFF;

localparam P_REG_UE_FFD_95_64_RDAC = (C_DQ_WIDTH > 72) ? 1'b1 : 1'b0 ;
localparam P_REG_UE_FFD_95_64_INDX = 14;
localparam P_REG_UE_FFD_95_64_INIT = 32'h0000_0000;
localparam P_REG_UE_FFD_95_64_WRAC = 1'b0;
localparam P_REG_UE_FFD_95_64_ADDR = 32'h0000_0208;
localparam P_REG_UE_FFD_95_64_MASK = 32'hFFFF_FFFF;

localparam P_REG_UE_FFD_63_32_RDAC = 1'b1;
localparam P_REG_UE_FFD_63_32_INDX = 13;
localparam P_REG_UE_FFD_63_32_INIT = 32'h0000_0000;
localparam P_REG_UE_FFD_63_32_WRAC = 1'b0;
localparam P_REG_UE_FFD_63_32_ADDR = 32'h0000_0204;
localparam P_REG_UE_FFD_63_32_MASK = 32'hFFFF_FFFF;

localparam P_REG_UE_FFD_31_00_RDAC = 1'b1;
localparam P_REG_UE_FFD_31_00_INDX = 12;
localparam P_REG_UE_FFD_31_00_INIT = 32'h0000_0000;
localparam P_REG_UE_FFD_31_00_WRAC = 1'b0;
localparam P_REG_UE_FFD_31_00_ADDR = 32'h0000_0200;
localparam P_REG_UE_FFD_31_00_MASK = 32'hFFFF_FFFF;

localparam P_REG_CE_FFA_63_32_RDAC = 1'b1;
localparam P_REG_CE_FFA_63_32_INDX = 11;
localparam P_REG_CE_FFA_63_32_INIT = 32'h0000_0000;
localparam P_REG_CE_FFA_63_32_WRAC = 1'b0;
localparam P_REG_CE_FFA_63_32_ADDR = 32'h0000_01C4;
localparam P_REG_CE_FFA_63_32_MASK = 32'hFFFF_FFFF;

localparam P_REG_CE_FFA_31_00_RDAC = 1'b1;
localparam P_REG_CE_FFA_31_00_INDX = 10;
localparam P_REG_CE_FFA_31_00_INIT = 32'h0000_0000;
localparam P_REG_CE_FFA_31_00_WRAC = 1'b0;
localparam P_REG_CE_FFA_31_00_ADDR = 32'h0000_01C0;
localparam P_REG_CE_FFA_31_00_MASK = 32'hFFFF_FFFF;

localparam P_REG_CE_FFE_RDAC = 1'b1;
localparam P_REG_CE_FFE_INDX = 9;
localparam P_REG_CE_FFE_INIT = 32'h0000_0000;
localparam P_REG_CE_FFE_WRAC = 1'b0;
localparam P_REG_CE_FFE_ADDR = 32'h0000_0180;
localparam P_REG_CE_FFE_MASK = 32'h0000_FFFF;

localparam P_REG_CE_FFD_127_96_RDAC = (C_DQ_WIDTH > 72) ? 1'b1 : 1'b0 ;
localparam P_REG_CE_FFD_127_96_INDX = 8;
localparam P_REG_CE_FFD_127_96_INIT = 32'h0000_0000;
localparam P_REG_CE_FFD_127_96_WRAC = 1'b0;
localparam P_REG_CE_FFD_127_96_ADDR = 32'h0000_010C;
localparam P_REG_CE_FFD_127_96_MASK = 32'hFFFF_FFFF;

localparam P_REG_CE_FFD_95_64_RDAC = (C_DQ_WIDTH > 72) ? 1'b1 : 1'b0 ;
localparam P_REG_CE_FFD_95_64_INDX = 7;
localparam P_REG_CE_FFD_95_64_INIT = 32'h0000_0000;
localparam P_REG_CE_FFD_95_64_WRAC = 1'b0;
localparam P_REG_CE_FFD_95_64_ADDR = 32'h0000_0108;
localparam P_REG_CE_FFD_95_64_MASK = 32'hFFFF_FFFF;

localparam P_REG_CE_FFD_63_32_RDAC = 1'b1;
localparam P_REG_CE_FFD_63_32_INDX = 6;
localparam P_REG_CE_FFD_63_32_INIT = 32'h0000_0000;
localparam P_REG_CE_FFD_63_32_WRAC = 1'b0;
localparam P_REG_CE_FFD_63_32_ADDR = 32'h0000_0104;
localparam P_REG_CE_FFD_63_32_MASK = 32'hFFFF_FFFF;

localparam P_REG_CE_FFD_31_00_RDAC = 1'b1;
localparam P_REG_CE_FFD_31_00_INDX = 5;
localparam P_REG_CE_FFD_31_00_INIT = 32'h0000_0000;
localparam P_REG_CE_FFD_31_00_WRAC = 1'b0;
localparam P_REG_CE_FFD_31_00_ADDR = 32'h0000_0100;
localparam P_REG_CE_FFD_31_00_MASK = 32'hFFFF_FFFF;

localparam P_REG_CE_CNT_RDAC = 1'b1;
localparam P_REG_CE_CNT_INDX = 4;
localparam P_REG_CE_CNT_INIT = 32'h0000_0000;
localparam P_REG_CE_CNT_WRAC = 1'b1;
localparam P_REG_CE_CNT_ADDR = 32'h0000_000C;
localparam P_REG_CE_CNT_MASK = {{C_S_AXI_CTRL_DATA_WIDTH-C_ECC_CE_COUNTER_WIDTH{1'b0}}, {C_ECC_CE_COUNTER_WIDTH{1'b1}}};

localparam P_REG_ECC_ON_OFF_RDAC = 1'b1;
localparam P_REG_ECC_ON_OFF_INDX = 3;
localparam P_REG_ECC_ON_OFF_INIT = {{31{1'b0}}, C_ECC_ONOFF_RESET_VALUE[0]};
localparam P_REG_ECC_ON_OFF_WRAC = 1'b1;
localparam P_REG_ECC_ON_OFF_ADDR = 32'h0000_0008;
localparam P_REG_ECC_ON_OFF_MASK = 32'h0000_0001;

localparam P_REG_ECC_EN_IRQ_RDAC = 1'b1;
localparam P_REG_ECC_EN_IRQ_INDX = 2;
localparam P_REG_ECC_EN_IRQ_INIT = 32'h0000_0000;
localparam P_REG_ECC_EN_IRQ_WRAC = 1'b1;
localparam P_REG_ECC_EN_IRQ_ADDR = 32'h0000_0004;
localparam P_REG_ECC_EN_IRQ_MASK = 32'h0000_0003;

localparam P_REG_ECC_STATUS_RDAC = 1'b1;
localparam P_REG_ECC_STATUS_INDX = 1;
localparam P_REG_ECC_STATUS_INIT = 32'h0000_0000;
localparam P_REG_ECC_STATUS_WRAC = 1'b1;
localparam P_REG_ECC_STATUS_ADDR = 32'h0000_0000;
localparam P_REG_ECC_STATUS_MASK = 32'h0000_0003;

localparam P_REG_DUMMY_RDAC = 1'b1;
localparam P_REG_DUMMY_INDX = 0;
localparam P_REG_DUMMY_INIT = 32'hDEAD_DEAD;
localparam P_REG_DUMMY_WRAC = 1'b1;
localparam P_REG_DUMMY_ADDR = 32'hFFFF_FFFF;
localparam P_REG_DUMMY_MASK = 32'hFFFF_FFFF;

localparam P_REG_INDX_ARRAY = {
    P_REG_FI_ECC_INDX,
    P_REG_FI_D_127_96_INDX,
    P_REG_FI_D_95_64_INDX,
    P_REG_FI_D_63_32_INDX,
    P_REG_FI_D_31_00_INDX,
    P_REG_UE_FFA_63_32_INDX,
    P_REG_UE_FFA_31_00_INDX,
    P_REG_UE_FFE_INDX,
    P_REG_UE_FFD_127_96_INDX,
    P_REG_UE_FFD_95_64_INDX,
    P_REG_UE_FFD_63_32_INDX,
    P_REG_UE_FFD_31_00_INDX,
    P_REG_CE_FFA_63_32_INDX,
    P_REG_CE_FFA_31_00_INDX,
    P_REG_CE_FFE_INDX,
    P_REG_CE_FFD_127_96_INDX,
    P_REG_CE_FFD_95_64_INDX,
    P_REG_CE_FFD_63_32_INDX,
    P_REG_CE_FFD_31_00_INDX,
    P_REG_CE_CNT_INDX,
    P_REG_ECC_ON_OFF_INDX,
    P_REG_ECC_EN_IRQ_INDX,
    P_REG_ECC_STATUS_INDX,
    P_REG_DUMMY_INDX
};

localparam P_REG_RDAC_ARRAY = {
    P_REG_FI_ECC_RDAC,
    P_REG_FI_D_127_96_RDAC,
    P_REG_FI_D_95_64_RDAC,
    P_REG_FI_D_63_32_RDAC,
    P_REG_FI_D_31_00_RDAC,
    P_REG_UE_FFA_63_32_RDAC,
    P_REG_UE_FFA_31_00_RDAC,
    P_REG_UE_FFE_RDAC,
    P_REG_UE_FFD_127_96_RDAC,
    P_REG_UE_FFD_95_64_RDAC,
    P_REG_UE_FFD_63_32_RDAC,
    P_REG_UE_FFD_31_00_RDAC,
    P_REG_CE_FFA_63_32_RDAC,
    P_REG_CE_FFA_31_00_RDAC,
    P_REG_CE_FFE_RDAC,
    P_REG_CE_FFD_127_96_RDAC,
    P_REG_CE_FFD_95_64_RDAC,
    P_REG_CE_FFD_63_32_RDAC,
    P_REG_CE_FFD_31_00_RDAC,
    P_REG_CE_CNT_RDAC,
    P_REG_ECC_ON_OFF_RDAC,
    P_REG_ECC_EN_IRQ_RDAC,
    P_REG_ECC_STATUS_RDAC,
    P_REG_DUMMY_RDAC
};

localparam P_REG_INIT_ARRAY = {
    P_REG_FI_ECC_INIT,
    P_REG_FI_D_127_96_INIT,
    P_REG_FI_D_95_64_INIT,
    P_REG_FI_D_63_32_INIT,
    P_REG_FI_D_31_00_INIT,
    P_REG_UE_FFA_63_32_INIT,
    P_REG_UE_FFA_31_00_INIT,
    P_REG_UE_FFE_INIT,
    P_REG_UE_FFD_127_96_INIT,
    P_REG_UE_FFD_95_64_INIT,
    P_REG_UE_FFD_63_32_INIT,
    P_REG_UE_FFD_31_00_INIT,
    P_REG_CE_FFA_63_32_INIT,
    P_REG_CE_FFA_31_00_INIT,
    P_REG_CE_FFE_INIT,
    P_REG_CE_FFD_127_96_INIT,
    P_REG_CE_FFD_95_64_INIT,
    P_REG_CE_FFD_63_32_INIT,
    P_REG_CE_FFD_31_00_INIT,
    P_REG_CE_CNT_INIT,
    P_REG_ECC_ON_OFF_INIT,
    P_REG_ECC_EN_IRQ_INIT,
    P_REG_ECC_STATUS_INIT,
    P_REG_DUMMY_INIT
};

localparam P_REG_ADDR_ARRAY = {
    P_REG_FI_ECC_ADDR,
    P_REG_FI_D_127_96_ADDR,
    P_REG_FI_D_95_64_ADDR,
    P_REG_FI_D_63_32_ADDR,
    P_REG_FI_D_31_00_ADDR,
    P_REG_UE_FFA_63_32_ADDR,
    P_REG_UE_FFA_31_00_ADDR,
    P_REG_UE_FFE_ADDR,
    P_REG_UE_FFD_127_96_ADDR,
    P_REG_UE_FFD_95_64_ADDR,
    P_REG_UE_FFD_63_32_ADDR,
    P_REG_UE_FFD_31_00_ADDR,
    P_REG_CE_FFA_63_32_ADDR,
    P_REG_CE_FFA_31_00_ADDR,
    P_REG_CE_FFE_ADDR,
    P_REG_CE_FFD_127_96_ADDR,
    P_REG_CE_FFD_95_64_ADDR,
    P_REG_CE_FFD_63_32_ADDR,
    P_REG_CE_FFD_31_00_ADDR,
    P_REG_CE_CNT_ADDR,
    P_REG_ECC_ON_OFF_ADDR,
    P_REG_ECC_EN_IRQ_ADDR,
    P_REG_ECC_STATUS_ADDR,
    P_REG_DUMMY_ADDR
};

localparam P_REG_WRAC_ARRAY = {
    P_REG_FI_ECC_WRAC,
    P_REG_FI_D_127_96_WRAC,
    P_REG_FI_D_95_64_WRAC,
    P_REG_FI_D_63_32_WRAC,
    P_REG_FI_D_31_00_WRAC,
    P_REG_UE_FFA_63_32_WRAC,
    P_REG_UE_FFA_31_00_WRAC,
    P_REG_UE_FFE_WRAC,
    P_REG_UE_FFD_127_96_WRAC,
    P_REG_UE_FFD_95_64_WRAC,
    P_REG_UE_FFD_63_32_WRAC,
    P_REG_UE_FFD_31_00_WRAC,
    P_REG_CE_FFA_63_32_WRAC,
    P_REG_CE_FFA_31_00_WRAC,
    P_REG_CE_FFE_WRAC,
    P_REG_CE_FFD_127_96_WRAC,
    P_REG_CE_FFD_95_64_WRAC,
    P_REG_CE_FFD_63_32_WRAC,
    P_REG_CE_FFD_31_00_WRAC,
    P_REG_CE_CNT_WRAC,
    P_REG_ECC_ON_OFF_WRAC,
    P_REG_ECC_EN_IRQ_WRAC,
    P_REG_ECC_STATUS_WRAC,
    P_REG_DUMMY_WRAC
};

localparam P_REG_WIDTH_ARRAY = {
    mask_width(P_REG_FI_ECC_MASK),
    mask_width(P_REG_FI_D_127_96_MASK),
    mask_width(P_REG_FI_D_95_64_MASK),
    mask_width(P_REG_FI_D_63_32_MASK),
    mask_width(P_REG_FI_D_31_00_MASK),
    mask_width(P_REG_UE_FFA_63_32_MASK),
    mask_width(P_REG_UE_FFA_31_00_MASK),
    mask_width(P_REG_UE_FFE_MASK),
    mask_width(P_REG_UE_FFD_127_96_MASK),
    mask_width(P_REG_UE_FFD_95_64_MASK),
    mask_width(P_REG_UE_FFD_63_32_MASK),
    mask_width(P_REG_UE_FFD_31_00_MASK),
    mask_width(P_REG_CE_FFA_63_32_MASK),
    mask_width(P_REG_CE_FFA_31_00_MASK),
    mask_width(P_REG_CE_FFE_MASK),
    mask_width(P_REG_CE_FFD_127_96_MASK),
    mask_width(P_REG_CE_FFD_95_64_MASK),
    mask_width(P_REG_CE_FFD_63_32_MASK),
    mask_width(P_REG_CE_FFD_31_00_MASK),
    mask_width(P_REG_CE_CNT_MASK),
    mask_width(P_REG_ECC_ON_OFF_MASK),
    mask_width(P_REG_ECC_EN_IRQ_MASK),
    mask_width(P_REG_ECC_STATUS_MASK),
    mask_width(P_REG_DUMMY_MASK)
};

localparam P_REG_MASK_ARRAY = {
    P_REG_FI_ECC_MASK,
    P_REG_FI_D_127_96_MASK,
    P_REG_FI_D_95_64_MASK,
    P_REG_FI_D_63_32_MASK,
    P_REG_FI_D_31_00_MASK,
    P_REG_UE_FFA_63_32_MASK,
    P_REG_UE_FFA_31_00_MASK,
    P_REG_UE_FFE_MASK,
    P_REG_UE_FFD_127_96_MASK,
    P_REG_UE_FFD_95_64_MASK,
    P_REG_UE_FFD_63_32_MASK,
    P_REG_UE_FFD_31_00_MASK,
    P_REG_CE_FFA_63_32_MASK,
    P_REG_CE_FFA_31_00_MASK,
    P_REG_CE_FFE_MASK,
    P_REG_CE_FFD_127_96_MASK,
    P_REG_CE_FFD_95_64_MASK,
    P_REG_CE_FFD_63_32_MASK,
    P_REG_CE_FFD_31_00_MASK,
    P_REG_CE_CNT_MASK,
    P_REG_ECC_ON_OFF_MASK,
    P_REG_ECC_EN_IRQ_MASK,
    P_REG_ECC_STATUS_MASK,
    P_REG_DUMMY_MASK
};

// END Auto-generated Register Mapping

////////////////////////////////////////////////////////////////////////////////
// Wires/Reg declarations
////////////////////////////////////////////////////////////////////////////////

wire [ P_NUM_REG_WIDTH-1:0                   ] reg_data_sel;
wire                                           reg_data_write;
wire [ C_S_AXI_CTRL_DATA_WIDTH-1:0           ] reg_data_in;
wire [ C_S_AXI_CTRL_DATA_WIDTH*P_NUM_REG-1:0 ] reg_data_out;
wire                                           reset;
wire                                           arhandshake;
wire                                           rhandshake;
wire                                           awhandshake;
wire                                           bhandshake;
reg                                            wr_pending;
reg                                            rd_pending;
reg                                            arready_r;
reg                                            awready_r;
reg  [ C_S_AXI_CTRL_ADDR_WIDTH-1:0           ] addr;

////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
///////////////////////////////////////////////////////////////////////////////
assign reset = ~aresetn;
assign arhandshake = s_axi_arvalid & s_axi_arready;
assign awhandshake = s_axi_awvalid & s_axi_awready;
assign rhandshake  = s_axi_rvalid  & s_axi_rready;
assign bhandshake  = s_axi_bvalid  & s_axi_bready;
assign s_axi_awready = awready_r;
assign s_axi_arready = arready_r;

always @(posedge aclk) begin 
  if (reset) begin
    wr_pending <= 1'b0;
  end
  else begin 
    wr_pending <= (awhandshake | wr_pending) & ~bhandshake;
  end
end

always @(posedge aclk) begin 
  if (reset) begin
    rd_pending <= 1'b0;
  end
  else begin 
    rd_pending <= (arhandshake | rd_pending) & ~rhandshake;
  end
end

always @(posedge aclk) begin 
  if (reset | ~init_complete) begin
    awready_r <= 1'b0;
  end
  else begin 
    awready_r <= s_axi_awvalid & ~rd_pending & ~wr_pending & ~awready_r;
  end
end

always @(posedge aclk) begin 
  if (reset | ~init_complete) begin
    arready_r <= 1'b0;
  end
  else begin 
    arready_r <= s_axi_arvalid & ~rd_pending & ~wr_pending & ~s_axi_awvalid & ~arready_r;
  end
end

always @(posedge aclk) begin 
  if (awhandshake) begin 
    addr <= s_axi_awaddr; 
  end else if (arhandshake) begin 
    addr <= s_axi_araddr;
  end
end

// Instantiate AXI4-Lite write channel module
ddr4_v2_2_0_axi_ctrl_write #
( 
  .C_ADDR_WIDTH     ( C_S_AXI_CTRL_ADDR_WIDTH ) ,
  .C_DATA_WIDTH     ( C_S_AXI_CTRL_DATA_WIDTH ) ,
  .C_NUM_REG        ( P_NUM_REG               ) ,
  .C_NUM_REG_WIDTH  ( P_NUM_REG_WIDTH         ) ,
  .C_REG_ADDR_ARRAY ( P_REG_ADDR_ARRAY        ) ,
  .C_REG_WRAC_ARRAY ( P_REG_WRAC_ARRAY        )
)
axi_ctrl_write_0
(
  .clk            ( aclk           ) ,
  .reset          ( reset          ) ,
  .awvalid        ( s_axi_awvalid  ) ,
  .awready        ( s_axi_awready  ) ,
  .awaddr         ( addr           ) ,
  .wvalid         ( s_axi_wvalid   ) ,
  .wready         ( s_axi_wready   ) ,
  .wdata          ( s_axi_wdata    ) ,
  .bvalid         ( s_axi_bvalid   ) ,
  .bready         ( s_axi_bready   ) ,
  .bresp          ( s_axi_bresp    ) ,
  .reg_data_sel   ( reg_data_sel   ) ,
  .reg_data_write ( reg_data_write ) ,
  .reg_data       ( reg_data_in    ) 
);
  
// Instantiate AXI4-Lite write channel module
ddr4_v2_2_0_axi_ctrl_read #
( 
  .C_ADDR_WIDTH     ( C_S_AXI_CTRL_ADDR_WIDTH ) ,
  .C_DATA_WIDTH     ( C_S_AXI_CTRL_DATA_WIDTH ) ,
  .C_NUM_REG        ( P_NUM_REG               ) ,
  .C_NUM_REG_WIDTH  ( P_NUM_REG_WIDTH         ) ,
  .C_REG_ADDR_ARRAY ( P_REG_ADDR_ARRAY        ) ,
  .C_REG_RDAC_ARRAY ( P_REG_RDAC_ARRAY        ) 
)
axi_ctrl_read_0
(
  .clk            ( aclk          ) ,
  .reset          ( reset         ) ,
  .araddr         ( addr          ) ,
  .rvalid         ( s_axi_rvalid  ) ,
  .rready         ( s_axi_rready  ) ,
  .rresp          ( s_axi_rresp   ) ,
  .rdata          ( s_axi_rdata   ) ,
  .pending        ( rd_pending    ) ,
  .reg_bank_array ( reg_data_out  ) 
);
 
ddr4_v2_2_0_axi_ctrl_reg_bank #
(
  .C_ADDR_WIDTH             ( C_S_AXI_CTRL_ADDR_WIDTH  ) ,
  .C_DATA_WIDTH             ( C_S_AXI_CTRL_DATA_WIDTH  ) ,
  .C_DQ_WIDTH               ( C_DQ_WIDTH               ) ,
  .C_ECC_CE_COUNTER_WIDTH   ( C_ECC_CE_COUNTER_WIDTH   ) ,
  .C_ECC_ONOFF_RESET_VALUE  ( C_ECC_ONOFF_RESET_VALUE  ) ,
  .C_ECC_TEST               ( C_ECC_TEST               ) ,
  .C_ECC_WIDTH              ( C_ECC_WIDTH              ) ,
  .C_MC_ERR_ADDR_WIDTH      ( C_MC_ERR_ADDR_WIDTH      ) ,
  .C_MEM_ADDR_ORDER         ( C_MEM_ADDR_ORDER         ) ,
  .C_BANK_WIDTH             ( C_BANK_WIDTH             ) ,
  .C_ROW_WIDTH              ( C_ROW_WIDTH              ) ,
  .C_COL_WIDTH              ( C_COL_WIDTH              ) ,
  .C_NCK_PER_CLK            ( C_NCK_PER_CLK            ) ,
  .C_NUM_REG                ( P_NUM_REG                ) ,
  .C_NUM_REG_WIDTH          ( P_NUM_REG_WIDTH          ) ,
  .C_S_AXI_ADDR_WIDTH       ( C_S_AXI_ADDR_WIDTH       ) ,
  .C_S_AXI_BASEADDR         ( C_S_AXI_BASEADDR         ) ,
  // Register arrays
  .C_REG_RDAC_ARRAY         ( P_REG_RDAC_ARRAY         ) ,
  .C_REG_WRAC_ARRAY         ( P_REG_WRAC_ARRAY         ) ,
  .C_REG_INIT_ARRAY         ( P_REG_INIT_ARRAY         ) ,
  .C_REG_MASK_ARRAY         ( P_REG_MASK_ARRAY         ) ,
  .C_REG_ADDR_ARRAY         ( P_REG_ADDR_ARRAY         ) ,
  .C_REG_WIDTH_ARRAY        ( P_REG_WIDTH_ARRAY        ) ,
  // Register Indices
  .C_REG_FI_ECC_INDX        ( P_REG_FI_ECC_INDX        ) ,
  .C_REG_FI_D_127_96_INDX   ( P_REG_FI_D_127_96_INDX   ) ,
  .C_REG_FI_D_95_64_INDX    ( P_REG_FI_D_95_64_INDX    ) ,
  .C_REG_FI_D_63_32_INDX    ( P_REG_FI_D_63_32_INDX    ) ,
  .C_REG_FI_D_31_00_INDX    ( P_REG_FI_D_31_00_INDX    ) ,
  .C_REG_UE_FFA_63_32_INDX  ( P_REG_UE_FFA_63_32_INDX  ) ,
  .C_REG_UE_FFA_31_00_INDX  ( P_REG_UE_FFA_31_00_INDX  ) ,
  .C_REG_UE_FFE_INDX        ( P_REG_UE_FFE_INDX        ) ,
  .C_REG_UE_FFD_127_96_INDX ( P_REG_UE_FFD_127_96_INDX ) ,
  .C_REG_UE_FFD_95_64_INDX  ( P_REG_UE_FFD_95_64_INDX  ) ,
  .C_REG_UE_FFD_63_32_INDX  ( P_REG_UE_FFD_63_32_INDX  ) ,
  .C_REG_UE_FFD_31_00_INDX  ( P_REG_UE_FFD_31_00_INDX  ) ,
  .C_REG_CE_FFA_63_32_INDX  ( P_REG_CE_FFA_63_32_INDX  ) ,
  .C_REG_CE_FFA_31_00_INDX  ( P_REG_CE_FFA_31_00_INDX  ) ,
  .C_REG_CE_FFE_INDX        ( P_REG_CE_FFE_INDX        ) ,
  .C_REG_CE_FFD_127_96_INDX ( P_REG_CE_FFD_127_96_INDX ) ,
  .C_REG_CE_FFD_95_64_INDX  ( P_REG_CE_FFD_95_64_INDX  ) ,
  .C_REG_CE_FFD_63_32_INDX  ( P_REG_CE_FFD_63_32_INDX  ) ,
  .C_REG_CE_FFD_31_00_INDX  ( P_REG_CE_FFD_31_00_INDX  ) ,
  .C_REG_CE_CNT_INDX        ( P_REG_CE_CNT_INDX        ) ,
  .C_REG_ECC_ON_OFF_INDX    ( P_REG_ECC_ON_OFF_INDX    ) ,
  .C_REG_ECC_EN_IRQ_INDX    ( P_REG_ECC_EN_IRQ_INDX    ) ,
  .C_REG_ECC_STATUS_INDX    ( P_REG_ECC_STATUS_INDX    ) ,
  .C_REG_DUMMY_INDX         ( P_REG_DUMMY_INDX         ) 
  
)
axi_ctrl_reg_bank_0
(
  .clk            ( aclk           ) ,
  .reset          ( reset          ) ,
  .reg_data_sel   ( reg_data_sel   ) ,
  .reg_data_write ( reg_data_write ) ,
  .reg_data_in    ( reg_data_in    ) ,
  .reg_data_out   ( reg_data_out   ) ,
  .interrupt      ( interrupt      ) ,
  .ecc_single     ( ecc_single     ) ,
  .ecc_multiple   ( ecc_multiple   ) ,
  .ecc_err_addr   ( ecc_err_addr   ) ,
  .app_correct_en ( app_correct_en ) ,
  .dfi_rddata     ( dfi_rddata     ) ,
  .fi_xor_we      ( fi_xor_we      ) ,
  .fi_xor_wrdata  ( fi_xor_wrdata  ) 
);

endmodule

`default_nettype wire

