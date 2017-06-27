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
// File name: ddr4_v2_2_0_axi_ctrl_write.v
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

module ddr4_v2_2_0_axi_ctrl_write #
(
///////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
///////////////////////////////////////////////////////////////////////////////
  // Width of AXI-4-Lite address bus
  parameter integer C_ADDR_WIDTH        = 32,
  // Width of AXI-4-Lite data buses
  parameter integer C_DATA_WIDTH        = 32,
  // Number of Registers
  parameter integer C_NUM_REG           = 5,
  parameter integer C_NUM_REG_WIDTH     = 3,
  // Number of Registers
  parameter         C_REG_ADDR_ARRAY = 160'h0000_f00C_0000_f008_0000_f004_0000_f000_FFFF_FFFF,
  parameter         C_REG_WRAC_ARRAY = 5'b11111
)
(
///////////////////////////////////////////////////////////////////////////////
// Port Declarations     
///////////////////////////////////////////////////////////////////////////////
  // AXI4-Lite Slave Interface
  // Slave Interface System Signals           
  input  wire                               clk              , 
  input  wire                               reset           , 
  // Slave Interface Read Address Ports
  input  wire                               awvalid     , 
  input  wire                               awready     , 
  input  wire [C_ADDR_WIDTH-1:0]            awaddr      , 
  // Slave Interface Read Data Ports
  input  wire                               wvalid      , 
  output wire                               wready      , 
  input  wire [C_DATA_WIDTH-1:0]            wdata       , 

  output wire                               bvalid      , 
  input  wire                               bready      , 
  output wire [1:0]                         bresp       , 

  // Internal Signals
  output wire [C_NUM_REG_WIDTH-1:0]         reg_data_sel     ,
  output wire                               reg_data_write   ,
  output wire [C_DATA_WIDTH-1:0]            reg_data 
);

////////////////////////////////////////////////////////////////////////////////
// Local parameters
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
// Wires/Reg declarations
////////////////////////////////////////////////////////////////////////////////

wire                        awhandshake;
wire                        whandshake;
reg                         whandshake_d1;
wire                        bhandshake;
wire [C_NUM_REG_WIDTH-1:0]  reg_decode_num;
reg                         awready_i;
reg                         wready_i;
reg                         bvalid_i;
reg  [C_DATA_WIDTH-1:0]     data;

////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
///////////////////////////////////////////////////////////////////////////////

// Handshake signals
assign awhandshake = awvalid & awready;
assign whandshake = wvalid & wready;
assign bhandshake = bvalid & bready;

ddr4_v2_2_0_axi_ctrl_addr_decode #
(
  .C_ADDR_WIDTH     ( C_ADDR_WIDTH     ) ,
  .C_NUM_REG        ( C_NUM_REG        ) ,
  .C_NUM_REG_WIDTH  ( C_NUM_REG_WIDTH  ) ,
  .C_REG_ADDR_ARRAY ( C_REG_ADDR_ARRAY ) ,
  .C_REG_RDWR_ARRAY ( C_REG_WRAC_ARRAY ) 
)
axi_ctrl_addr_decode_0
(
  .axaddr         ( awaddr         ) ,
  .reg_decode_num ( reg_decode_num ) 
);

// wchannel only accepts data after aw handshake
assign wready = wready_i;

always @(posedge clk) begin
  if (reset) begin 
    wready_i <= 1'b0;
  end
  else begin
    wready_i <= (awhandshake | wready_i) & ~whandshake;
  end
end

// Data is registered but not latched (like awaddr) since it used a cycle later
always @(posedge clk) begin
  data <= wdata;
end

// bresponse is sent after successful w handshake
assign bvalid = bvalid_i;
assign bresp = 2'b0; // Okay

always @(posedge clk) begin
  if (reset) begin 
    bvalid_i <= 1'b0;
  end
  else begin
    bvalid_i <= (whandshake | bvalid_i) & ~bhandshake;
  end
end

// Assign internal signals 
assign reg_data       = data;
assign reg_data_write = whandshake_d1;
assign reg_data_sel   = reg_decode_num;

always @(posedge clk) begin
  whandshake_d1 <= whandshake;
end

endmodule

`default_nettype wire

