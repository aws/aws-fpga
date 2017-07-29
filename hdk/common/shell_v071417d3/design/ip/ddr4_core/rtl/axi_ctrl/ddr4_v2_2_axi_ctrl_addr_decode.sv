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
// File name: ddr4_v2_2_0_axi_ctrl_addr_decode.v
//
// Description: AXI Lite Controller
//
// Specifications:
//
// Structure:
//
///////////////////////////////////////////////////////////////////////////////
`timescale 1ps/1ps
`default_nettype none

module ddr4_v2_2_0_axi_ctrl_addr_decode #
(
///////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
///////////////////////////////////////////////////////////////////////////////
  // Width of AXI-4-Lite address bus
  parameter integer C_ADDR_WIDTH        = 32,
  // Number of Registers
  parameter integer C_NUM_REG           = 5,
  parameter integer C_NUM_REG_WIDTH     = 3,
  // Number of Registers
  parameter         C_REG_ADDR_ARRAY = 160'h0000_f00C_0000_f008_0000_f004_0000_f000_FFFF_FFFF,
  parameter         C_REG_RDWR_ARRAY = 5'b00101

)
(
///////////////////////////////////////////////////////////////////////////////
// Port Declarations     
///////////////////////////////////////////////////////////////////////////////
  // AXI4-Lite Slave Interface
  // Slave Interface System Signals           
  input  wire [C_ADDR_WIDTH-1:0]            axaddr          , 
  // Slave Interface Write Data Ports
  output wire [C_NUM_REG_WIDTH-1:0]         reg_decode_num
);

////////////////////////////////////////////////////////////////////////////////
// Functions
////////////////////////////////////////////////////////////////////////////////

function [C_ADDR_WIDTH-1:0] calc_bit_mask (
  input [C_NUM_REG*C_ADDR_WIDTH-1:0] addr_decode_array
);
begin : func_calc_bit_mask
  integer i;
  reg [C_ADDR_WIDTH-1:0] first_addr;
  reg [C_ADDR_WIDTH-1:0] bit_mask;

  calc_bit_mask = {C_ADDR_WIDTH{1'b0}};
  first_addr = addr_decode_array[C_ADDR_WIDTH+:C_ADDR_WIDTH];

  for (i = 2; i < C_NUM_REG; i = i + 1) begin
    bit_mask = first_addr ^ addr_decode_array[C_ADDR_WIDTH*i +: C_ADDR_WIDTH];
    calc_bit_mask = calc_bit_mask | bit_mask;
  end
end
endfunction

function integer lsb_mask_index (
  input [C_ADDR_WIDTH-1:0] mask
);
begin : my_lsb_mask_index
  lsb_mask_index = 0;
  while ((lsb_mask_index < C_ADDR_WIDTH-1) && ~mask[lsb_mask_index]) begin 
    lsb_mask_index = lsb_mask_index + 1;
  end
end
endfunction

function integer msb_mask_index (
  input [C_ADDR_WIDTH-1:0] mask
);
begin : my_msb_mask_index
  msb_mask_index = C_ADDR_WIDTH-1;
  while ((msb_mask_index > 0) && ~mask[msb_mask_index]) begin 
      msb_mask_index = msb_mask_index - 1;
  end
end
endfunction

////////////////////////////////////////////////////////////////////////////////
// Local parameters
////////////////////////////////////////////////////////////////////////////////
localparam P_ADDR_BIT_MASK      = calc_bit_mask(C_REG_ADDR_ARRAY);
localparam P_MASK_LSB           = lsb_mask_index(P_ADDR_BIT_MASK);
localparam P_MASK_MSB           = msb_mask_index(P_ADDR_BIT_MASK);
localparam P_MASK_WIDTH         = P_MASK_MSB - P_MASK_LSB + 1;

////////////////////////////////////////////////////////////////////////////////
// Wires/Reg declarations
////////////////////////////////////////////////////////////////////////////////
integer i;
(* rom_extract = "no" *)
reg [C_NUM_REG_WIDTH-1:0] reg_decode_num_i;

////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
///////////////////////////////////////////////////////////////////////////////
always @(*) begin 
  reg_decode_num_i = {C_NUM_REG_WIDTH{1'b0}};
  for (i = 1; i < C_NUM_REG; i = i + 1) begin : decode_addr
    if ((axaddr[P_MASK_MSB:P_MASK_LSB] == C_REG_ADDR_ARRAY[i*C_ADDR_WIDTH+P_MASK_LSB+:P_MASK_WIDTH]) 
        && C_REG_RDWR_ARRAY[i] ) begin
      reg_decode_num_i = i[C_NUM_REG_WIDTH-1:0];
    end
  end
end

assign reg_decode_num = reg_decode_num_i;

endmodule

`default_nettype wire

