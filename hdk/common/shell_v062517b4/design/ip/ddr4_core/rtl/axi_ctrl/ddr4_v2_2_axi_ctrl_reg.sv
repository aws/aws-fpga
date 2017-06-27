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
// File name: ddr4_v2_2_0_axi_ctrl_reg.v     
//
// Description: 
// AXI Lite Controller
// This is just a general register.  It has two write enables and two data ins 
// to simplify the operation.  Typically one write enable (we) comes from the 
// external interface and the second write enable is used for internal writing
// to the register. A mask parameter is used to only write to the bits that
// are used in the register.
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

module ddr4_v2_2_0_axi_ctrl_reg #
(
///////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
///////////////////////////////////////////////////////////////////////////////
  parameter integer C_REG_WIDTH         = 32,
  parameter integer C_DATA_WIDTH        = 32,
  parameter         C_INIT              = 32'h0,
  parameter         C_MASK              = 32'h1
)
(
///////////////////////////////////////////////////////////////////////////////
// Port Declarations     
///////////////////////////////////////////////////////////////////////////////
  input  wire                               clk         , 
  input  wire                               reset       , 
  input  wire [C_REG_WIDTH-1:0]             data_in     , 
  input  wire                               we          , 
  input  wire                               we_int      , 
  input  wire [C_REG_WIDTH-1:0]             data_in_int , 
  output wire [C_DATA_WIDTH-1:0]            data_out
);
////////////////////////////////////////////////////////////////////////////////
// Functions
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// Local parameters
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// Wires/Reg declarations
////////////////////////////////////////////////////////////////////////////////
reg [C_REG_WIDTH-1:0] data;

////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
///////////////////////////////////////////////////////////////////////////////
always @(posedge clk) begin
  if (reset) begin
    data <= C_INIT[0+:C_REG_WIDTH];
  end
  else if (we) begin
    data <= data_in;
  end
  else if (we_int) begin
    data <= data_in_int;
  end
  else begin
    data <= data;
  end
end

// Does not supprot case where P_MASK_LSB > 0
generate 
  if (C_REG_WIDTH == C_DATA_WIDTH) begin : assign_no_zero_pad
    assign data_out = data;
  end
  else begin : assign_zero_pad
    assign data_out = {{C_DATA_WIDTH-C_REG_WIDTH{1'b0}}, data};
  end
endgenerate

endmodule

`default_nettype wire

