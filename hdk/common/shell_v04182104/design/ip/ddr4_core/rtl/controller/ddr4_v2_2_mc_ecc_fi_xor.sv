//*****************************************************************************
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
//
//*****************************************************************************
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor             : Xilinx
// \   \   \/     Version            : 1.1
//  \   \         Application        : MIG
//  /   /         Filename           : ddr4_v2_2_10_mc_ecc_fi_xor.xv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Tue May 13 2014
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_mc_ecc_fi_xor module
// Reference        :
// Revision History :
//*****************************************************************************
///////////////////////////////////////////////////////////////////////////////
`timescale 1ns/100ps
`default_nettype none

module ddr4_v2_2_10_mc_ecc_fi_xor #
(
///////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
///////////////////////////////////////////////////////////////////////////////
  // External Memory Data Width
  parameter integer DQ_WIDTH               = 72,
  parameter integer DQS_WIDTH              = 9,
  parameter integer DATA_WIDTH             = 64,
  parameter integer ECC_WIDTH              = 8,
  parameter integer nCK_PER_CLK            = 4,
  parameter TCQ = 100
)
(
///////////////////////////////////////////////////////////////////////////////
// Port Declarations     
///////////////////////////////////////////////////////////////////////////////
  input  wire                              clk           , 
  input  wire                              rst           , 
  input  wire [2*nCK_PER_CLK*DQ_WIDTH-1:0] wrdata_in     , 
  output wire [2*nCK_PER_CLK*DQ_WIDTH-1:0] wrdata_out    , 
  input  wire                              wrdata_en     , 
  input  wire [DQS_WIDTH-1:0]              fi_xor_we     ,
  input  wire [DQ_WIDTH-1:0]               fi_xor_wrdata
);

/////////////////////////////////////////////////////////////////////////////
// Functions
/////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// Local parameters
////////////////////////////////////////////////////////////////////////////////
localparam DQ_PER_DQS = DQ_WIDTH / DQS_WIDTH;

////////////////////////////////////////////////////////////////////////////////
// Wires/Reg declarations
////////////////////////////////////////////////////////////////////////////////
reg [DQ_WIDTH-1:0]              fi_xor_data = {DQ_WIDTH{1'b0}};
reg [1:0]                       wrdata_en_dly;

////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
///////////////////////////////////////////////////////////////////////////////

// Delay wrdata_en to align with error injection cycle.
// The delayed signal clears fi_xor_data in time to avoid injecting
// on multiple writes with a single fi_xor_we assertion.
wire [1:0] wrdata_en_dly_nxt = { wrdata_en_dly[0], wrdata_en };
always @(posedge clk) begin
  wrdata_en_dly <= #TCQ wrdata_en_dly_nxt;
end

// Register in the fi_xor_wrdata on a byte width basis
generate
begin
  genvar i;
  for (i = 0; i < DQS_WIDTH; i = i + 1) begin : assign_fi_xor_data
    always @(posedge clk) begin
      if (wrdata_en_dly[1]) begin
        fi_xor_data[i*DQ_PER_DQS+:DQ_PER_DQS] <= {DQ_PER_DQS{1'b0}};
      end
      else if (fi_xor_we[i]) begin
        fi_xor_data[i*DQ_PER_DQS+:DQ_PER_DQS] <= fi_xor_wrdata[i*DQ_PER_DQS+:DQ_PER_DQS];
      end 
      else begin
        fi_xor_data[i*DQ_PER_DQS+:DQ_PER_DQS] <= fi_xor_data[i*DQ_PER_DQS+:DQ_PER_DQS];
      end
    end
  end
  
end
endgenerate

localparam CBYTES_BURST0_LSB          = 2*nCK_PER_CLK*DATA_WIDTH;
localparam CBYTES_BURST1_LSB          = CBYTES_BURST0_LSB + ECC_WIDTH;
localparam CBYTES_BURST7TO1_WIDTH     = (2*nCK_PER_CLK-1)*ECC_WIDTH;
localparam DATA_BYTES_BURST7TO1_WIDTH = (2*nCK_PER_CLK-1)*DATA_WIDTH;

// Inject error on burst 0
assign wrdata_out[0+:DATA_WIDTH]                = wrdata_in[0+:DATA_WIDTH]                ^ fi_xor_data[0+:DATA_WIDTH];         // Data bytes of burst 0
assign wrdata_out[CBYTES_BURST0_LSB+:ECC_WIDTH] = wrdata_in[CBYTES_BURST0_LSB+:ECC_WIDTH] ^ fi_xor_data[DATA_WIDTH+:ECC_WIDTH]; // Check byte of burst 0
 
// Pass through bursts 1 thru 7
assign wrdata_out[DATA_WIDTH+:DATA_BYTES_BURST7TO1_WIDTH]    = wrdata_in[DATA_WIDTH+:DATA_BYTES_BURST7TO1_WIDTH];    // Data bytes burst 1 thru 7
assign wrdata_out[CBYTES_BURST1_LSB+:CBYTES_BURST7TO1_WIDTH] = wrdata_in[CBYTES_BURST1_LSB+:CBYTES_BURST7TO1_WIDTH]; // Check bytes burst 1 thru 7


//synopsys translate_off

`ifdef MEM_INTERNAL
// Events - When asserted high in a test that passes all verification checks, these coverage
//          properties indicate that a functional coverage event has been hit.
// ---------------------------------------------------------------------------------------------

//  Error injected
wire   e_mc_ecc_fi_000 = ( | fi_xor_data ) & wrdata_en;
always @(posedge clk) mc_ecc_fi_000: if (~rst) cover property (e_mc_ecc_fi_000);

// Asserts - When asserted high, an illegal condition has been detected and the test has failed.
// ---------------------------------------------------------------------------------------------

//  Error injection setup dropped
wire   a_mc_ecc_fi_000 = ( | fi_xor_we ) & wrdata_en;
always @(posedge clk) if (~rst) assert property (~a_mc_ecc_fi_000);


`endif

//synopsys translate_on

endmodule

`default_nettype wire

