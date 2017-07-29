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
//  /   /         Filename           : ddr4_v2_2_0_axi_r_channel.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 17 2014
//  \___\/\___\
//
//Device: UltraScale 
//Design Name: AXI Slave
//Purpose:
// Description: 
// Read data channel module to buffer read data from MC, ignore 
// extra data in case of BL8 and send the data to AXI.
// The MC will send out the read data as it is ready and it has to be 
// accepted. The read data FIFO in the axi_mc_r_channel module will buffer 
// the data before being sent to AXI. The address channel module will
// send the transaction information for every command that is sent to the 
// MC. The transaction information will be buffered in a transaction FIFO.
// Based on the transaction FIFO information data will be ignored in
// BL8 mode and the last signal to the AXI will be asserted. 
///////////////////////////////////////////////////////////////////////////////
//Reference:
//Revision History:
//*****************************************************************************
`timescale 1ps/1ps
`default_nettype none

module ddr4_v2_2_0_axi_r_channel #
(
///////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
///////////////////////////////////////////////////////////////////////////////
                    // Width of ID signals.
                    // Range: >= 1.
  parameter integer C_ID_WIDTH                = 4, 
                    // Width of AXI xDATA and MCB xx_data
                    // Range: 32, 64, 128.
  parameter integer C_DATA_WIDTH              = 32,
                        // MC burst length. = 1 for BL4 or BC4, = 2 for BL8
  parameter integer C_MC_BURST_LEN              = 1,
                    // axi addr width 
  parameter integer C_AXI_ADDR_WIDTH            = 32,
                    // Number of memory clocks per fabric clock
                    // = 2 for DDR2 or low frequency designs
                    // = 4 for DDR3 or high frequency designs 
  parameter         C_MC_nCK_PER_CLK            = 2,
                    // memory controller burst mode,
                    // values "8", "4" & "OTF"
  parameter         C_MC_BURST_MODE             = "8" 
)
(
///////////////////////////////////////////////////////////////////////////////
// Port Declarations     
///////////////////////////////////////////////////////////////////////////////
  input  wire                                 clk              , 
  input  wire                                 reset            , 

  output wire  [C_ID_WIDTH-1:0]               rid              , 
  output wire  [C_DATA_WIDTH-1:0]             rdata            , 
  output wire [1:0]                           rresp            , 
  output wire                                 rlast            , 
  output wire                                 rvalid           , 
  input  wire                                 rready           , 

  input  wire [C_DATA_WIDTH-1:0]              mc_app_rd_data   , 
  input  wire                                 mc_app_rd_valid  , 
  input  wire                                 mc_app_rd_last   , 
  input  wire                                 mc_app_ecc_multiple_err ,

  // Connections to/from axi_mc_ar_channel module
  input  wire                                 r_push           ,
  output wire                                 r_data_rdy           , 
  // length not needed. Can be removed. 
  input  wire [C_ID_WIDTH-1:0]                r_arid           , 
  input  wire                                 r_rlast          ,
  input  wire                                 r_ignore_begin   ,
  input  wire                                 r_ignore_end   

);

////////////////////////////////////////////////////////////////////////////////
// Local parameters
////////////////////////////////////////////////////////////////////////////////
localparam P_WIDTH = 3+C_ID_WIDTH;
localparam P_DEPTH = 30;
localparam P_AWIDTH = 5;
localparam P_D_WIDTH = C_DATA_WIDTH+1;
// rd data FIFO depth varies based on burst length.
// For Bl8 it is two times the size of transaction FIFO.
// Only in 2:1 mode BL8 transactions will happen which results in
// two beats of read data per read transaction. 
localparam P_D_DEPTH  = (C_MC_BURST_LEN == 2)? 64 : 32;
localparam P_D_AWIDTH = (C_MC_BURST_LEN == 2)? 6: 5;
 
// AXI protocol responses:
localparam P_OKAY   = 2'b00;
localparam P_EXOKAY = 2'b01;
localparam P_SLVERR = 2'b10;
localparam P_DECERR = 2'b11;

////////////////////////////////////////////////////////////////////////////////
// Wire and register declarations
////////////////////////////////////////////////////////////////////////////////
   
wire                       done;
wire [C_ID_WIDTH+3-1:0]    trans_in;
wire [C_ID_WIDTH+3-1:0]    trans_out;
reg  [C_ID_WIDTH+3-1:0]    trans_buf_out_r1;
reg  [C_ID_WIDTH+3-1:0]    trans_buf_out_r;
wire                       tr_empty;
wire                       tr_rden;
reg [1:0]                  state;
wire [C_ID_WIDTH-1:0]      rid_i;
wire                       assert_rlast;
wire                       ignore_begin;
wire                       ignore_end;
reg                        load_stage1;
wire                       load_stage2;
wire                       load_stage1_from_stage2;

wire                       rhandshake;
wire                       rlast_i;
wire                       r_valid_i;
wire [C_DATA_WIDTH:0]      rd_data_fifo_in;
wire [C_DATA_WIDTH:0]      rd_data_fifo_out; 
wire                       rd_en; 
wire                       rd_full;
wire                       rd_empty;  
wire                       rd_a_full;
reg                        rd_last_r;
wire                       fifo_rd_last;
wire                       trans_a_full;
wire                       trans_full;

reg                        r_ignore_begin_r;
reg                        r_ignore_end_r;
wire                       fifo_full;

////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
////////////////////////////////////////////////////////////////////////////////


// localparam for 2 deep skid buffer
localparam [1:0] 
  ZERO = 2'b10,
  ONE  = 2'b11,
  TWO  = 2'b01;

assign rresp  = (rd_data_fifo_out[C_DATA_WIDTH] == 'd1) ? P_SLVERR : P_OKAY; 
assign rid    = rid_i;
assign rdata  = rd_data_fifo_out[C_DATA_WIDTH-1:0];
assign rlast  = assert_rlast & ((~fifo_rd_last & ignore_end) 
                          |  (fifo_rd_last & ~ignore_end));
assign rvalid = ~rd_empty & ((~fifo_rd_last & ~ignore_begin)
                                 | (fifo_rd_last & ~ignore_end ));

// assign MCB outputs
assign rd_en      = rhandshake & (~rd_empty);

assign rhandshake =(rvalid & rready) |
(((~fifo_rd_last & ignore_begin) | (fifo_rd_last & ignore_end )) & (~rd_empty));

// register for timing 
always @(posedge clk) begin
  r_ignore_begin_r <= r_ignore_begin;
  r_ignore_end_r <= r_ignore_end;
end

assign trans_in[0]  = r_ignore_end_r;
assign trans_in[1]  = r_ignore_begin_r;
assign trans_in[2]  = r_rlast;
assign trans_in[3+:C_ID_WIDTH]  = r_arid;

always @(posedge clk) begin
  if (reset) begin
     rd_last_r <= 1'b0;
  end else if (rhandshake) begin
     rd_last_r <= ~rd_last_r;
  end
end   
   
assign fifo_rd_last = (C_MC_BURST_LEN == 1) ? 1'b1 : rd_last_r;
   
// rd data fifo
ddr4_v2_2_0_axi_fifo #
  (
  .C_WIDTH                (P_D_WIDTH),
  .C_AWIDTH               (P_D_AWIDTH),
  .C_DEPTH                (P_D_DEPTH)
)
rd_data_fifo_0
(
  .clk     ( clk              ) ,
  .rst     ( reset            ) ,
  .wr_en   ( mc_app_rd_valid  ) ,
  .rd_en   ( rd_en            ) ,
  .din     ( rd_data_fifo_in  ) ,
  .dout    ( rd_data_fifo_out ) ,
  .a_full  ( rd_a_full        ) ,
  .full    ( rd_full          ) ,
  .a_empty (                  ) ,
  .empty   ( rd_empty         ) 
);

assign rd_data_fifo_in = {mc_app_ecc_multiple_err, mc_app_rd_data};


ddr4_v2_2_0_axi_fifo #
  (
  .C_WIDTH                  (P_WIDTH),
  .C_AWIDTH                 (P_AWIDTH),
  .C_DEPTH                  (P_DEPTH)
)
transaction_fifo_0
(
  .clk     ( clk         ) ,
  .rst     ( reset       ) ,
  .wr_en   ( r_push      ) ,
  .rd_en   ( tr_rden     ) ,
  .din     ( trans_in    ) ,
  .dout    ( trans_out   ) ,
  .a_full  ( trans_a_full) ,
  .full    ( trans_full  ) ,
  .a_empty (             ) ,
  .empty   ( tr_empty    ) 
);

assign rid_i = trans_buf_out_r[3+:C_ID_WIDTH];
assign assert_rlast = trans_buf_out_r[2];
assign ignore_begin = trans_buf_out_r[1];
assign ignore_end   = trans_buf_out_r[0];

assign done = fifo_rd_last & rhandshake;
assign fifo_full = (trans_a_full | trans_full) | (rd_a_full | rd_full);
assign r_data_rdy = ~fifo_full ; 

// logic for 2 deep skid buffer for storing transaction data for timing

// loading the output of the buffer 
always @(posedge clk) begin
  if(load_stage1)
    if(load_stage1_from_stage2)
      trans_buf_out_r <= trans_buf_out_r1;
    else
      trans_buf_out_r <= trans_out;        
end

// store data into the optional second stage 
always @(posedge clk) begin
  if(load_stage2)
    trans_buf_out_r1 <= trans_out;
end


// condition to store data for the second stage 
assign load_stage2 = ~tr_empty & state[1];

// Loading stage one conditions 
always @ (*) begin
  if( ((state == ZERO) && (~tr_empty)) ||
    ((state == ONE) && (~tr_empty) && (done)) ||
    ((state == TWO) && (done)))
    load_stage1 = 1'b1;
  else
    load_stage1 = 1'b0;
end // always @ *

assign load_stage1_from_stage2 = (state == TWO);
                       
always @(posedge clk) 
begin
if(reset) 
  state <= ZERO;
else
  state <= state; 
  case (state)
    ZERO: if (~tr_empty) state <= ONE; 
    ONE: begin
      if (done & tr_empty) state <= ZERO; 
      if (~done & (~tr_empty)) state <= TWO;  
    end
    TWO: if (done) state <= ONE; 
    default : state <= ZERO ;
  endcase
end 

assign tr_rden = ((state == ZERO) || (state == ONE)) && (~tr_empty);

endmodule
`default_nettype wire

