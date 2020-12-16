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
//  /   /         Filename           : ddr4_v2_2_10_cal_read.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_cal_read module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_10_cal_read # (parameter
   DBAW = 5
   ,DBYTES = 4
   ,RL     = 12
   ,EXTRA_CMD_DELAY = 0
   ,TCQ = 0.1
)(
    input clk
   ,input rst

   ,output reg [DBYTES*13-1:0]                   mc_clb2phy_fifo_rden_nxt
   ,output reg  [DBAW-1:0]                       rdDataAddr
   ,output                                       rdDataEn
   ,output                                       rdDataEnd
   ,output reg                                   rdInj
   ,output reg                                   rdRmw

   ,input                 mcrdCAS
   ,input                 calrdCAS
   ,input                 cal_clear_fifo_rden
   ,input                 calDone
   ,input                 winInjTxn
   ,input                 winRmw
   ,input      [DBAW-1:0] winBuf
   ,input      [6:0]      max_rd_lat
);


// ========================================================================
// Read Latency Timing.
// This section will use a FIFO and shift register to pop the XiPhy Rx FIFO
// a programmable number of fabric cycles after a rdCas pulse.  There will
// be a single delay from rdCas for all ranks.  The uB will calculate the
// the delay from Gate calibration results.
// ========================================================================

// FIFO to store read return information
// --------------------------------------

localparam READ_LAT_FIFO_WIDTH = DBAW + 2;
wire [4:0] read_lat_shift_rptr = ( max_rd_lat + 3 )/4 + 3 + EXTRA_CMD_DELAY; // spyglass disable W164a
wire       rdCAS_nxt           = mcrdCAS | ( calrdCAS & ~calDone );

reg  [READ_LAT_FIFO_WIDTH-1:0] read_lat_fifo     [31:0];
reg  [READ_LAT_FIFO_WIDTH-1:0] read_lat_fifo_nxt [31:0];
reg  [4:0]                     read_lat_rptr;
reg  [4:0]                     read_lat_wptr;
reg                            pop_read_lat_fifo;
reg                            rdCAS;
reg  [31:0]                    read_lat_shift;
reg                            read_lat_shift_cal_dq_valid;
reg                            read_data_en;
reg  [READ_LAT_FIFO_WIDTH-1:0] read_lat_fifo_in;

wire [READ_LAT_FIFO_WIDTH-1:0] read_lat_fifo_in_nxt = { winInjTxn, winRmw, winBuf };

always @(*) begin
  read_lat_fifo_nxt                  = read_lat_fifo;
  read_lat_fifo_nxt[ read_lat_wptr ] = read_lat_fifo_in;
end

wire [4:0] read_lat_wptr_nxt = cal_clear_fifo_rden ? '0 : ( read_lat_wptr + { 4'b0, rdCAS } ); // spyglass disable W164a
wire [4:0] read_lat_rptr_nxt = cal_clear_fifo_rden ? '0 : ( read_lat_rptr + { 4'b0, pop_read_lat_fifo } ); // spyglass disable W164a


assign          rdDataEnd = 1'b1;
wire [DBAW-1:0] rdDataAddr_nxt = read_lat_fifo[ read_lat_rptr ][READ_LAT_FIFO_WIDTH-3:0];
assign          rdDataEn       = read_data_en;
wire            rdRmw_nxt      = read_lat_fifo[ read_lat_rptr ][READ_LAT_FIFO_WIDTH-2];
wire            rdInj_nxt      = read_lat_fifo[ read_lat_rptr ][READ_LAT_FIFO_WIDTH-1];


// Shift register to time when the XiPhy Rx FIFO should be popped
// ---------------------------------------------------------------

wire [31:0] read_lat_shift_nxt = { read_lat_shift[30:0], rdCAS };
wire        read_lat_shift_cal_dq_valid_nxt = read_lat_shift[ read_lat_shift_rptr ];
wire        pop_read_lat_fifo_nxt           = read_lat_shift_cal_dq_valid;
wire        read_data_en_nxt                = pop_read_lat_fifo;



always @(posedge clk) begin
  if (rst) begin
    read_lat_rptr  <= #TCQ '0;
    read_lat_wptr  <= #TCQ '0;
    read_lat_shift <= #TCQ '0;
  end
  else begin
    read_lat_rptr  <= #TCQ read_lat_rptr_nxt;
    read_lat_wptr  <= #TCQ read_lat_wptr_nxt;
    read_lat_shift <= #TCQ read_lat_shift_nxt;
  end
end

always @(posedge clk) begin
  read_lat_fifo               <= #TCQ read_lat_fifo_nxt;
  read_lat_shift_cal_dq_valid <= #TCQ read_lat_shift_cal_dq_valid_nxt;
  read_data_en                <= #TCQ read_data_en_nxt;
  rdDataAddr                  <= #TCQ rdDataAddr_nxt;
  rdRmw                       <= #TCQ rdRmw_nxt;
  rdInj                       <= #TCQ rdInj_nxt;
  pop_read_lat_fifo           <= #TCQ pop_read_lat_fifo_nxt;
  mc_clb2phy_fifo_rden_nxt    <= #TCQ { DBYTES*13 { read_lat_shift_cal_dq_valid_nxt } };
  rdCAS                       <= #TCQ rdCAS_nxt;
  read_lat_fifo_in            <= #TCQ read_lat_fifo_in_nxt;
end

// Assertions
// =================
//synthesis translate_off

`ifdef MEM_INTERNAL

// Check for read_lat_shift_rptr overflow
wire  a_mc_read_lat_rptr_ovf = ( max_rd_lat + 3 )/4 + 3 + EXTRA_CMD_DELAY > 31;
always @(posedge clk) if (~rst) assert property (~a_mc_read_lat_rptr_ovf);

`endif
//synthesis translate_on

endmodule


