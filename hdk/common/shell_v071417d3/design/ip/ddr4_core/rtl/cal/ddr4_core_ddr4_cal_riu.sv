
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
// \   \   \/     Version            : 1.0
//  \   \         Application        : MIG
//  /   /         Filename           : ddr4_cal_riu.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/05 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4_SDRAM
// Purpose          :
//                   ddr4_cal_riu module
// Reference        :
// Revision History :
//*****************************************************************************
`ifdef MODEL_TECH
    `ifndef CALIB_SIM
       `define SIMULATION
     `endif
`elsif INCA
    `ifndef CALIB_SIM
       `define SIMULATION
     `endif
`elsif VCS
    `ifndef CALIB_SIM
       `define SIMULATION
     `endif
`elsif XILINX_SIMULATOR
    `ifndef CALIB_SIM
       `define SIMULATION
     `endif
`endif
`timescale 1ps/1ps

module  ddr4_core_ddr4_cal_riu #
  (
   parameter real    TCQ                     = 100,
   parameter       MCS_ECC_ENABLE             = "FALSE" // MCS ECC enable 
)
  (
   input                          riu_clk
   ,input                          riu_clk_rst

   ,input   [15:0] riu2clb_vld_read_data
   ,input   [7:0] riu_nibble_8
   ,input [5:0]                    riu_addr_cal


   ,input [31:0] io_read_data_riuclk
   ,input        io_ready_lvl_riuclk


   ,input fab_rst_sync

   ,input reset_ub_riuclk



   ,(* dont_touch = "true" *) output  io_addr_strobe_clb2riu_riuclk
   ,(* dont_touch = "true" *) output reg io_addr_strobe_lvl_riuclk = 1'b0
   ,(* dont_touch = "true" *) output reg [31:0] io_address_riuclk
   ,(* dont_touch = "true" *) output reg [31:0] io_write_data_riuclk
   ,(* dont_touch = "true" *) output reg        io_write_strobe_riuclk = 1'b0

   ,output reg ub_rst_out_riuclk
   ,(* dont_touch = "true" *) output LMB_UE //MCS Local Memory Uncorrectable Error
   ,(* dont_touch = "true" *) output LMB_CE //MCS Local Memory Correctable Error

   ,input  [20-1:0] riu2clb_valid_riuclk // max number of bytes possible
   ,(* dont_touch = "true" *) output reg [20-1:0] riu2clb_valid_r1_riuclk // max number of bytes possible

);


//Microblaze MCS I/O module
wire [31:0] io_address_ub;
wire        io_addr_strobe_ub;
wire        io_addr_strobe_ub_vld;
reg         io_addr_strobe_ub_hold;
wire [31:0] io_write_data_ub;
wire        io_write_strobe_ub;
wire [31:0] io_read_data_mux;


reg        io_addr_strobe_vld_riuclk;
reg [31:0] io_read_data_ub;
reg        io_ready_ub;

wire [31:0] Trace_PC;

wire riu_access;

wire ub_rst_adr_hit;




//######################## RIU Clock Domain ########################


reg io_ready_riuclk;
reg io_ready_lvl_riuclk_r1;
reg io_ready_lvl_riuclk_r2;
 reg io_addr_strobe_riuclk;
assign	io_addr_strobe_clb2riu_riuclk = io_addr_strobe_riuclk && riu_access;

// IO Ready Level to Pulse conversion
  always @(posedge riu_clk) begin
    io_ready_lvl_riuclk_r1 <= #TCQ io_ready_lvl_riuclk;
    io_ready_lvl_riuclk_r2 <= #TCQ io_ready_lvl_riuclk_r1;
    io_ready_riuclk <= #TCQ io_ready_lvl_riuclk_r1 ^ io_ready_lvl_riuclk_r2;
  end
// Check the RIU and Fabric resets and hold the Microblaze transactions until they are released.
reg [15:0] fab_riu_rst_pipe;
wire fab_riu_rst = |fab_riu_rst_pipe;

(* keep = "TRUE" *) reg riu_clk_rst_r1;

always @(posedge riu_clk)
  riu_clk_rst_r1 <= riu_clk_rst;

always @(posedge riu_clk)
  fab_riu_rst_pipe <= #TCQ {fab_riu_rst_pipe, (riu_clk_rst_r1 | fab_rst_sync)};

assign io_addr_strobe_ub_vld = fab_riu_rst ? 1'b0 : (io_addr_strobe_ub | io_addr_strobe_ub_hold);

always @(posedge riu_clk) begin
  if(reset_ub_riuclk)
    io_addr_strobe_ub_hold <= #TCQ 1'b0;
  else if(fab_riu_rst & io_addr_strobe_ub)
    io_addr_strobe_ub_hold <= #TCQ 1'b1;
  else if(~fab_riu_rst)
    io_addr_strobe_ub_hold <= #TCQ 1'b0;
end

  always @(posedge riu_clk) begin
    io_address_riuclk <= #TCQ io_address_ub[29:2];
    io_addr_strobe_riuclk <= #TCQ io_addr_strobe_ub;
    io_addr_strobe_vld_riuclk <= #TCQ io_addr_strobe_ub_vld;
    io_write_data_riuclk <= #TCQ io_write_data_ub;

    if(io_addr_strobe_ub)
      io_write_strobe_riuclk <= #TCQ io_write_strobe_ub;
  end

  always @(posedge riu_clk) begin // PS Level
    if(io_addr_strobe_vld_riuclk & ~riu_access & ~ub_rst_adr_hit)
      io_addr_strobe_lvl_riuclk <= #TCQ ~io_addr_strobe_lvl_riuclk;
  end

// Special register to reset the cal logic except the uB!
assign ub_rst_adr_hit = (io_address_riuclk == 28'h0020002);

always @(posedge riu_clk) begin
   if (reset_ub_riuclk)
     ub_rst_out_riuclk <= #TCQ 1'b0;
   else if (io_addr_strobe_riuclk && io_write_strobe_riuclk && ub_rst_adr_hit)
     ub_rst_out_riuclk <= #TCQ io_write_data_riuclk[0];
end

//-----------------------------------------------------------------------------
// Microblaze MCS core instantiation
//-----------------------------------------------------------------------------
// For non-calibration simulation, Microblaze mcs static netlist will be used. 
// This part of code will be used only for non-calibration simulation.
// Don't add/remove the i/o ports or parameters from the SIMULATION section of 
// code, since it doe not affect the functionality.
//-----------------------------------------------------------------------------
  `ifndef ENABLE_MICROBLAZE_BFM
    // Microblaze MCS core without ECC
    //MCS V3.0 instance
ddr4_core_microblaze_mcs  mcs0 (
      .Clk                (riu_clk),
      .Reset              (reset_ub_riuclk),
      .IO_addr_strobe     (io_addr_strobe_ub),
      .IO_read_strobe     (),
      .IO_write_strobe    (io_write_strobe_ub),
      .IO_address         (io_address_ub),
      .IO_byte_enable     (),
      .IO_write_data      (io_write_data_ub),
      .IO_read_data       (io_read_data_ub),
      .IO_ready           (io_ready_ub),
      .TRACE_pc           (Trace_PC)
    );
    assign LMB_UE = 1'b0;
    assign LMB_CE = 1'b0;
  `endif

//-----------------------------------------------------------------------------

  assign riu_access       = (~io_address_riuclk[23]) & (io_address_riuclk[12] | io_address_riuclk[13] | io_address_riuclk[14] | io_address_riuclk[15] | io_address_riuclk [16] ) & (~io_address_riuclk[21]) &(~io_address_riuclk[22]);

  
  assign io_read_data_mux = riu_access ? {2'b0, riu_addr_cal[5:0], riu_nibble_8[7:0], riu2clb_vld_read_data} : io_read_data_riuclk;

  always @(posedge riu_clk) begin
    io_read_data_ub <= #TCQ io_read_data_mux;
  end

// wait until riu write finished
reg any_clb2riu_wr_wait = 0;
reg riu_rd_val;
reg riu_rd_val_r;
reg riu_rd_val_r1;
reg riu_rd_val_r2;

reg any_clb2riu_wr_en;
always @(posedge riu_clk) begin
    any_clb2riu_wr_en <= #TCQ io_addr_strobe_vld_riuclk && riu_access && io_write_strobe_riuclk;
end
always @(posedge riu_clk) begin
   if (reset_ub_riuclk)
     any_clb2riu_wr_wait <= 0;
   else if (any_clb2riu_wr_en)	// MAN - replaced clb2riu_wr_en
     any_clb2riu_wr_wait <= 1;
   else if ((any_clb2riu_wr_wait && (&riu2clb_valid_riuclk)) || io_ready_ub)
     any_clb2riu_wr_wait <= 0;
end


  always @ (posedge riu_clk) begin
    if (ub_rst_adr_hit) // Microblaze reset access
      io_ready_ub <= #TCQ io_addr_strobe_riuclk;
    else if (riu_access && any_clb2riu_wr_wait) // RIU Write
      io_ready_ub <= #TCQ &riu2clb_valid_riuclk;
    else if (riu_access) // RIU Read
      io_ready_ub <= #TCQ riu_rd_val_r2;
    else
      io_ready_ub <= #TCQ io_ready_riuclk;
  end

  //used for generation io ready for RIU read (data become valid after one clock of nibble sel)
  always @ (posedge riu_clk) begin
    riu_rd_val <= #TCQ  io_addr_strobe_vld_riuclk & ~io_write_strobe_riuclk;
    riu_rd_val_r <= #TCQ  riu_rd_val;
    riu_rd_val_r1 <= #TCQ  riu_rd_val_r;
    riu_rd_val_r2 <= #TCQ  riu_rd_val_r1;
  end


  always @ (posedge riu_clk) begin
    riu2clb_valid_r1_riuclk <= #TCQ riu2clb_valid_riuclk;
    end

endmodule
