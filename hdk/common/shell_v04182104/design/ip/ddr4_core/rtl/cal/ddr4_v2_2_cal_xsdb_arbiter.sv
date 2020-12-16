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
//  /   /         Filename           : ddr4_v2_2_10_cal_xsdb_arbiter.sv
// /___/   /\     Date Last Modified : $Date: 2016/01/11 $
// \   \  /  \    Date Created       : Mon Jan 11 2016
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                  An arbiter between the XSDB slave interface and external self-refresh XSDB interface
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ps/1ps

module ddr4_v2_2_10_cal_xsdb_arbiter #(

  parameter SYNC_MTBF = 2,
  parameter TCQ       = 100
)(

  // Slave interface
  input         slave_clk,
  input         slave_en, 
  input         slave_we,
  input [15:0]  slave_addr,
  input [15:0]  slave_di,
  output [15:0] slave_do,
  output reg    slave_rdy,

  // External interface
  input         fabric_clk,
  input         fabric_rst,
  input         user_en,
  input         user_we,
  input [15:0]  user_addr,
  input [8:0]   user_di,
  output [8:0]  user_do,
  output        user_rdy,

  // Interface with the BRAM
  output            bram_clk,
  output reg        bram_en,
  output reg        bram_we,
  output reg [15:0] bram_addr,
  output reg [8:0]  bram_di,
  input [8:0]  bram_do,
  input         bram_rdy
);

// Wire declarations
(* dont_touch = "true" *) reg         slave_en_lvl = 1'b0;
wire        slave_cmd_en;
reg         slave_cmd_en_r;
(* dont_touch = "true" *) reg         slave_we_r;
(* dont_touch = "true" *) reg  [15:0] slave_addr_r;
(* dont_touch = "true" *) reg  [8:0]  slave_di_r;
reg         user_cmd_en_r;
reg         user_cmd_en;
reg         user_we_r;
reg  [15:0] user_addr_r;
reg  [8:0]  user_di_r;
wire        slave_we_fclk;
wire [15:0] slave_addr_fclk;
wire [8:0]  slave_di_fclk;
wire        slave_en_lvl_fclk;
reg         slave_en_lvl_fclk_r1;
reg         slave_en_lvl_fclk_r2;
reg         slave_en_fclk;
reg         user_cmd_pend;
reg         user_cmd_sent;
reg         bram_busy;

wire slave_rdy_fclk;
reg  slave_rdy_fclk_r;
(* dont_touch = "true" *) reg  slave_rdy_lvl_fclk;
wire slave_rdy_lvl_sclk;
reg  slave_rdy_lvl_sclk_r1;
reg  slave_rdy_lvl_sclk_r2;
(* dont_touch = "true" *) reg [8:0] slave_do_fclk;
reg [8:0] slave_do_sclk;
reg  slave_rdy_r;
(* dont_touch = "true" *) reg  slave_rdy_cptd_sclk;
wire slave_rdy_cptd_fclk;

localparam INSERT_DELAY = 0; // Insert delay for simulations
localparam MAX_DELAY_FABRIC = 3000; // Fabric Clock Max frequency 333MHz
localparam MAX_DELAY_DBGHUB = 12000; // Debug hub clock (dbg_clk) Max frequency 333MHz/4

// clock BRAM is fabric clock
assign bram_clk = fabric_clk;

// Generate command enables from slave and user interfaces
assign slave_cmd_en = (slave_en | slave_we);
assign user_cmd_en  = (user_en | user_we);

// Latching the input signals in their clock domain
always @(posedge slave_clk)
begin
  slave_cmd_en_r <= #TCQ slave_cmd_en;
  slave_addr_r   <= #TCQ slave_addr;
  slave_di_r     <= #TCQ slave_di[8:0];
  slave_rdy_r    <= #TCQ slave_rdy;
  if (~slave_cmd_en_r && slave_cmd_en)
    slave_we_r   <= #TCQ slave_we;
end
always @(posedge fabric_clk)
begin
  user_cmd_en_r <= #TCQ user_cmd_en;
  user_addr_r   <= #TCQ user_addr;
  user_di_r     <= #TCQ user_di;
  if (~user_cmd_en_r & user_cmd_en)
    user_we_r   <= #TCQ user_we;
end

// converting the input slave_en from pulse to level signal
always @(posedge slave_clk)
begin
  if (~slave_cmd_en_r && slave_cmd_en)
    slave_en_lvl <= #TCQ ~slave_en_lvl;
end

// Converting the slave xsdb signals to fabric clock domain
ddr4_v2_2_10_cal_sync #(SYNC_MTBF, 1, INSERT_DELAY, MAX_DELAY_FABRIC, TCQ) u_slave_en_sync (fabric_clk, slave_en_lvl, slave_en_lvl_fclk);
ddr4_v2_2_10_cal_sync #(SYNC_MTBF, 1, INSERT_DELAY, MAX_DELAY_FABRIC, TCQ) u_slave_we_sync (fabric_clk, slave_we_r, slave_we_fclk);
ddr4_v2_2_10_cal_sync #(SYNC_MTBF, 16, INSERT_DELAY, MAX_DELAY_FABRIC, TCQ) u_slave_addr_sync (fabric_clk, slave_addr_r, slave_addr_fclk);
ddr4_v2_2_10_cal_sync #(SYNC_MTBF, 9, INSERT_DELAY, MAX_DELAY_FABRIC, TCQ) u_slave_di_sync (fabric_clk, slave_di_r, slave_di_fclk);
ddr4_v2_2_10_cal_sync #(SYNC_MTBF, 1, INSERT_DELAY, MAX_DELAY_FABRIC, TCQ) u_slave_rdy_cptd_sync (fabric_clk, slave_rdy_cptd_sclk, slave_rdy_cptd_fclk);

//converting the xsdb_en level signal to pulse
always @(posedge fabric_clk)
begin
  slave_en_lvl_fclk_r1 <= #TCQ slave_en_lvl_fclk;
  slave_en_lvl_fclk_r2 <= #TCQ slave_en_lvl_fclk_r1;
  slave_en_fclk        <= #TCQ slave_en_lvl_fclk_r2 ^ slave_en_lvl_fclk_r1;
end

always @(posedge fabric_clk)
begin
  if (fabric_rst)
    user_cmd_pend <= #TCQ 1'b0;
  else if (~user_cmd_en_r & user_cmd_en)
    user_cmd_pend <= #TCQ 1'b1;
  else if (user_rdy)
    user_cmd_pend <= #TCQ 1'b0;
end

always @(posedge fabric_clk)
begin
  if (fabric_rst)
    bram_busy <= #TCQ 1'b0;
  else if (slave_en_fclk)
    bram_busy <= #TCQ 1'b1;
  else if (slave_rdy_cptd_fclk)
    bram_busy <= #TCQ 1'b0;
end

always @(posedge fabric_clk)
begin
  if (fabric_rst) begin
    bram_en   <= #TCQ 1'b0;
    bram_we   <= #TCQ 1'b0;
    bram_addr <= #TCQ 16'b0;
    bram_di   <= #TCQ 9'b0;
    user_cmd_sent <= #TCQ 1'b0;
  end else begin
    bram_en   <= #TCQ 1'b0;
    if (slave_en_fclk) begin
      bram_en   <= #TCQ 1'b1;
      bram_we   <= #TCQ slave_we_fclk;
      bram_addr <= #TCQ slave_addr_fclk;
      bram_di   <= #TCQ slave_di_fclk;
      user_cmd_sent <= #TCQ 1'b0;
    end else if (user_cmd_pend && ~bram_busy & ~user_cmd_sent) begin
      bram_en   <= #TCQ 1'b1;
      bram_we   <= #TCQ user_we_r;
      bram_addr <= #TCQ user_addr_r;
      bram_di   <= #TCQ user_di_r;
      user_cmd_sent <= #TCQ 1'b1;
    end else if (user_rdy) begin
      user_cmd_sent <= #TCQ 1'b0;
    end
  end
end

assign user_rdy = bram_rdy & user_cmd_sent;
assign user_do  = bram_do;

assign slave_rdy_fclk = bram_rdy & ~user_cmd_sent;
always @(posedge fabric_clk) begin
    if (fabric_rst) begin
      slave_rdy_lvl_fclk <= #TCQ 1'b0;
    end else begin
      if (~slave_rdy_fclk_r && slave_rdy_fclk)
        slave_rdy_lvl_fclk <= #TCQ 1'b1;
      else if (slave_rdy_cptd_fclk)
        slave_rdy_lvl_fclk <= #TCQ 1'b0;
    end

    slave_rdy_fclk_r <= #TCQ slave_rdy_fclk;

    // Latching the bram data when slave rdy is asserted
    if (slave_rdy_fclk) begin
      slave_do_fclk <= #TCQ bram_do;
    end
end

// Converting the fabic xsdb ready into slave clock domain
ddr4_v2_2_10_cal_sync #(SYNC_MTBF, 1, INSERT_DELAY, MAX_DELAY_DBGHUB, TCQ) u_slave_rdy_sync (slave_clk, slave_rdy_lvl_fclk, slave_rdy_lvl_sclk);
ddr4_v2_2_10_cal_sync #(SYNC_MTBF, 9, INSERT_DELAY, MAX_DELAY_DBGHUB, TCQ) u_slave_do_sync (slave_clk, slave_do_fclk, slave_do_sclk);

assign slave_do = {7'b0,slave_do_sclk};
always @(posedge slave_clk)
begin
  slave_rdy_lvl_sclk_r1 <= #TCQ slave_rdy_lvl_sclk;
  slave_rdy_lvl_sclk_r2 <= #TCQ slave_rdy_lvl_sclk_r1;

  if (slave_rdy_lvl_sclk_r1 && ~slave_rdy_lvl_sclk_r2) begin
    slave_rdy <= 1'b1;
    slave_rdy_cptd_sclk <= 1'b1;
  end else begin
    slave_rdy <= 1'b0;
    slave_rdy_cptd_sclk <= 1'b0;
  end
end

endmodule


