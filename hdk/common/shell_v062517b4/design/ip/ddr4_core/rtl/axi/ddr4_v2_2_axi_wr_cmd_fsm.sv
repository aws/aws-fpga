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
//  /   /         Filename           : ddr4_v2_2_0_axi_wr_cmd_fsm.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 17 2014
//  \___\/\___\
//
//Device: UltraScale
//Design Name: AXI Slave
//Purpose:
// Description: 
// Simple state machine to handle sending commands from AXI to MC.  The flow:
// 1. A transaction can only be initiaited when axvalid is true and data_rdy
// is true.  For writes, data_rdy means that  one completed BL8 or BL4 write 
// data has been pushed into the MC write FIFOs.  For read operations,
// data_rdy indicates that there is enough room to push the transaction into
// the read FIF & read transaction fifo in the shim.  If the FIFO's in the 
// read channel module is full, then the state machine waits for the 
// FIFO's to drain out. 
//
// 2. When CMD_EN is asserted, it remains high until we sample CMD_FULL in
// a low state.  When CMD_EN == 1'b1, and CMD_FULL == 1'b0, then the command
// has been accepted.  When the command is accepted, if the next_pending
// signal is high we will incremented to the next transaction and issue the
// cmd_en again when data_rdy is high.  Otherwise we will go to the done
// state.
//
// 3. The AXI transaction can only complete when b_full is not true (for writes)
// and no more mc transactions need to be issued.  The AXREADY will be
// asserted and the state machine will progress back to the the IDLE state.
// 
///////////////////////////////////////////////////////////////////////////////
//Reference:
//Revision History:
//*****************************************************************************
`timescale 1ps/1ps
`default_nettype none

module ddr4_v2_2_0_axi_wr_cmd_fsm #(
///////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
///////////////////////////////////////////////////////////////////////////////
                        // MC burst length. = 1 for BL4 or BC4, = 2 for BL8
  parameter integer C_MC_BURST_LEN              = 1,
                     // parameter to identify rd or wr instantation
                     // = 1 rd , = 0 wr 
  parameter integer C_MC_RD_INST              = 0
  
)
(
///////////////////////////////////////////////////////////////////////////////
// Port Declarations     
///////////////////////////////////////////////////////////////////////////////
  input  wire                                 clk           , 
  input  wire                                 reset         , 
  output reg                                  axready       , 
  input  wire                                 axvalid       , 
  output wire                                 cmd_en        , 
  input  wire                                 cmd_full      , 
  // signal to increment to the next mc transaction 
  output wire                                 next          , 
  // signal to the fsm there is another transaction required
  input  wire                                 next_pending  ,
  // Write Data portion has completed or Read FIFO has a slot available (not
  // full)
  input  wire                                 data_rdy    ,
  // status signal for w_channel when command is written. 
  output wire                                 b_push        ,
  input  wire                                 b_full        ,
  output wire                                 cmd_en_last   
);

////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
///////////////////////////////////////////////////////////////////////////////
    assign cmd_en = (~b_full & axvalid & data_rdy);

    assign next = (~cmd_full & cmd_en);

    assign cmd_en_last = next & ~next_pending;

    assign b_push  = cmd_en_last;

  always @(posedge clk) begin
    if (reset)
      axready <= 1'b0;
    else
      axready <= ~axvalid | cmd_en_last;
  end

endmodule
`default_nettype wire

