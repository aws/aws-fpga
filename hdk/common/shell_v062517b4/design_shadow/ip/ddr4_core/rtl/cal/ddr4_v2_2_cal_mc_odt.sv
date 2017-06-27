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
//  /   /         Filename           : ddr4_v2_2_0_cal_mc_odt.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_0_cal_mc_odt module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_0_cal_mc_odt #(parameter
    ODTWR     = 16'h8421
   ,ODTWRDEL  = 5'd9
   ,ODTWRDUR  = 4'd6
   ,ODTWRODEL = 5'd9
   ,ODTWRODUR = 4'd6

   ,ODTRD     = 16'h0000
   ,ODTRDDEL  = 5'd9
   ,ODTRDDUR  = 4'd6
   ,ODTRDODEL = 5'd9
   ,ODTRDODUR = 4'd6

   ,ODTBITS   = 4
   ,ODTNOP    = 4'b0000
   ,TCQ       = 0.1
)(
    input clk
   ,input rst

   ,output [ODTBITS*8-1:0] mc_ODT

   ,input       casSlot2
   ,input [1:0] rank
   ,input       winRead
   ,input       winWrite
   ,input       tranSentC 
);

// ==========================================================================================
// ODT is a multi-fabric-cycle waveform that needs to assert on the same cycle as write CAS,
// and also on the same cycle as read CAS when tCL=tCWL.  This block generates the full
// multi-cycle ODT waveform in the same cycle that rdCAS or wrCAS is generated, bypassing
// the first 8 bits per ODT pin to mc_ODT combinationally, and flopping the remaining bits
// in a shift register which are then sent to the XiPhy 8 bits per pin per cycle.  If CAS
// commands are issued so that the current ODT waveform overlaps with the waveform from
// previous commands, the waveforms will be OR'd together.
// Note:  The original Olympus ODT block had separate timing for the selected rank and
// non-target ranks.  This version of the code does not support this.
// ==========================================================================================


// ==========================================================================================
// Signal Declarations
// ==========================================================================================

// Structures holding multi-fabric-cycle ODT pin waveforms for current CAS transaction
wire [31:0] odt_array    [ ODTBITS-1:0 ];
wire [31:0] odt_transent [ ODTBITS-1:0 ];

// Shift register holding ODT pin waveforms for previous CAS transactions
reg  [23:0] odt_shift    [ ODTBITS-1:0 ];
wire [23:0] odt_shift_nxt[ ODTBITS-1:0 ];

// ODT pin waveform for current fabric cycle, with time going from msb to lsb, reverse for XiPhy order
wire [ 7:0] odt_reverse  [ ODTBITS-1:0 ];


// ==========================================================================================
// Module Code
// ==========================================================================================

// Set up basic write ODT timing waveform.  Note that time increases moving from msb to lsb.
wire [31:0] odt_pulse_wr_slot0 = 32'hff_ff_ff_ff << (32 - 2*ODTWRDUR);
wire [31:0] odt_pulse_wr_slot2 = odt_pulse_wr_slot0 >> 4;

// Set up basic read ODT timing waveform.  Note that time increases moving from msb to lsb.
wire [31:0] odt_pulse_rd_slot0 = ( 32'hff_ff_ff_ff << (32 - 2*ODTRDDUR) ) >> ( 2*( ODTRDDEL - ODTWRDEL ) );
wire [31:0] odt_pulse_rd_slot2 = odt_pulse_rd_slot0 >> 4;

// Select ODT timing waveform based on winning command type and slot position
wire [31:0] win_odt_pulse_slot0 = winRead ? odt_pulse_rd_slot0 : odt_pulse_wr_slot0;
wire [31:0] win_odt_pulse_slot2 = winRead ? odt_pulse_rd_slot2 : odt_pulse_wr_slot2;
wire [31:0] win_odt_pulse       = casSlot2 ? win_odt_pulse_slot2 : win_odt_pulse_slot0;

// Select ODT pin pattern based on winning command type and rank
wire [15:0] win_odt_cmd_pat = winRead ? ODTRD : ODTWR;
wire [ 3:0] win_odt_pat     = { 4 { winRead | winWrite } } & win_odt_cmd_pat[ 4*rank +:4 ]; // spyglass disable W498

genvar odt_pin;
generate
   for (odt_pin = 0; odt_pin < ODTBITS; odt_pin = odt_pin + 1) begin
      // Combine selected waveform and pattern to generate full ODT output for the current winning CAS command
      assign odt_array[odt_pin]    = { 32 { win_odt_pat[ odt_pin ] } } & win_odt_pulse;

      // Qualify with tranSendC
      assign odt_transent[odt_pin] = { 32 { tranSentC } } & odt_array[ odt_pin ];

      // Parallel load lower 24 bits of qualified ODT output into shift register
      assign odt_shift_nxt[odt_pin] = odt_transent[odt_pin][23:0] | { odt_shift[odt_pin][15:0], 8'b0 };

      // Combine the upper 8 bits of the odt output for the new transaction (bypass path) with
      // the upper 8 bits of the shift register output to generate the odt block's output
      assign odt_reverse[odt_pin] = odt_transent[odt_pin][31:24] | odt_shift[odt_pin][23:16];

      // Reverse the msb/lsb order.  XiPhy wants increasing time going from lsb to msb
      assign mc_ODT[odt_pin*8+:8] = { odt_reverse[odt_pin][0], odt_reverse[odt_pin][1], odt_reverse[odt_pin][2], odt_reverse[odt_pin][3],
                                      odt_reverse[odt_pin][4], odt_reverse[odt_pin][5], odt_reverse[odt_pin][6], odt_reverse[odt_pin][7] };
   end
endgenerate


// ==========================================================================================
// Reset flops
// ==========================================================================================

integer i;
always @(posedge clk) begin
  if (rst) begin
    for (i = 0; i < ODTBITS; i = i + 1) begin
      odt_shift[i] <= #TCQ 28'b0;
    end
  end else begin
    for (i = 0; i < ODTBITS; i = i + 1) begin
      odt_shift[i] <= #TCQ odt_shift_nxt[i];
    end
  end
end

endmodule


