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
//  /   /         Filename           : ddr4_v2_2_10_mc_act_rank.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_mc_act_rank module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_10_mc_act_rank #(parameter
    tFAW   = 500
   ,tFAW_dlr = 500
   ,tRRD_L = 500
   ,tRRD_S = 500
   ,tRRD_dlr = 500
   ,TWO_GROUP_DDR4 = "FALSE"
   ,S_HEIGHT = 1
   ,LR_WIDTH = 1
   ,TCQ    = 0.1
)(
    input clk
   ,input rst

   ,output           fawOK
   ,output reg [3:0] rrdOK
   
   ,input [3:0] actReq
   ,input       update
   ,input [LR_WIDTH-1:0] winLRank_nxt
   ,input       act_rank_update
   ,input [4*LR_WIDTH-1:0] cmdLRank
   ,input [1:0] winGr
   ,input [1:0] winGr2
   ,input [LR_WIDTH-1:0] winLRank
   ,input [3:0] winPort
);

localparam
    S           = ((tRRD_S + 3) / 4) - 1               // tRRD_S minus 1 for scheduler pipeline
   ,S_pipe      = (S>0) ? S-1 : 0                      // tRRD_S timer load value
   ,L           = ((tRRD_L + 3) / 4) - 1               // tRRD_L minus 1 for scheduler pipeline
   ,L_pipe      = (L>0) ? L-1 : 0                      // tRRD_L timer load value
   ,RRD_dlr     = ((tRRD_dlr + 3) / 4) - 1
   ,RRD_dlr_pipe= (RRD_dlr > 0) ? RRD_dlr - 1 : 0
   ,tFAWF_slr_temp  = ((tFAW + 3)/4) - 3                           // Activate age shift register length
   ,tFAWF_slr       = ( tFAWF_slr_temp > 1 ) ? tFAWF_slr_temp : 1  // Minimum tFAWF size is 1 to keep select in legal range
   ,tFAWF_dlr_temp  = ((tFAW_dlr + 3)/4) - 3                       // !!!!!!! CHECK: JEDEC spec for FAW_slr in ns; but JEDEC spec for FAW_dlr in nCK
   ,tFAWF_dlr       = ( tFAWF_dlr_temp > 1 ) ? tFAWF_dlr_temp : 1;


integer i, j, k, l;

// tFAW_slr conformance check

reg  [4:0]         outstanding_act_slr [S_HEIGHT-1:0]; 
reg  [tFAWF_slr:0] act_shift_slr       [S_HEIGHT-1:0];  
reg  [tFAWF_slr:0] act_shift_slr_nxt   [S_HEIGHT-1:0];
reg  [4:0]         outstanding_act_slr_nxt [S_HEIGHT-1:0];
reg [S_HEIGHT-1:0] act_aged_out_slr;
reg [S_HEIGHT-1:0] faw_slr_done_vec;
reg                faw_slr_done;

always @(*) begin
  for (k = 0; k <= S_HEIGHT-1; k++) begin
    act_aged_out_slr[k] = act_shift_slr[k][tFAWF_slr];
    act_shift_slr_nxt[k] = { act_shift_slr[k][tFAWF_slr-1:0], 1'b0 };
    outstanding_act_slr_nxt[k] = outstanding_act_slr[k] >> act_aged_out_slr[k];
  end
  if (update) act_shift_slr_nxt[winLRank] = { act_shift_slr[winLRank][tFAWF_slr-1:0], update };
  if (act_rank_update) outstanding_act_slr_nxt[winLRank_nxt] = outstanding_act_slr_nxt[winLRank_nxt] << act_rank_update;
  for (k = 0; k <= S_HEIGHT-1; k++)
    faw_slr_done_vec[k] = ~outstanding_act_slr_nxt[k][4];
end // always

always @(posedge clk) begin
  if (rst) begin
    faw_slr_done           <= #TCQ 1'b0;
    for (l = 0; l <= S_HEIGHT-1; l++) begin
      outstanding_act_slr[l] <= #TCQ 5'b1;
      act_shift_slr[l]       <= #TCQ '0;
    end
  end else begin
    faw_slr_done           <= #TCQ &faw_slr_done_vec;
    for (l = 0; l <= S_HEIGHT-1; l++) begin
      outstanding_act_slr[l] <= #TCQ outstanding_act_slr_nxt[l];
      act_shift_slr[l]       <= #TCQ act_shift_slr_nxt[l];
    end
  end
end

// tFAW_dlr conformance check

reg  [4:0]         outstanding_act_dlr;  // Decoded format of the number of Activates in tFAW window
reg  [tFAWF_dlr:0] act_shift_dlr;        // Activate age delay line

// Push new Activates into the age delay line
wire [tFAWF_dlr:0] act_shift_dlr_nxt = { act_shift_dlr[tFAWF_dlr-1:0], update }; // spyglass disable W164a

// Signal when an old Activate command has aged out of the tFAW window.
wire           act_aged_out_dlr = act_shift_dlr[tFAWF_dlr];

// Increment the Activate count when a new Activate command is issued.
// Decrement as old Activates age out of the tFAW window.
// Note that the reset value of outstanding_act is 'b1. Left shift = increment, right shift = decrement.
wire [4:0]     outstanding_act_dlr_nxt = ( outstanding_act_dlr >> act_aged_out_dlr ) << act_rank_update;

always @(posedge clk) begin
  if (rst) begin
    outstanding_act_dlr <= #TCQ 5'b1;
    act_shift_dlr       <= #TCQ '0;
  end else begin
    outstanding_act_dlr <= #TCQ outstanding_act_dlr_nxt;
    act_shift_dlr       <= #TCQ act_shift_dlr_nxt;
  end
end

// Block new Activate commands when the Activate count reaches 4.
generate
  if (S_HEIGHT > 1)
    assign         fawOK = ~outstanding_act_dlr[4] & faw_slr_done;
  else
    assign         fawOK = ~outstanding_act_slr[0][4];
endgenerate

// tRRD conformance check
  
reg [1:0] rrdS[0:3];
reg [1:0] rrdL[0:3];
reg [1:0] rrdDLR;
reg [LR_WIDTH-1:0] prevLRA;

wire rrdDLR_zero;

generate
  if (RRD_dlr == 0)
    assign rrdDLR_zero = 1'b1;
  else
    assign rrdDLR_zero = rrdDLR==0;
endgenerate

always @(posedge clk) if (rst) begin
   prevLRA <= 'b0;
   rrdDLR <= 'b0;
   for (i = 0; i <= 3; i++) begin
      rrdS[i] <= 'b0;
      rrdL[i] <= 'b0;
   end
end else begin
   if (update) prevLRA <= #TCQ winLRank;
   if (update)
     rrdDLR <= #TCQ RRD_dlr_pipe;
   else if (rrdDLR)
     rrdDLR <= #TCQ rrdDLR - 1'b1;

   for (i = 0; i <= 3; i++) begin
      if (rrdS[i]) rrdS[i] <= #TCQ rrdS[i] - 1'b1;
      if (rrdL[i]) rrdL[i] <= #TCQ rrdL[i] - 1'b1;
      if (update)  rrdS[i] <= #TCQ S_pipe;         // spyglass disable W164c // load tRRD_S restriction to all Groups when any Activate issues to memory
   end
   if (update) begin
      rrdL[winGr] <= #TCQ L_pipe;                  // spyglass disable W164c // load tRRD_L restriction to Group that issued the Activate command
      if (TWO_GROUP_DDR4 == "TRUE") begin          // load tRRD_L restriction to sister Group if x16 DDR4
        rrdL[winGr2] <= #TCQ L_pipe;               // spyglass disable W164c
      end
   end
end

reg [3:0] act_dlr;

always @(*) begin
  for (j = 0; j <= 3; j++)
    act_dlr[j] = (S_HEIGHT > 1 & update) ? winLRank != cmdLRank[j*LR_WIDTH+:LR_WIDTH] : 
                 (S_HEIGHT > 1) ? prevLRA != cmdLRank[j*LR_WIDTH+:LR_WIDTH] : 
                 1'b0;
end 

always @(*) begin
   // The logic below checks the tRRD timers, including a bypass tRRD check on an update cycle,
   // for the Group FSM that the actReq orignated from.
   // Note that for x16 DDR4 there are only 2 Groups, so FSM 0 and FSM 1
   // both map to DRAM Group 0, and FSM 2 and FSM 3 map to DRAM group 1.
   // Therefore timers for two FSMs need to be checked for each actReq for x16 DDR4.
   // Note that FSM[n] is not checked against tRRD_L on update & winPort[n].
   // This is because an FSM cannot issue actReq on the cycle after it issues
   // an activate.  By the same reasoning the logic does not need to check
   // FSM[n] against tRRD_S on an update & winPort[n], but it doesn't hurt and
   // leaving it in simplifies the logic.
   rrdOK[0] = actReq[0]                                                                  // actReq[n] for FSM[n].
              & ( ( rrdS[0]==0 & rrdL[0]==0 & ~act_dlr[0] ) | ( rrdDLR_zero & act_dlr[0] ) )  // rrd timers for FSM[n] have expired.
              & ( ( rrdS[1]==0 & rrdL[1]==0 ) | ( TWO_GROUP_DDR4 == "FALSE" ) )          // rrd timers for sister FSM have expired or component is not x16 DDR4.
              & ( ~( update              ) | ( S==0 & ~act_dlr[0] ) | ( act_dlr[0] & (RRD_dlr == 0) )  )     // no group issued an act to this rank on the previous cycle or tRRD_S is zero.
              & ( ~( update & winPort[1] ) | ( L==0 ) | ( TWO_GROUP_DDR4 == "FALSE" ) ); // sister FSM did not issue an act to this rank on previous cycle,
                                                                                         // or tRRD_L is zero, or component is not x16 DDR4.
   rrdOK[1] = actReq[1]
              & ( ( rrdS[1]==0 & rrdL[1]==0 & ~act_dlr[1] ) | ( rrdDLR_zero & act_dlr[1] ) )
              & ( ( rrdS[0]==0 & rrdL[0]==0 ) | ( TWO_GROUP_DDR4 == "FALSE" ) )
              & (   ~( update              ) | ( S==0 & ~act_dlr[1] )   | ( act_dlr[1] & (RRD_dlr == 0) )  )
              & ( ( ~( update & winPort[0] ) | ( L==0 ) ) | ( TWO_GROUP_DDR4 == "FALSE" ) );
   rrdOK[2] = actReq[2]
              & ( ( rrdS[2]==0 & rrdL[2]==0 & ~act_dlr[2] ) | ( rrdDLR_zero & act_dlr[2] ) )
              & ( ( rrdS[3]==0 & rrdL[3]==0 ) | ( TWO_GROUP_DDR4 == "FALSE" ) )
              & (   ~( update              ) | ( S==0 & ~act_dlr[2] )   | ( act_dlr[2] & (RRD_dlr == 0) )  )
              & ( ( ~( update & winPort[3] ) | ( L==0 ) ) | ( TWO_GROUP_DDR4 == "FALSE" ) );
   rrdOK[3] = actReq[3]
              & ( ( rrdS[3]==0 & rrdL[3]==0 & ~act_dlr[3] ) | ( rrdDLR_zero & act_dlr[3] ) )
              & ( ( rrdS[2]==0 & rrdL[2]==0 ) | ( TWO_GROUP_DDR4 == "FALSE" ) )
              & (   ~( update              ) | ( S==0 & ~act_dlr[3] )   | ( act_dlr[3] & (RRD_dlr == 0) )  )
              & ( ( ~( update & winPort[2] ) | ( L==0 ) ) | ( TWO_GROUP_DDR4 == "FALSE" ) );
end

//synopsys translate_off

`ifdef MEM_INTERNAL
// Events - When asserted high in a test that passes all verification checks, these coverage
//          properties indicate that a functional coverage event has been hit.
// ---------------------------------------------------------------------------------------------

// Act request blocked by tRRD_S counter
wire   e_mc_act_rank_000_rrd = actReq[0] & fawOK & ~(rrdS[0]==0) & (rrdL[0]==0) & ~act_dlr[0] &  ~update & ( TWO_GROUP_DDR4 == "FALSE" );
always @(posedge clk) mc_act_rank_000: if (~rst) cover property (e_mc_act_rank_000_rrd);

// Act request blocked by tRRD_S update
wire   e_mc_act_rank_001_rrd = actReq[0] & fawOK & (rrdS[0]==0) & (rrdL[0]==0) & ~act_dlr[0] & update & ~( S==0 ) & ( TWO_GROUP_DDR4 == "FALSE" );
always @(posedge clk) mc_act_rank_001: if (~rst) cover property (e_mc_act_rank_001_rrd);

// Act request blocked by tRRD_S counter DDR4 x16 (hittable?)
wire   e_mc_act_rank_002_rrd = actReq[0] & fawOK & ~(rrdS[0]==0) & (rrdL[0]==0) &  ~act_dlr[0] & ~update & ~( TWO_GROUP_DDR4 == "FALSE" )
                                                 &  (rrdS[1]==0) & (rrdL[1]==0);
always @(posedge clk) mc_act_rank_002: if (~rst) cover property (e_mc_act_rank_002_rrd);

// Act request blocked by tRRD_S update DDR4 x16
wire   e_mc_act_rank_003_rrd = actReq[0] & fawOK & (rrdS[0]==0) & (rrdL[0]==0) & ~act_dlr[0] & update & ~( S==0 ) & ~( TWO_GROUP_DDR4 == "FALSE" )
                                                 & (rrdS[1]==0) & (rrdL[1]==0);
always @(posedge clk) mc_act_rank_003: if (~rst) cover property (e_mc_act_rank_003_rrd);

// Act request blocked by tRRD_S counter DDR4 x16 from other group (hittable?)
wire   e_mc_act_rank_004_rrd = actReq[0] & fawOK &  (rrdS[0]==0) & (rrdL[0]==0) &  ~act_dlr[0] & ~update & ~( TWO_GROUP_DDR4 == "FALSE" )
                                                 & ~(rrdS[1]==0) & (rrdL[1]==0);
always @(posedge clk) mc_act_rank_004: if (~rst) cover property (e_mc_act_rank_004_rrd);

// Act request blocked by tRRD_S update DDR4 x16 from other group
wire   e_mc_act_rank_005_rrd = actReq[0] & fawOK & (rrdS[0]==0) & (rrdL[0]==0) & ~act_dlr[0] & update & ~( S==0 ) & ~( TWO_GROUP_DDR4 == "FALSE" )
                                                 & (rrdS[1]==0) & (rrdL[1]==0);
always @(posedge clk) mc_act_rank_005: if (~rst) cover property (e_mc_act_rank_005_rrd);

// Act request blocked by tRRD_L update DDR4 x16 from other group
wire   e_mc_act_rank_006_rrd = actReq[0] & fawOK & (rrdS[0]==0) & (rrdL[0]==0) & ~act_dlr[0] & update & ( S==0 ) & ~( TWO_GROUP_DDR4 == "FALSE" )
                                                 & (rrdS[1]==0) & (rrdL[1]==0) & winPort[1] & ~( L==0 );
always @(posedge clk) mc_act_rank_006: if (~rst) cover property (e_mc_act_rank_006_rrd);

// Act request blocked by tRRD_L update DDR4 x16 from other group
wire   e_mc_act_rank_007_rrd = actReq[1] & fawOK & (rrdS[1]==0) & (rrdL[1]==0) & ~act_dlr[1] & update & ( S==0 ) & ~( TWO_GROUP_DDR4 == "FALSE" )
                                                 & (rrdS[0]==0) & (rrdL[0]==0) & winPort[0] & ~( L==0 );
always @(posedge clk) mc_act_rank_007: if (~rst) cover property (e_mc_act_rank_007_rrd);

// Act request blocked by tRRD_L update DDR4 x16 from other group
wire   e_mc_act_rank_008_rrd = actReq[2] & fawOK & (rrdS[2]==0) & (rrdL[2]==0) & ~act_dlr[2] & update & ( S==0 ) & ~( TWO_GROUP_DDR4 == "FALSE" )
                                                 & (rrdS[3]==0) & (rrdL[3]==0) & winPort[3] & ~( L==0 );
always @(posedge clk) mc_act_rank_008: if (~rst) cover property (e_mc_act_rank_008_rrd);

// Act request blocked by tRRD_L update DDR4 x16 from other group
wire   e_mc_act_rank_009_rrd = actReq[3] & fawOK & (rrdS[3]==0) & (rrdL[3]==0) & ~act_dlr[3] & update & ( S==0 ) & ~( TWO_GROUP_DDR4 == "FALSE" )
                                                 & (rrdS[2]==0) & (rrdL[2]==0) & winPort[2] & ~( L==0 );
always @(posedge clk) mc_act_rank_009: if (~rst) cover property (e_mc_act_rank_009_rrd);

// Act request blocked by tRRD_dlr
wire   e_mc_act_rank_015_rrd = actReq[0] & fawOK & act_dlr[0] & ~rrdDLR_zero & ~update & ( TWO_GROUP_DDR4 == "FALSE" );
always @(posedge clk) mc_act_rank_015: if (~rst) cover property (e_mc_act_rank_015_rrd);

wire   e_mc_act_rank_016_rrd = actReq[0] & fawOK & act_dlr[0] &  rrdDLR_zero &  update & ~(S==0) & ( TWO_GROUP_DDR4 == "FALSE" );
always @(posedge clk) mc_act_rank_016: if (~rst) cover property (e_mc_act_rank_016_rrd);

wire   e_mc_act_rank_017_rrd = actReq[1] & fawOK & act_dlr[1] & ~rrdDLR_zero & ~update & ( TWO_GROUP_DDR4 == "FALSE" );
always @(posedge clk) mc_act_rank_017: if (~rst) cover property (e_mc_act_rank_017_rrd);

wire   e_mc_act_rank_018_rrd = actReq[1] & fawOK & act_dlr[1] &  rrdDLR_zero &  update & ~(S==0) & ( TWO_GROUP_DDR4 == "FALSE" );
always @(posedge clk) mc_act_rank_018: if (~rst) cover property (e_mc_act_rank_018_rrd);

wire   e_mc_act_rank_019_rrd = actReq[2] & fawOK & act_dlr[2] & ~rrdDLR_zero & ~update & ( TWO_GROUP_DDR4 == "FALSE" );
always @(posedge clk) mc_act_rank_019: if (~rst) cover property (e_mc_act_rank_019_rrd);

wire   e_mc_act_rank_020_rrd = actReq[2] & fawOK & act_dlr[2] &  rrdDLR_zero &  update & ~(S==0) & ( TWO_GROUP_DDR4 == "FALSE" );
always @(posedge clk) mc_act_rank_020: if (~rst) cover property (e_mc_act_rank_020_rrd);

wire   e_mc_act_rank_021_rrd = actReq[3] & fawOK & act_dlr[3] & ~rrdDLR_zero & ~update & ( TWO_GROUP_DDR4 == "FALSE" );
always @(posedge clk) mc_act_rank_021: if (~rst) cover property (e_mc_act_rank_021_rrd);

wire   e_mc_act_rank_022_rrd = actReq[3] & fawOK & act_dlr[3] &  rrdDLR_zero &  update & ~(S==0) & ( TWO_GROUP_DDR4 == "FALSE" );
always @(posedge clk) mc_act_rank_022: if (~rst) cover property (e_mc_act_rank_022_rrd);

// Multiple groups blocked by tRRD_L
integer group_index;
reg [1:0] e_rrd_l_hot;
always @(*) begin
  e_rrd_l_hot = 2'b0;
  for (group_index = 0; group_index < 4; group_index = group_index + 1) begin
    e_rrd_l_hot += ~( rrdL[group_index] == 0 );
  end
end
wire   e_mc_act_rank_010_rrd = e_rrd_l_hot > 2'd1;
always @(posedge clk) mc_act_rank_010: if (~rst) cover property (e_mc_act_rank_010_rrd);
wire   e_mc_act_rank_011_rrd = e_rrd_l_hot > 2'd2;
always @(posedge clk) mc_act_rank_011: if (~rst) cover property (e_mc_act_rank_011_rrd);

// tFAW at minimum
wire   e_mc_act_rank_012_faw = (S_HEIGHT == 1) & ( tFAWF_slr == 1 ) & update;
always @(posedge clk) mc_act_rank_012: if (~rst) cover property (e_mc_act_rank_012_faw);

// tFAW at minimum to block act
wire   e_mc_act_rank_013_faw = (S_HEIGHT == 1) & ( tFAWF_slr == 4 ) & outstanding_act_slr[0][4];
always @(posedge clk) mc_act_rank_013: if (~rst) cover property (e_mc_act_rank_013_faw);

// tFAW above minimum to block act
wire   e_mc_act_rank_014_faw = (S_HEIGHT == 1) & ( tFAWF_slr == 8 ) & outstanding_act_slr[0][4];
always @(posedge clk) mc_act_rank_014: if (~rst) cover property (e_mc_act_rank_014_faw);

// tFAW_dlr block act
wire   e_mc_act_rank_023_faw = (S_HEIGHT == 2) & ( tFAWF_dlr == 1 ) & outstanding_act_dlr[4] & faw_slr_done;
always @(posedge clk) mc_act_rank_023: if (~rst) cover property (e_mc_act_rank_023_faw);


// Asserts - When asserted high, an illegal condition has been detected and the test has failed.
// ---------------------------------------------------------------------------------------------

// Same group wins on consecutive cycles due to no tRRD_L check
wire   a_mc_act_rank_000_rrd = actReq[0] & fawOK & (rrdS[0]==0) & (rrdL[0]==0) & update & ( S==0 ) & ~( TWO_GROUP_DDR4 == "FALSE" )
                                                 & (rrdS[1]==0) & (rrdL[1]==0) & winPort[0] & ~( L==0 );
always @(posedge clk) if (~rst) assert property (~a_mc_act_rank_000_rrd);

// Illegal act_rank_update
wire   a_mc_act_rank_001_faw = ((S_HEIGHT == 1) & outstanding_act_slr[0][4] & act_rank_update) |
                               ((S_HEIGHT  > 1) & (outstanding_act_dlr[4] | ~faw_slr_done) & act_rank_update);
always @(posedge clk) if (~rst) assert property (~a_mc_act_rank_001_faw);

// Illegal act_rank_update
reg act_rank_update_dly;
always @(posedge clk) begin
  act_rank_update_dly <= #TCQ act_rank_update;
end
wire   a_mc_act_rank_002_faw = update ^ act_rank_update_dly;
always @(posedge clk) if (~rst) assert property (~a_mc_act_rank_002_faw);


`endif

//synopsys translate_on

endmodule


