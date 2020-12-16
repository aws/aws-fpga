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
//  /   /         Filename           : ddr4_v2_2_10_mc_act_timer.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_mc_act_timer module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_10_mc_act_timer #(parameter
    tFAW   = 500
   ,tFAW_dlr = 500
   ,tRRD_L = 500
   ,tRRD_S = 500
   ,tRRD_dlr = 500
   ,BGBITS  = 2
   ,S_HEIGHT = 1
   ,LR_WIDTH = 1
   ,RKBITS    = 2
   ,RANK_SLAB = 4
   ,MEM     = "DDR4"
   ,TCQ    = 0.1   
)(
    input       clk
   ,input       rst

   ,output [3:0] actReqT

   ,input [3:0] actReq
   ,input [RKBITS*4-1:0] cmdRank
   ,input [4*LR_WIDTH-1:0] cmdLRank
   ,input [3:0] winPort
   ,input [RKBITS-1:0] winRank
   ,input [LR_WIDTH-1:0] winLRank
   ,input [3:0] act_winPort_nxt
   ,input [RANK_SLAB-1:0] act_rank_update
);

integer i, j;

localparam TWO_GROUP_DDR4 = ( ( BGBITS == 1 ) & ( MEM == "DDR4" ) ) ? "TRUE" : "FALSE";

wire [3:0] rrdOK[0:RANK_SLAB-1];
wire [RANK_SLAB-1:0] fawOK;

generate
if (RANK_SLAB == 4) begin: aReqT_4R
assign actReqT =   ( rrdOK[0] & { 4 { fawOK[0] } } )
                 | ( rrdOK[1] & { 4 { fawOK[1] } } )
                 | ( rrdOK[2] & { 4 { fawOK[2] } } )
                 | ( rrdOK[3] & { 4 { fawOK[3] } } );
end else begin:aReqT_8R
assign actReqT =   ( rrdOK[0] & { 4 { fawOK[0] } } )
                 | ( rrdOK[1] & { 4 { fawOK[1] } } )
                 | ( rrdOK[2] & { 4 { fawOK[2] } } )
                 | ( rrdOK[3] & { 4 { fawOK[3] } } )
                 | ( rrdOK[4] & { 4 { fawOK[4] } } )
                 | ( rrdOK[5] & { 4 { fawOK[5] } } )
                 | ( rrdOK[6] & { 4 { fawOK[6] } } )
                 | ( rrdOK[7] & { 4 { fawOK[7] } } );
end
endgenerate

reg [RANK_SLAB-1:0] update;
reg [1:0] winGr;
reg [1:0] winGr2;
reg [3:0] actReqs[0:RANK_SLAB-1];
reg [LR_WIDTH-1:0] winLRank_nxt;

always @(*) begin
   for (i = 0; i <= RANK_SLAB-1; i++) actReqs[i] = 4'b0;
   if (actReq[0]) actReqs[cmdRank[RKBITS*1-1:RKBITS*0]][0] = 1'b1;
   if (actReq[1]) actReqs[cmdRank[RKBITS*2-1:RKBITS*1]][1] = 1'b1;
   if (actReq[2]) actReqs[cmdRank[RKBITS*3-1:RKBITS*2]][2] = 1'b1;
   if (actReq[3]) actReqs[cmdRank[RKBITS*4-1:RKBITS*3]][3] = 1'b1;
end

always @(*) begin
   casez (act_winPort_nxt)
     4'bzzz1: begin
        winLRank_nxt = cmdLRank[0*LR_WIDTH+:LR_WIDTH];
     end
     4'bzz1z: begin
        winLRank_nxt = cmdLRank[1*LR_WIDTH+:LR_WIDTH];
     end
     4'bz1zz: begin
        winLRank_nxt = cmdLRank[2*LR_WIDTH+:LR_WIDTH];
     end
     4'b1zzz: begin
        winLRank_nxt = cmdLRank[3*LR_WIDTH+:LR_WIDTH];
     end
     default: begin
        winLRank_nxt = '0;
     end
   endcase
end

always @(*) begin
   update = {RANK_SLAB{1'b0}};
   winGr = 2'b0;
   winGr2 = 2'b0;
   casez (winPort)
      4'b0001: begin
         update[winRank] = 1'b1;
         winGr = 2'd0;
         winGr2 = 2'd1;
      end
      4'b0010: begin
         update[winRank] = 1'b1;
         winGr = 2'd1;
         winGr2 = 2'd0;
      end
      4'b0100: begin
         update[winRank] = 1'b1;
         winGr = 2'd2;
         winGr2 = 2'd3;
      end
      4'b1000: begin
         update[winRank] = 1'b1;
         winGr = 2'd3;
         winGr2 = 2'd2;
      end
      default: begin
         update = {RANK_SLAB{1'b0}};
         winGr  = 2'b0;
         winGr2 = 2'b0;
      end
   endcase
end

genvar r;
generate
   for (r = 0; r <= RANK_SLAB-1; r = r + 1) begin:rr
      ddr4_v2_2_10_mc_act_rank #(
         .tFAW   (tFAW)
        ,.tFAW_dlr(tFAW_dlr)
        ,.tRRD_L (tRRD_L)
        ,.tRRD_S (tRRD_S)
	,.tRRD_dlr (tRRD_dlr)
        ,.TWO_GROUP_DDR4 (TWO_GROUP_DDR4)
        ,.S_HEIGHT (S_HEIGHT)
        ,.LR_WIDTH (LR_WIDTH)
        ,.TCQ    (TCQ)
      )u__ddr_mc_act_rank(
          .clk (clk)
         ,.rst (rst)

         ,.fawOK   (fawOK[r])
         ,.rrdOK   (rrdOK[r])

         ,.actReq  (actReqs[r])
         ,.update  (update[r])
         ,.winLRank_nxt     (winLRank_nxt)
         ,.act_rank_update  (act_rank_update[r])
         ,.cmdLRank(cmdLRank)
         ,.winGr   (winGr)
         ,.winGr2  (winGr2)
         ,.winLRank(winLRank)
         ,.winPort (winPort)
      );
   end
endgenerate

//synopsys translate_off

`ifdef MEM_INTERNAL
// Events - When asserted high in a test that passes all verification checks, these coverage
//          properties indicate that a functional coverage event has been hit.
// ---------------------------------------------------------------------------------------------

// Act request blocked by tRRD
wire   e_mc_act_timer_000_rrd = actReq[0] & fawOK[cmdRank[RKBITS*1-1:RKBITS*0]] & ~rrdOK[cmdRank[RKBITS*1-1:RKBITS*0]][0];
always @(posedge clk) mc_act_timer_000: if (~rst) cover property (e_mc_act_timer_000_rrd);

// Three Act requests blocked by tRRD
wire   e_mc_act_timer_001_rrd = ( & actReq[2:0] ) 
                                & fawOK[cmdRank[RKBITS*1-1:RKBITS*0]] & fawOK[cmdRank[RKBITS*2-1:RKBITS*1]] & fawOK[cmdRank[RKBITS*3-1:RKBITS*2]] 
                                & ~rrdOK[cmdRank[RKBITS*1-1:RKBITS*0]][0] & ~rrdOK[cmdRank[RKBITS*2-1:RKBITS*1]][0] & ~rrdOK[cmdRank[RKBITS*3-1:RKBITS*2]][0];
always @(posedge clk) mc_act_timer_001: if (~rst) cover property (e_mc_act_timer_001_rrd);

// Act requests to two different ranks blocked by tRRD
wire   e_mc_act_timer_002_rrd = ( & actReq[1:0] ) 
                                & fawOK[cmdRank[RKBITS*1-1:RKBITS*0]] & fawOK[cmdRank[RKBITS*2-1:RKBITS*1]]
                                & ~rrdOK[cmdRank[RKBITS*1-1:RKBITS*0]][0] & ~rrdOK[cmdRank[RKBITS*2-1:RKBITS*1]][0]
                                & ~( cmdRank[RKBITS*1-1:RKBITS*0] == cmdRank[RKBITS*2-1:RKBITS*1] );
always @(posedge clk) mc_act_timer_002: if (~rst) cover property (e_mc_act_timer_002_rrd);

// Act request blocked by tFAW
wire   e_mc_act_timer_003_faw = actReq[0] & ~fawOK[cmdRank[RKBITS*1-1:RKBITS*0]] & rrdOK[cmdRank[RKBITS*1-1:RKBITS*0]][0];
always @(posedge clk) mc_act_timer_003: if (~rst) cover property (e_mc_act_timer_003_faw);

// Three Act requests blocked by tFAW
wire   e_mc_act_timer_004_faw = ( & actReq[3:1] ) 
                                & ~fawOK[cmdRank[RKBITS*4-1:RKBITS*3]] & ~fawOK[cmdRank[RKBITS*2-1:RKBITS*1]] & ~fawOK[cmdRank[RKBITS*3-1:RKBITS*2]] 
                                & rrdOK[cmdRank[RKBITS*4-1:RKBITS*3]][0] & rrdOK[cmdRank[RKBITS*2-1:RKBITS*1]][0] & rrdOK[cmdRank[RKBITS*3-1:RKBITS*2]][0];
always @(posedge clk) mc_act_timer_004: if (~rst) cover property (e_mc_act_timer_004_faw);

// Act requests to two different ranks blocked by tFAW
wire   e_mc_act_timer_005_faw = ( & actReq[3:2] ) 
                                & ~fawOK[cmdRank[RKBITS*4-1:RKBITS*3]] & ~fawOK[cmdRank[RKBITS*3-1:RKBITS*2]]
                                & rrdOK[cmdRank[RKBITS*4-1:RKBITS*3]][0] & rrdOK[cmdRank[RKBITS*3-1:RKBITS*2]][0]
                                & ~( cmdRank[RKBITS*4-1:RKBITS*3] == cmdRank[RKBITS*3-1:RKBITS*2] );
always @(posedge clk) mc_act_timer_005: if (~rst) cover property (e_mc_act_timer_005_faw);



// Asserts - When asserted high, an illegal condition has been detected and the test has failed.
// ---------------------------------------------------------------------------------------------

integer group_index;
integer rank_index;

// One-hot cold checks
reg [2:0]  a_winport_hot;
reg [2:0]  a_act_rank_update_hot;
always @(*) begin
  a_winport_hot = 2'b0;
  a_act_rank_update_hot = 2'b0;
  for (group_index = 0; group_index < 4; group_index = group_index + 1) begin
    a_winport_hot         += winPort[group_index];
  end
  for (rank_index = 0; rank_index < RANK_SLAB; rank_index = rank_index + 1) begin
    a_act_rank_update_hot += act_rank_update[rank_index];
  end
end
wire       a_mc_act_timer_000_hot = ( a_winport_hot > 3'd1 );
always @(posedge clk) if (~rst) assert property (~a_mc_act_timer_000_hot);
wire       a_mc_act_timer_001_hot = ( a_act_rank_update_hot > 3'd1 );
always @(posedge clk) if (~rst) assert property (~a_mc_act_timer_001_hot);


`endif

//synopsys translate_on

endmodule


