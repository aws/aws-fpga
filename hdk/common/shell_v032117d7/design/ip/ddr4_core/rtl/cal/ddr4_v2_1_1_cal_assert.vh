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
//  /   /         Filename           : mig_0_phy_ddr4_assert.vh
// /___/   /\     Date Last Modified : $Date: 2014/09/14 $
// \   \  /  \    Date Created       : Fri Jul 25 2014
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM
// Purpose          : Phy-Only and PingPing Phy Assertion check
//                   
// Reference        :
// Revision History :
//*****************************************************************************

//synthesis translate_off
   localparam CH0           = 0;
   localparam CH1           = 1;   
   localparam NUM_OF_SLOT   = 4;
   localparam SLOT0         = 0;
   localparam SLOT1         = 1;
   localparam SLOT2         = 2;
   localparam SLOT3         = 3;
   
   reg [CSBITS-1:0] premerged_CS_n[PING_PONG_PHY][8-1:0];
   reg [8-1:0] merged_CS_n[PING_PONG_PHY-1:0];

   reg [PING_PONG_PHY-1:0][NUM_OF_SLOT-1:0] slotX_is_cas;
   reg [PING_PONG_PHY-1:0][NUM_OF_SLOT-1:0] slotX_is_non_cas;

   integer k;
      
   // Merged CS amount Ranks
   always@(*) begin
   for (i=0; i<PING_PONG_PHY; i=i+1) begin
      for (j=0; j<CSBITS; j=j+1) begin
	 for (k=0; k<8; k=k+1) begin
	    premerged_CS_n[i][k][j] = mc_CS_n[i*CSBITS*8+j*8+k];
	 end
      end
   end
   for (i=0; i<PING_PONG_PHY; i=i+1) begin   
      for (k=0; k<8; k=k+1) begin
   	 merged_CS_n[i][k] = | premerged_CS_n[i][k];
      end
   end

   for (i=0; i<PING_PONG_PHY; i=i+1) begin
      for (j=0; j<NUM_OF_SLOT; j=j+1) begin
	 // CAS command per slot when CS is active
	 slotX_is_cas[i][j]     = (mcRdCAS[i] || mcWrCAS[i])   && (mcCasSlot[i*2+:2] == j) && 
					 (merged_CS_n[i][j*2+:2] != 2'd3);
	 // Non-CAS command per slot when CS is active
	 slotX_is_non_cas[i][j] = ((~mcRdCAS[i] && ~mcWrCAS[i]) || (mcCasSlot[i*2+:2] != j)) &&
					 (merged_CS_n[i][j*2+:2] != 2'd3);
      end
   end
   end
      
   always@(posedge clk) begin
      if (PING_PONG_PHY>1) begin // Only check for PingPong Phy.
      for (i=0; i<PING_PONG_PHY; i=i+1) begin
	 // Check CAS should not be in Slot1, 3
	 CAS_NOT_IN_SLOT_0_2:     assert ((slotX_is_cas[i][SLOT1] == 0) && (slotX_is_cas[i][SLOT3] == 0))
	   else $display ($time, "\tINCORRECT CAS SLOT USED: Channel %h PPS1 %h PPS3 %h\n",
			  i,
			  slotX_is_cas[i][SLOT1], slotX_is_cas[i][SLOT3]);
	 // Check Non-CAS should not be in Slot0, 2
	 // Note: This limitation is added for 2015.1 to simplify verification
	 //NON_CAS_NOT_IN_SLOT_1_3: assert ((slotX_is_non_cas[CH0][SLOT0] == 0) && (slotX_is_non_cas[CH0][SLOT2] == 0) &&
	 //				  (slotX_is_non_cas[CH1][SLOT0] == 0) && (slotX_is_non_cas[CH1][SLOT2] == 0))
	 //  else $display ($time, "\tINCORRECT NON-CAS SLOT USED: PP0S0 %h PP0S2 %h PP1S0 %h PP1S2 %h (Need review after 2015.1 release)\n",
	 //		  slotX_is_non_cas[CH0][SLOT0], slotX_is_non_cas[CH0][SLOT2],
	 //		  slotX_is_non_cas[CH1][SLOT0], slotX_is_non_cas[CH1][SLOT2]);
      end
      end

   end

//synthesis translate_on
