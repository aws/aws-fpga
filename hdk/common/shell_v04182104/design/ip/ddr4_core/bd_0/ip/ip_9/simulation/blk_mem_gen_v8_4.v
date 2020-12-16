/******************************************************************************
-- (c) Copyright 2006 - 2013 Xilinx, Inc. All rights reserved.
--
-- This file contains confidential and proprietary information
-- of Xilinx, Inc. and is protected under U.S. and
-- international copyright and other intellectual property
-- laws.
--
-- DISCLAIMER
-- This disclaimer is not a license and does not grant any
-- rights to the materials distributed herewith. Except as
-- otherwise provided in a valid license issued to you by
-- Xilinx, and to the maximum extent permitted by applicable
-- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
-- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
-- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
-- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
-- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
-- (2) Xilinx shall not be liable (whether in contract or tort,
-- including negligence, or under any other theory of
-- liability) for any loss or damage of any kind or nature
-- related to, arising under or in connection with these
-- materials, including for any direct, or any indirect,
-- special, incidental, or consequential loss or damage
-- (including loss of data, profits, goodwill, or any type of
-- loss or damage suffered as a result of any action brought
-- by a third party) even if such damage or loss was
-- reasonably foreseeable or Xilinx had been advised of the
-- possibility of the same.
--
-- CRITICAL APPLICATIONS
-- Xilinx products are not designed or intended to be fail-
-- safe, or for use in any application requiring fail-safe
-- performance, such as life-support or safety devices or
-- systems, Class III medical devices, nuclear facilities,
-- applications related to the deployment of airbags, or any
-- other applications that could lead to death, personal
-- injury, or severe property or environmental damage
-- (individually and collectively, "Critical
-- Applications"). Customer assumes the sole risk and
-- liability of any use of Xilinx products in Critical
-- Applications, subject only to applicable laws and
-- regulations governing limitations on product liability.
--
-- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
-- PART OF THIS FILE AT ALL TIMES.
--
 *****************************************************************************
 *
 * Filename: blk_mem_gen_v8_4_4.v
 *
 * Description:
 *   This file is the Verilog behvarial model for the
 *       Block Memory Generator Core.
 *
 *****************************************************************************
 * Author: Xilinx
 *
 * History: Jan 11, 2006 Initial revision
 *          Jun 11, 2007 Added independent register stages for 
 *                       Port A and Port B (IP1_Jm/v2.5)
 *          Aug 28, 2007 Added mux pipeline stages feature (IP2_Jm/v2.6)
 *          Mar 13, 2008 Behavioral model optimizations
 *          April 07, 2009  : Added support for Spartan-6 and Virtex-6
 *                            features, including the following:
 *                            (i)   error injection, detection and/or correction
 *                            (ii) reset priority
 *                            (iii)  special reset behavior
 *    
 *****************************************************************************/
`timescale 1ps/1ps

module STATE_LOGIC_v8_4 (O, I0, I1, I2, I3, I4, I5);

  parameter INIT = 64'h0000000000000000;

  input I0, I1, I2, I3, I4, I5;

  output O;

  reg O;
  reg tmp;

  always @( I5 or I4 or I3 or  I2 or  I1 or  I0 )  begin
 
    tmp =  I0 ^ I1  ^ I2 ^ I3 ^ I4 ^ I5;

    if ( tmp == 0 || tmp == 1)

        O = INIT[{I5, I4, I3, I2, I1, I0}];

  end
endmodule

module beh_vlog_muxf7_v8_4 (O, I0, I1, S);

    output O;
    reg    O;

    input  I0, I1, S;

	always @(I0 or I1 or S) 
	    if (S)
		O = I1;
	    else
		O = I0;
endmodule

module beh_vlog_ff_clr_v8_4 (Q, C, CLR, D);
  parameter INIT = 0;
localparam FLOP_DELAY = 100;
    output Q;

    input  C, CLR, D;

    reg Q;

    initial Q= 1'b0;

    always @(posedge C )
      if (CLR)
	Q<= 1'b0;
      else
	Q<= #FLOP_DELAY D;


endmodule

module beh_vlog_ff_pre_v8_4 (Q, C, D, PRE);

  parameter INIT = 0;
localparam FLOP_DELAY = 100;
    output Q;
    input  C, D, PRE;

    reg Q;

    initial Q= 1'b0;

    always @(posedge C )
      if (PRE)
           Q <= 1'b1;
      else
	   Q <= #FLOP_DELAY D;

endmodule

module beh_vlog_ff_ce_clr_v8_4 (Q, C, CE, CLR, D);

  parameter INIT = 0;
localparam FLOP_DELAY = 100;
    output Q;
    input  C, CE, CLR, D;

    reg Q;

    initial Q= 1'b0;
    always @(posedge C )
       if (CLR)
           Q <= 1'b0;
       else if (CE)
	   Q <= #FLOP_DELAY D;

endmodule

module write_netlist_v8_4
#(
   parameter	     C_AXI_TYPE = 0
 )
 (
    S_ACLK, S_ARESETN, S_AXI_AWVALID, S_AXI_WVALID, S_AXI_BREADY,
    w_last_c, bready_timeout_c, aw_ready_r, S_AXI_WREADY, S_AXI_BVALID,
    S_AXI_WR_EN, addr_en_c, incr_addr_c, bvalid_c 
  );

    input S_ACLK;
    input S_ARESETN;
    input S_AXI_AWVALID;
    input S_AXI_WVALID;
    input S_AXI_BREADY;
    input w_last_c;
    input bready_timeout_c;
    output aw_ready_r;
    output S_AXI_WREADY;
    output S_AXI_BVALID;
    output S_AXI_WR_EN;
    output addr_en_c;
    output incr_addr_c;
    output bvalid_c;
 //-------------------------------------------------------------------------
 //AXI LITE
 //-------------------------------------------------------------------------
generate if (C_AXI_TYPE == 0 ) begin : gbeh_axi_lite_sm
  wire w_ready_r_7;
  wire w_ready_c;
  wire aw_ready_c;
  wire NlwRenamedSignal_bvalid_c;
  wire NlwRenamedSignal_incr_addr_c;
  wire present_state_FSM_FFd3_13;
  wire present_state_FSM_FFd2_14;
  wire present_state_FSM_FFd1_15;
  wire present_state_FSM_FFd4_16;
  wire present_state_FSM_FFd4_In;
  wire present_state_FSM_FFd3_In;
  wire present_state_FSM_FFd2_In;
  wire present_state_FSM_FFd1_In;
  wire present_state_FSM_FFd4_In1_21;
  wire [0:0] Mmux_aw_ready_c ; 
begin
  assign
  S_AXI_WREADY = w_ready_r_7,
  S_AXI_BVALID = NlwRenamedSignal_incr_addr_c,
  S_AXI_WR_EN = NlwRenamedSignal_bvalid_c,
  incr_addr_c = NlwRenamedSignal_incr_addr_c,
  bvalid_c = NlwRenamedSignal_bvalid_c;

  assign NlwRenamedSignal_incr_addr_c = 1'b0;

  beh_vlog_ff_clr_v8_4 #(
      .INIT (1'b0))
  aw_ready_r_2 (
      .C ( S_ACLK), 
      .CLR ( S_ARESETN), 
      .D ( aw_ready_c), 
      .Q ( aw_ready_r)
    );
  beh_vlog_ff_clr_v8_4 #(
      .INIT (1'b0))
  w_ready_r (
      .C ( S_ACLK), 
      .CLR ( S_ARESETN), 
      .D ( w_ready_c), 
      .Q ( w_ready_r_7)
    );
  beh_vlog_ff_pre_v8_4  #(
      .INIT (1'b1))
  present_state_FSM_FFd4 (
      .C ( S_ACLK), 
      .D ( present_state_FSM_FFd4_In), 
      .PRE ( S_ARESETN), 
      .Q ( present_state_FSM_FFd4_16)
    );
 beh_vlog_ff_clr_v8_4 #(
      .INIT (1'b0))
  present_state_FSM_FFd3 (
      .C ( S_ACLK), 
      .CLR ( S_ARESETN), 
      .D ( present_state_FSM_FFd3_In), 
      .Q ( present_state_FSM_FFd3_13)
    );
  beh_vlog_ff_clr_v8_4 #(
      .INIT (1'b0))
  present_state_FSM_FFd2 (
      .C ( S_ACLK), 
      .CLR ( S_ARESETN), 
      .D ( present_state_FSM_FFd2_In), 
      .Q ( present_state_FSM_FFd2_14)
    );
beh_vlog_ff_clr_v8_4 #(
      .INIT (1'b0))
  present_state_FSM_FFd1 (
      .C ( S_ACLK), 
      .CLR ( S_ARESETN), 
      .D ( present_state_FSM_FFd1_In), 
      .Q ( present_state_FSM_FFd1_15)
    );
STATE_LOGIC_v8_4 #(
      .INIT (64'h0000000055554440))
  present_state_FSM_FFd3_In1 (
      .I0 ( S_AXI_WVALID), 
      .I1 ( S_AXI_AWVALID), 
      .I2 ( present_state_FSM_FFd2_14), 
      .I3 ( present_state_FSM_FFd4_16), 
      .I4 ( present_state_FSM_FFd3_13), 
      .I5 (1'b0), 
      .O ( present_state_FSM_FFd3_In)
    );
STATE_LOGIC_v8_4 #(
      .INIT (64'h0000000088880800))
  present_state_FSM_FFd2_In1 (
      .I0 ( S_AXI_AWVALID), 
      .I1 ( S_AXI_WVALID), 
      .I2 ( bready_timeout_c), 
      .I3 ( present_state_FSM_FFd2_14), 
      .I4 ( present_state_FSM_FFd4_16), 
      .I5 (1'b0), 
      .O ( present_state_FSM_FFd2_In)
    );
STATE_LOGIC_v8_4 #(
      .INIT (64'h00000000AAAA2000))
  Mmux_addr_en_c_0_1 (
      .I0 ( S_AXI_AWVALID), 
      .I1 ( bready_timeout_c), 
      .I2 ( present_state_FSM_FFd2_14), 
      .I3 ( S_AXI_WVALID), 
      .I4 ( present_state_FSM_FFd4_16), 
      .I5 (1'b0), 
      .O ( addr_en_c)
    );
 STATE_LOGIC_v8_4 #(
      .INIT (64'hF5F07570F5F05500))
  Mmux_w_ready_c_0_1 (
      .I0 ( S_AXI_WVALID), 
      .I1 ( bready_timeout_c), 
      .I2 ( S_AXI_AWVALID), 
      .I3 ( present_state_FSM_FFd3_13), 
      .I4 ( present_state_FSM_FFd4_16), 
      .I5 ( present_state_FSM_FFd2_14), 
      .O ( w_ready_c)
    );
STATE_LOGIC_v8_4 #(
      .INIT (64'h88808880FFFF8880))
  present_state_FSM_FFd1_In1 (
      .I0 ( S_AXI_WVALID), 
      .I1 ( bready_timeout_c), 
      .I2 ( present_state_FSM_FFd3_13), 
      .I3 ( present_state_FSM_FFd2_14), 
      .I4 ( present_state_FSM_FFd1_15), 
      .I5 ( S_AXI_BREADY), 
      .O ( present_state_FSM_FFd1_In)
    );
STATE_LOGIC_v8_4 #(
      .INIT (64'h00000000000000A8))
  Mmux_S_AXI_WR_EN_0_1 (
      .I0 ( S_AXI_WVALID), 
      .I1 ( present_state_FSM_FFd2_14), 
      .I2 ( present_state_FSM_FFd3_13), 
      .I3 (1'b0), 
      .I4 (1'b0), 
      .I5 (1'b0), 
      .O ( NlwRenamedSignal_bvalid_c)
    );
 STATE_LOGIC_v8_4 #(
      .INIT (64'h2F0F27072F0F2200))
  present_state_FSM_FFd4_In1 (
      .I0 ( S_AXI_WVALID), 
      .I1 ( bready_timeout_c), 
      .I2 ( S_AXI_AWVALID), 
      .I3 ( present_state_FSM_FFd3_13), 
      .I4 ( present_state_FSM_FFd4_16), 
      .I5 ( present_state_FSM_FFd2_14), 
      .O ( present_state_FSM_FFd4_In1_21)
    );
 STATE_LOGIC_v8_4 #(
      .INIT (64'h00000000000000F8))
  present_state_FSM_FFd4_In2 ( 
      .I0 ( present_state_FSM_FFd1_15), 
      .I1 ( S_AXI_BREADY), 
      .I2 ( present_state_FSM_FFd4_In1_21), 
      .I3 (1'b0), 
      .I4 (1'b0), 
      .I5 (1'b0), 
      .O ( present_state_FSM_FFd4_In)
    );
STATE_LOGIC_v8_4 #(
      .INIT (64'h7535753575305500))
  Mmux_aw_ready_c_0_1 ( 
      .I0 ( S_AXI_AWVALID), 
      .I1 ( bready_timeout_c), 
      .I2 ( S_AXI_WVALID), 
      .I3 ( present_state_FSM_FFd4_16), 
      .I4 ( present_state_FSM_FFd3_13), 
      .I5 ( present_state_FSM_FFd2_14), 
      .O ( Mmux_aw_ready_c[0])
    );
STATE_LOGIC_v8_4 #(
      .INIT (64'h00000000000000F8))
  Mmux_aw_ready_c_0_2 (
      .I0 ( present_state_FSM_FFd1_15), 
      .I1 ( S_AXI_BREADY), 
      .I2 ( Mmux_aw_ready_c[0]), 
      .I3 (1'b0), 
      .I4 (1'b0), 
      .I5 (1'b0), 
      .O ( aw_ready_c)
    );
end 
end 
endgenerate

  //---------------------------------------------------------------------
  // AXI FULL
  //---------------------------------------------------------------------
generate if (C_AXI_TYPE == 1 ) begin : gbeh_axi_full_sm
  wire w_ready_r_8; 
  wire w_ready_c; 
  wire aw_ready_c; 
  wire NlwRenamedSig_OI_bvalid_c; 
  wire present_state_FSM_FFd1_16; 
  wire present_state_FSM_FFd4_17; 
  wire present_state_FSM_FFd3_18; 
  wire present_state_FSM_FFd2_19; 
  wire present_state_FSM_FFd4_In; 
  wire present_state_FSM_FFd3_In; 
  wire present_state_FSM_FFd2_In; 
  wire present_state_FSM_FFd1_In; 
  wire present_state_FSM_FFd2_In1_24; 
  wire present_state_FSM_FFd4_In1_25; 
  wire N2; 
  wire N4; 
begin
assign
  S_AXI_WREADY = w_ready_r_8,
  bvalid_c = NlwRenamedSig_OI_bvalid_c,
  S_AXI_BVALID = 1'b0;

beh_vlog_ff_clr_v8_4 #(
      .INIT (1'b0))
  aw_ready_r_2
    (
      .C ( S_ACLK),
      .CLR ( S_ARESETN),
      .D ( aw_ready_c),
      .Q ( aw_ready_r)
    );
beh_vlog_ff_clr_v8_4 #(
      .INIT (1'b0))
  w_ready_r
    (
      .C ( S_ACLK),
      .CLR ( S_ARESETN),
      .D ( w_ready_c),
      .Q ( w_ready_r_8)
    );
 beh_vlog_ff_pre_v8_4  #(
      .INIT (1'b1))
  present_state_FSM_FFd4
    (
      .C ( S_ACLK),
      .D ( present_state_FSM_FFd4_In),
      .PRE ( S_ARESETN),
      .Q ( present_state_FSM_FFd4_17)
    );
beh_vlog_ff_clr_v8_4 #(
      .INIT (1'b0))
  present_state_FSM_FFd3
    (
      .C ( S_ACLK),
      .CLR ( S_ARESETN),
      .D ( present_state_FSM_FFd3_In),
      .Q ( present_state_FSM_FFd3_18)
    );
beh_vlog_ff_clr_v8_4 #(
      .INIT (1'b0))
  present_state_FSM_FFd2
    (
      .C ( S_ACLK),
      .CLR ( S_ARESETN),
      .D ( present_state_FSM_FFd2_In),
      .Q ( present_state_FSM_FFd2_19)
    );
 beh_vlog_ff_clr_v8_4 #(
      .INIT (1'b0))
  present_state_FSM_FFd1
    (
      .C ( S_ACLK),
      .CLR ( S_ARESETN),
      .D ( present_state_FSM_FFd1_In),
      .Q ( present_state_FSM_FFd1_16)
    );
 STATE_LOGIC_v8_4 #(
      .INIT (64'h0000000000005540))
  present_state_FSM_FFd3_In1
    (
      .I0 ( S_AXI_WVALID),
      .I1 ( present_state_FSM_FFd4_17),
      .I2 ( S_AXI_AWVALID),
      .I3 ( present_state_FSM_FFd3_18),
      .I4 (1'b0),
      .I5 (1'b0),
      .O ( present_state_FSM_FFd3_In)
    );
STATE_LOGIC_v8_4 #(
      .INIT (64'hBF3FBB33AF0FAA00))
  Mmux_aw_ready_c_0_2
    (
      .I0 ( S_AXI_BREADY),
      .I1 ( bready_timeout_c),
      .I2 ( S_AXI_AWVALID),
      .I3 ( present_state_FSM_FFd1_16),
      .I4 ( present_state_FSM_FFd4_17),
      .I5 ( NlwRenamedSig_OI_bvalid_c),
      .O ( aw_ready_c)
    );
 STATE_LOGIC_v8_4 #(
      .INIT (64'hAAAAAAAA20000000))
  Mmux_addr_en_c_0_1
    (
      .I0 ( S_AXI_AWVALID),
      .I1 ( bready_timeout_c),
      .I2 ( present_state_FSM_FFd2_19),
      .I3 ( S_AXI_WVALID),
      .I4 ( w_last_c),
      .I5 ( present_state_FSM_FFd4_17),
      .O ( addr_en_c)
    );
 STATE_LOGIC_v8_4 #(
      .INIT (64'h00000000000000A8))
  Mmux_S_AXI_WR_EN_0_1
    (
      .I0 ( S_AXI_WVALID),
      .I1 ( present_state_FSM_FFd2_19),
      .I2 ( present_state_FSM_FFd3_18),
      .I3 (1'b0),
      .I4 (1'b0),
      .I5 (1'b0),
      .O ( S_AXI_WR_EN)
    );
 STATE_LOGIC_v8_4 #(
      .INIT (64'h0000000000002220))
  Mmux_incr_addr_c_0_1
    (
      .I0 ( S_AXI_WVALID),
      .I1 ( w_last_c),
      .I2 ( present_state_FSM_FFd2_19),
      .I3 ( present_state_FSM_FFd3_18),
      .I4 (1'b0),
      .I5 (1'b0),
      .O ( incr_addr_c)
    );
STATE_LOGIC_v8_4 #(
      .INIT (64'h0000000000008880))
  Mmux_aw_ready_c_0_11
    (
      .I0 ( S_AXI_WVALID),
      .I1 ( w_last_c),
      .I2 ( present_state_FSM_FFd2_19),
      .I3 ( present_state_FSM_FFd3_18),
      .I4 (1'b0),
      .I5 (1'b0),
      .O ( NlwRenamedSig_OI_bvalid_c)
    );
 STATE_LOGIC_v8_4 #(
      .INIT (64'h000000000000D5C0))
  present_state_FSM_FFd2_In1
    (
      .I0 ( w_last_c),
      .I1 ( S_AXI_AWVALID),
      .I2 ( present_state_FSM_FFd4_17),
      .I3 ( present_state_FSM_FFd3_18),
      .I4 (1'b0),
      .I5 (1'b0),
      .O ( present_state_FSM_FFd2_In1_24)
    );
STATE_LOGIC_v8_4 #(
      .INIT (64'hFFFFAAAA08AAAAAA))
  present_state_FSM_FFd2_In2
    (
      .I0 ( present_state_FSM_FFd2_19),
      .I1 ( S_AXI_AWVALID),
      .I2 ( bready_timeout_c),
      .I3 ( w_last_c),
      .I4 ( S_AXI_WVALID),
      .I5 ( present_state_FSM_FFd2_In1_24),
      .O ( present_state_FSM_FFd2_In)
    );
 STATE_LOGIC_v8_4 #(
      .INIT (64'h00C0004000C00000))
  present_state_FSM_FFd4_In1
    (
      .I0 ( S_AXI_AWVALID),
      .I1 ( w_last_c),
      .I2 ( S_AXI_WVALID),
      .I3 ( bready_timeout_c),
      .I4 ( present_state_FSM_FFd3_18),
      .I5 ( present_state_FSM_FFd2_19),
      .O ( present_state_FSM_FFd4_In1_25)
    );
 STATE_LOGIC_v8_4 #(
      .INIT (64'h00000000FFFF88F8))
  present_state_FSM_FFd4_In2
    (
      .I0 ( present_state_FSM_FFd1_16),
      .I1 ( S_AXI_BREADY),
      .I2 ( present_state_FSM_FFd4_17),
      .I3 ( S_AXI_AWVALID),
      .I4 ( present_state_FSM_FFd4_In1_25),
      .I5 (1'b0),
      .O ( present_state_FSM_FFd4_In)
    );
 STATE_LOGIC_v8_4 #(
      .INIT (64'h0000000000000007))
  Mmux_w_ready_c_0_SW0
    (
      .I0 ( w_last_c),
      .I1 ( S_AXI_WVALID),
      .I2 (1'b0),
      .I3 (1'b0),
      .I4 (1'b0),
      .I5 (1'b0),
      .O ( N2)
    );
 STATE_LOGIC_v8_4 #(
      .INIT (64'hFABAFABAFAAAF000))
  Mmux_w_ready_c_0_Q
    (
      .I0 ( N2),
      .I1 ( bready_timeout_c),
      .I2 ( S_AXI_AWVALID),
      .I3 ( present_state_FSM_FFd4_17),
      .I4 ( present_state_FSM_FFd3_18),
      .I5 ( present_state_FSM_FFd2_19),
      .O ( w_ready_c)
    );
 STATE_LOGIC_v8_4 #(
      .INIT (64'h0000000000000008))
  Mmux_aw_ready_c_0_11_SW0
    (
      .I0 ( bready_timeout_c),
      .I1 ( S_AXI_WVALID),
      .I2 (1'b0),
      .I3 (1'b0),
      .I4 (1'b0),
      .I5 (1'b0),
      .O ( N4)
    );
 STATE_LOGIC_v8_4 #(
      .INIT (64'h88808880FFFF8880))
  present_state_FSM_FFd1_In1
    (
      .I0 ( w_last_c),
      .I1 ( N4),
      .I2 ( present_state_FSM_FFd2_19),
      .I3 ( present_state_FSM_FFd3_18),
      .I4 ( present_state_FSM_FFd1_16),
      .I5 ( S_AXI_BREADY),
      .O ( present_state_FSM_FFd1_In)
    );
end
end
endgenerate
endmodule


module read_netlist_v8_4 #(
      parameter C_AXI_TYPE                 = 1,
      parameter C_ADDRB_WIDTH              = 12
      ) ( S_AXI_R_LAST_INT, S_ACLK, S_ARESETN, S_AXI_ARVALID,
          S_AXI_RREADY,S_AXI_INCR_ADDR,S_AXI_ADDR_EN,
          S_AXI_SINGLE_TRANS,S_AXI_MUX_SEL, S_AXI_R_LAST, S_AXI_ARREADY,
          S_AXI_RLAST, S_AXI_RVALID, S_AXI_RD_EN, S_AXI_ARLEN);

    input S_AXI_R_LAST_INT;
    input S_ACLK;
    input S_ARESETN;
    input S_AXI_ARVALID;
    input S_AXI_RREADY;
    output S_AXI_INCR_ADDR;
    output S_AXI_ADDR_EN;
    output S_AXI_SINGLE_TRANS;
    output S_AXI_MUX_SEL;
    output S_AXI_R_LAST;
    output S_AXI_ARREADY;
    output S_AXI_RLAST;
    output S_AXI_RVALID;
    output S_AXI_RD_EN;
    input [7:0] S_AXI_ARLEN;

  wire present_state_FSM_FFd1_13 ; 
  wire present_state_FSM_FFd2_14 ; 
  wire gaxi_full_sm_outstanding_read_r_15 ; 
  wire gaxi_full_sm_ar_ready_r_16 ; 
  wire gaxi_full_sm_r_last_r_17 ; 
  wire NlwRenamedSig_OI_gaxi_full_sm_r_valid_r ; 
  wire gaxi_full_sm_r_valid_c ; 
  wire S_AXI_RREADY_gaxi_full_sm_r_valid_r_OR_9_o ; 
  wire gaxi_full_sm_ar_ready_c ; 
  wire gaxi_full_sm_outstanding_read_c ; 
  wire NlwRenamedSig_OI_S_AXI_R_LAST ; 
  wire S_AXI_ARLEN_7_GND_8_o_equal_1_o ; 
  wire present_state_FSM_FFd2_In ; 
  wire present_state_FSM_FFd1_In ; 
  wire Mmux_S_AXI_R_LAST13 ; 
  wire N01 ; 
  wire N2 ; 
  wire Mmux_gaxi_full_sm_ar_ready_c11 ; 
  wire N4 ; 
  wire N8 ; 
  wire N9 ; 
  wire N10 ; 
  wire N11 ; 
  wire N12 ; 
  wire N13 ; 
  assign
  S_AXI_R_LAST = NlwRenamedSig_OI_S_AXI_R_LAST,
  S_AXI_ARREADY = gaxi_full_sm_ar_ready_r_16,
  S_AXI_RLAST = gaxi_full_sm_r_last_r_17,
  S_AXI_RVALID = NlwRenamedSig_OI_gaxi_full_sm_r_valid_r;

  beh_vlog_ff_clr_v8_4 #(
      .INIT (1'b0))
  gaxi_full_sm_outstanding_read_r (
      .C (S_ACLK),
      .CLR(S_ARESETN),
      .D(gaxi_full_sm_outstanding_read_c),
      .Q(gaxi_full_sm_outstanding_read_r_15)
    );
  beh_vlog_ff_ce_clr_v8_4 #(
      .INIT (1'b0))
  gaxi_full_sm_r_valid_r (
      .C (S_ACLK),
      .CE (S_AXI_RREADY_gaxi_full_sm_r_valid_r_OR_9_o),
      .CLR (S_ARESETN),
      .D (gaxi_full_sm_r_valid_c),
      .Q (NlwRenamedSig_OI_gaxi_full_sm_r_valid_r)
    );
  beh_vlog_ff_clr_v8_4 #(
      .INIT (1'b0))
  gaxi_full_sm_ar_ready_r (
      .C (S_ACLK),
      .CLR (S_ARESETN),
      .D (gaxi_full_sm_ar_ready_c),
      .Q (gaxi_full_sm_ar_ready_r_16)
    );
  beh_vlog_ff_ce_clr_v8_4 #(
      .INIT(1'b0))
  gaxi_full_sm_r_last_r (
      .C (S_ACLK),
      .CE (S_AXI_RREADY_gaxi_full_sm_r_valid_r_OR_9_o),
      .CLR (S_ARESETN),
      .D (NlwRenamedSig_OI_S_AXI_R_LAST),
      .Q (gaxi_full_sm_r_last_r_17)
    );
  beh_vlog_ff_clr_v8_4 #(
      .INIT (1'b0))
  present_state_FSM_FFd2 (
      .C ( S_ACLK),
      .CLR ( S_ARESETN),
      .D ( present_state_FSM_FFd2_In),
      .Q ( present_state_FSM_FFd2_14)
    );
  beh_vlog_ff_clr_v8_4 #(
      .INIT (1'b0))
  present_state_FSM_FFd1 (
      .C (S_ACLK),
      .CLR (S_ARESETN),
      .D (present_state_FSM_FFd1_In),
      .Q (present_state_FSM_FFd1_13)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'h000000000000000B))
  S_AXI_RREADY_gaxi_full_sm_r_valid_r_OR_9_o1 (
      .I0 ( S_AXI_RREADY),
      .I1 ( NlwRenamedSig_OI_gaxi_full_sm_r_valid_r),
      .I2 (1'b0),
      .I3 (1'b0),
      .I4 (1'b0),
      .I5 (1'b0),
      .O (S_AXI_RREADY_gaxi_full_sm_r_valid_r_OR_9_o)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'h0000000000000008))
  Mmux_S_AXI_SINGLE_TRANS11 (
      .I0 (S_AXI_ARVALID),
      .I1 (S_AXI_ARLEN_7_GND_8_o_equal_1_o),
      .I2 (1'b0),
      .I3 (1'b0),
      .I4 (1'b0),
      .I5 (1'b0),
      .O (S_AXI_SINGLE_TRANS)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'h0000000000000004))
  Mmux_S_AXI_ADDR_EN11 (
      .I0 (present_state_FSM_FFd1_13),
      .I1 (S_AXI_ARVALID),
      .I2 (1'b0),
      .I3 (1'b0),
      .I4 (1'b0),
      .I5 (1'b0),
      .O (S_AXI_ADDR_EN)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'hECEE2022EEEE2022))
  present_state_FSM_FFd2_In1 (
      .I0 ( S_AXI_ARVALID),
      .I1 ( present_state_FSM_FFd1_13),
      .I2 ( S_AXI_RREADY),
      .I3 ( S_AXI_ARLEN_7_GND_8_o_equal_1_o),
      .I4 ( present_state_FSM_FFd2_14),
      .I5 ( NlwRenamedSig_OI_gaxi_full_sm_r_valid_r),
      .O ( present_state_FSM_FFd2_In)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'h0000000044440444))
  Mmux_S_AXI_R_LAST131 (
      .I0 ( present_state_FSM_FFd1_13),
      .I1 ( S_AXI_ARVALID),
      .I2 ( present_state_FSM_FFd2_14),
      .I3 ( NlwRenamedSig_OI_gaxi_full_sm_r_valid_r),
      .I4 ( S_AXI_RREADY),
      .I5 (1'b0),
      .O ( Mmux_S_AXI_R_LAST13)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'h4000FFFF40004000))
  Mmux_S_AXI_INCR_ADDR11 (
      .I0 ( S_AXI_R_LAST_INT),
      .I1 ( S_AXI_RREADY_gaxi_full_sm_r_valid_r_OR_9_o),
      .I2 ( present_state_FSM_FFd2_14),
      .I3 ( present_state_FSM_FFd1_13),
      .I4 ( S_AXI_ARLEN_7_GND_8_o_equal_1_o),
      .I5 ( Mmux_S_AXI_R_LAST13),
      .O ( S_AXI_INCR_ADDR)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'h00000000000000FE))
  S_AXI_ARLEN_7_GND_8_o_equal_1_o_7_SW0 (
      .I0 ( S_AXI_ARLEN[2]),
      .I1 ( S_AXI_ARLEN[1]),
      .I2 ( S_AXI_ARLEN[0]),
      .I3 ( 1'b0),
      .I4 ( 1'b0),
      .I5 ( 1'b0),
      .O ( N01)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'h0000000000000001))
  S_AXI_ARLEN_7_GND_8_o_equal_1_o_7_Q (
      .I0 ( S_AXI_ARLEN[7]),
      .I1 ( S_AXI_ARLEN[6]),
      .I2 ( S_AXI_ARLEN[5]),
      .I3 ( S_AXI_ARLEN[4]),
      .I4 ( S_AXI_ARLEN[3]),
      .I5 ( N01),
      .O ( S_AXI_ARLEN_7_GND_8_o_equal_1_o)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'h0000000000000007))
  Mmux_gaxi_full_sm_outstanding_read_c1_SW0 (
      .I0 ( S_AXI_ARVALID),
      .I1 ( S_AXI_ARLEN_7_GND_8_o_equal_1_o),
      .I2 ( 1'b0),
      .I3 ( 1'b0),
      .I4 ( 1'b0),
      .I5 ( 1'b0),
      .O ( N2)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'h0020000002200200))
  Mmux_gaxi_full_sm_outstanding_read_c1 (
      .I0 ( NlwRenamedSig_OI_gaxi_full_sm_r_valid_r),
      .I1 ( S_AXI_RREADY),
      .I2 ( present_state_FSM_FFd1_13),
      .I3 ( present_state_FSM_FFd2_14),
      .I4 ( gaxi_full_sm_outstanding_read_r_15),
      .I5 ( N2),
      .O ( gaxi_full_sm_outstanding_read_c)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'h0000000000004555))
  Mmux_gaxi_full_sm_ar_ready_c12 (
      .I0 ( S_AXI_ARVALID),
      .I1 ( S_AXI_RREADY),
      .I2 ( present_state_FSM_FFd2_14),
      .I3 ( NlwRenamedSig_OI_gaxi_full_sm_r_valid_r),
      .I4 ( 1'b0),
      .I5 ( 1'b0),
      .O ( Mmux_gaxi_full_sm_ar_ready_c11)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'h00000000000000EF))
  Mmux_S_AXI_R_LAST11_SW0 (
      .I0 ( S_AXI_ARLEN_7_GND_8_o_equal_1_o),
      .I1 ( S_AXI_RREADY),
      .I2 ( NlwRenamedSig_OI_gaxi_full_sm_r_valid_r),
      .I3 ( 1'b0),
      .I4 ( 1'b0),
      .I5 ( 1'b0),
      .O ( N4)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'hFCAAFC0A00AA000A))
  Mmux_S_AXI_R_LAST11 (
      .I0 ( S_AXI_ARVALID),
      .I1 ( gaxi_full_sm_outstanding_read_r_15),
      .I2 ( present_state_FSM_FFd2_14),
      .I3 ( present_state_FSM_FFd1_13),
      .I4 ( N4),
      .I5 ( S_AXI_RREADY_gaxi_full_sm_r_valid_r_OR_9_o),
      .O ( gaxi_full_sm_r_valid_c)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'h00000000AAAAAA08))
  S_AXI_MUX_SEL1 (
      .I0 (present_state_FSM_FFd1_13),
      .I1 (NlwRenamedSig_OI_gaxi_full_sm_r_valid_r),
      .I2 (S_AXI_RREADY),
      .I3 (present_state_FSM_FFd2_14),
      .I4 (gaxi_full_sm_outstanding_read_r_15),
      .I5 (1'b0),
      .O (S_AXI_MUX_SEL)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'hF3F3F755A2A2A200))
  Mmux_S_AXI_RD_EN11 (
      .I0 ( present_state_FSM_FFd1_13),
      .I1 ( NlwRenamedSig_OI_gaxi_full_sm_r_valid_r),
      .I2 ( S_AXI_RREADY),
      .I3 ( gaxi_full_sm_outstanding_read_r_15),
      .I4 ( present_state_FSM_FFd2_14),
      .I5 ( S_AXI_ARVALID),
      .O ( S_AXI_RD_EN)
    );
  beh_vlog_muxf7_v8_4 present_state_FSM_FFd1_In3 (
      .I0 ( N8),
      .I1 ( N9),
      .S ( present_state_FSM_FFd1_13),
      .O ( present_state_FSM_FFd1_In)
    );

  STATE_LOGIC_v8_4 #(
      .INIT (64'h000000005410F4F0))
  present_state_FSM_FFd1_In3_F (
      .I0 ( S_AXI_RREADY),
      .I1 ( present_state_FSM_FFd2_14),
      .I2 ( S_AXI_ARVALID),
      .I3 ( NlwRenamedSig_OI_gaxi_full_sm_r_valid_r),
      .I4 ( S_AXI_ARLEN_7_GND_8_o_equal_1_o),
      .I5 ( 1'b0),
      .O ( N8)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'h0000000072FF7272))
  present_state_FSM_FFd1_In3_G (
      .I0 ( present_state_FSM_FFd2_14),
      .I1 ( S_AXI_R_LAST_INT),
      .I2 ( gaxi_full_sm_outstanding_read_r_15),
      .I3 ( S_AXI_RREADY),
      .I4 ( NlwRenamedSig_OI_gaxi_full_sm_r_valid_r),
      .I5 ( 1'b0),
      .O ( N9)
    );
  beh_vlog_muxf7_v8_4 Mmux_gaxi_full_sm_ar_ready_c14 (
      .I0 ( N10),
      .I1 ( N11),
      .S ( present_state_FSM_FFd1_13),
      .O ( gaxi_full_sm_ar_ready_c)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'h00000000FFFF88A8))
  Mmux_gaxi_full_sm_ar_ready_c14_F (
      .I0 ( S_AXI_ARLEN_7_GND_8_o_equal_1_o),
      .I1 ( S_AXI_RREADY),
      .I2 ( present_state_FSM_FFd2_14),
      .I3 ( NlwRenamedSig_OI_gaxi_full_sm_r_valid_r),
      .I4 ( Mmux_gaxi_full_sm_ar_ready_c11),
      .I5 ( 1'b0),
      .O ( N10)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'h000000008D008D8D))
  Mmux_gaxi_full_sm_ar_ready_c14_G (
      .I0 ( present_state_FSM_FFd2_14),
      .I1 ( S_AXI_R_LAST_INT),
      .I2 ( gaxi_full_sm_outstanding_read_r_15),
      .I3 ( S_AXI_RREADY),
      .I4 ( NlwRenamedSig_OI_gaxi_full_sm_r_valid_r),
      .I5 ( 1'b0),
      .O ( N11)
    );
  beh_vlog_muxf7_v8_4 Mmux_S_AXI_R_LAST1 (
      .I0 ( N12),
      .I1 ( N13),
      .S ( present_state_FSM_FFd1_13),
      .O ( NlwRenamedSig_OI_S_AXI_R_LAST)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'h0000000088088888))
  Mmux_S_AXI_R_LAST1_F (
      .I0 ( S_AXI_ARLEN_7_GND_8_o_equal_1_o),
      .I1 ( S_AXI_ARVALID),
      .I2 ( present_state_FSM_FFd2_14),
      .I3 ( S_AXI_RREADY),
      .I4 ( NlwRenamedSig_OI_gaxi_full_sm_r_valid_r),
      .I5 ( 1'b0),
      .O ( N12)
    );
  STATE_LOGIC_v8_4 #(
      .INIT (64'h00000000E400E4E4))
  Mmux_S_AXI_R_LAST1_G (
      .I0 ( present_state_FSM_FFd2_14),
      .I1 ( gaxi_full_sm_outstanding_read_r_15),
      .I2 ( S_AXI_R_LAST_INT),
      .I3 ( S_AXI_RREADY),
      .I4 ( NlwRenamedSig_OI_gaxi_full_sm_r_valid_r),
      .I5 ( 1'b0),
      .O ( N13)
    );

endmodule


module blk_mem_axi_write_wrapper_beh_v8_4
  # (
    // AXI Interface related parameters start here
    parameter C_INTERFACE_TYPE           = 0, // 0: Native Interface; 1: AXI Interface
    parameter C_AXI_TYPE                 = 0, // 0: AXI Lite; 1: AXI Full;
    parameter C_AXI_SLAVE_TYPE           = 0, // 0: MEMORY SLAVE; 1: PERIPHERAL SLAVE;
    parameter C_MEMORY_TYPE              = 0, // 0: SP-RAM, 1: SDP-RAM; 2: TDP-RAM; 3: DP-ROM;
    parameter C_WRITE_DEPTH_A            = 0,
    parameter C_AXI_AWADDR_WIDTH         = 32,
    parameter C_ADDRA_WIDTH 	         = 12,
    parameter C_AXI_WDATA_WIDTH          = 32,
    parameter C_HAS_AXI_ID               = 0,
    parameter C_AXI_ID_WIDTH             = 4,
    // AXI OUTSTANDING WRITES
    parameter C_AXI_OS_WR                = 2
    )
    (
     // AXI Global Signals
    input S_ACLK,  
    input S_ARESETN,
    // AXI Full/Lite Slave Write Channel (write side)
    input [C_AXI_ID_WIDTH-1:0] S_AXI_AWID,
    input [C_AXI_AWADDR_WIDTH-1:0] S_AXI_AWADDR,
    input [8-1:0] S_AXI_AWLEN,
    input [2:0] S_AXI_AWSIZE,
    input [1:0] S_AXI_AWBURST,
    input  S_AXI_AWVALID,
    output S_AXI_AWREADY,
    input  S_AXI_WVALID,
    output S_AXI_WREADY, 
    output reg [C_AXI_ID_WIDTH-1:0] S_AXI_BID = 0,
    output S_AXI_BVALID,
    input  S_AXI_BREADY,
    // Signals for BMG interface
    output [C_ADDRA_WIDTH-1:0] S_AXI_AWADDR_OUT,
    output S_AXI_WR_EN
    );

  localparam FLOP_DELAY  = 100;  // 100 ps

   localparam C_RANGE = ((C_AXI_WDATA_WIDTH == 8)?0:
                       ((C_AXI_WDATA_WIDTH==16)?1:
                       ((C_AXI_WDATA_WIDTH==32)?2:
                       ((C_AXI_WDATA_WIDTH==64)?3:
                       ((C_AXI_WDATA_WIDTH==128)?4:
                       ((C_AXI_WDATA_WIDTH==256)?5:0))))));




  wire bvalid_c                 ;
  reg bready_timeout_c          = 0;
  wire [1:0] bvalid_rd_cnt_c;
  reg bvalid_r         	= 0;
  reg [2:0] bvalid_count_r = 0;
  reg [((C_AXI_TYPE == 1 && C_AXI_SLAVE_TYPE == 0)?
        C_AXI_AWADDR_WIDTH:C_ADDRA_WIDTH)-1:0] awaddr_reg = 0;
  reg [1:0] bvalid_wr_cnt_r = 0;
  reg [1:0] bvalid_rd_cnt_r = 0;
  wire w_last_c                 ;
  wire addr_en_c                ;
  wire incr_addr_c              ;
  wire aw_ready_r 	        ;
  wire dec_alen_c               ;
  reg bvalid_d1_c = 0;
  reg [7:0] awlen_cntr_r = 0;
  reg [7:0] awlen_int = 0;
  reg [1:0] awburst_int = 0;

  integer total_bytes              = 0;
  integer wrap_boundary            = 0;
  integer wrap_base_addr           = 0;
  integer num_of_bytes_c           = 0;
  integer num_of_bytes_r           = 0;
  // Array to store BIDs
  reg [C_AXI_ID_WIDTH-1:0] axi_bid_array[3:0] ;
  wire S_AXI_BVALID_axi_wr_fsm;

  //-------------------------------------
  //AXI WRITE FSM COMPONENT INSTANTIATION
  //-------------------------------------
 write_netlist_v8_4 #(.C_AXI_TYPE(C_AXI_TYPE)) axi_wr_fsm
      (
      .S_ACLK(S_ACLK),
      .S_ARESETN(S_ARESETN),
      .S_AXI_AWVALID(S_AXI_AWVALID),
      .aw_ready_r(aw_ready_r),
      .S_AXI_WVALID(S_AXI_WVALID),
      .S_AXI_WREADY(S_AXI_WREADY),
      .S_AXI_BREADY(S_AXI_BREADY),
      .S_AXI_WR_EN(S_AXI_WR_EN),
      .w_last_c(w_last_c),
      .bready_timeout_c(bready_timeout_c),
      .addr_en_c(addr_en_c),
      .incr_addr_c(incr_addr_c),
      .bvalid_c(bvalid_c),
      .S_AXI_BVALID (S_AXI_BVALID_axi_wr_fsm) 
	  );   
  
   
   //Wrap Address boundary calculation 
   always@(*) begin
    num_of_bytes_c = 2**((C_AXI_TYPE == 1 && C_AXI_SLAVE_TYPE == 0)?S_AXI_AWSIZE:0);
    total_bytes    = (num_of_bytes_r)*(awlen_int+1);
    wrap_base_addr = ((awaddr_reg)/((total_bytes==0)?1:total_bytes))*(total_bytes);
    wrap_boundary  = wrap_base_addr+total_bytes;
  end
  
  //-------------------------------------------------------------------------
  // BMG address generation
  //-------------------------------------------------------------------------
   always @(posedge S_ACLK or S_ARESETN) begin
         if (S_ARESETN == 1'b1) begin
           awaddr_reg       <= 0;
	   num_of_bytes_r   <= 0;
	   awburst_int      <= 0; 
	 end else begin
           if (addr_en_c == 1'b1) begin
              awaddr_reg       <= #FLOP_DELAY S_AXI_AWADDR  ;
	      num_of_bytes_r   <= num_of_bytes_c;
	      awburst_int      <= ((C_AXI_TYPE == 1 && C_AXI_SLAVE_TYPE == 0)?S_AXI_AWBURST:2'b01);
	   end else if (incr_addr_c == 1'b1) begin
	      if (awburst_int == 2'b10) begin
		if(awaddr_reg == (wrap_boundary-num_of_bytes_r)) begin
		  awaddr_reg  <= wrap_base_addr;
		end else begin
		  awaddr_reg <= awaddr_reg + num_of_bytes_r;
		end
	      end else if (awburst_int == 2'b01 || awburst_int == 2'b11) begin
		awaddr_reg   <= awaddr_reg + num_of_bytes_r;
	      end
           end
         end
   end
  
    
   assign S_AXI_AWADDR_OUT   =  ((C_AXI_TYPE == 1 && C_AXI_SLAVE_TYPE == 0)?
			  	       awaddr_reg[C_AXI_AWADDR_WIDTH-1:C_RANGE]:awaddr_reg);

  //-------------------------------------------------------------------------
  // AXI wlast generation
  //-------------------------------------------------------------------------
    always @(posedge S_ACLK or S_ARESETN) begin
        if (S_ARESETN == 1'b1) begin
          awlen_cntr_r      <= 0;
	  awlen_int       <= 0;
	  end else begin
          if (addr_en_c == 1'b1) begin
	    awlen_int         <= #FLOP_DELAY (C_AXI_TYPE == 0?0:S_AXI_AWLEN) ;
	    awlen_cntr_r      <= #FLOP_DELAY (C_AXI_TYPE == 0?0:S_AXI_AWLEN) ;
	    end else if (dec_alen_c == 1'b1) begin
            awlen_cntr_r      <= #FLOP_DELAY awlen_cntr_r - 1 ;
          end
        end
    end

    assign w_last_c          = (awlen_cntr_r == 0 && S_AXI_WVALID == 1'b1)?1'b1:1'b0;
    
    assign dec_alen_c        =  (incr_addr_c | w_last_c);

   //-------------------------------------------------------------------------
   // Generation of bvalid counter for outstanding transactions  
   //-------------------------------------------------------------------------
    always @(posedge S_ACLK or S_ARESETN) begin
      if (S_ARESETN == 1'b1) begin
	bvalid_count_r             <= 0;
	end else begin
	// bvalid_count_r generation
	if (bvalid_c == 1'b1 && bvalid_r == 1'b1 && S_AXI_BREADY == 1'b1) begin
	  bvalid_count_r          <=   #FLOP_DELAY bvalid_count_r ;
	  end else if (bvalid_c == 1'b1) begin  
	  bvalid_count_r          <=  #FLOP_DELAY  bvalid_count_r + 1 ;
	  end else if (bvalid_r == 1'b1 && S_AXI_BREADY == 1'b1 && bvalid_count_r != 0) begin
	  bvalid_count_r          <=  #FLOP_DELAY  bvalid_count_r - 1 ;
	end
      end
    end

    //-------------------------------------------------------------------------
    // Generation of bvalid when BID is used 
    //-------------------------------------------------------------------------
    generate if (C_HAS_AXI_ID == 1) begin:gaxi_bvalid_id_r
      always @(posedge S_ACLK or S_ARESETN) begin
        if (S_ARESETN == 1'b1) begin
          bvalid_r                   <=  0;
          bvalid_d1_c                <=  0;
	end else begin
         // Delay the generation o bvalid_r for generation for BID 
         bvalid_d1_c  <= bvalid_c;
         
         //external bvalid signal generation
         if (bvalid_d1_c == 1'b1) begin
           bvalid_r                <=   #FLOP_DELAY 1'b1 ;
	 end else if (bvalid_count_r <= 1 && S_AXI_BREADY == 1'b1) begin
           bvalid_r                <=   #FLOP_DELAY 0 ;
         end
        end
      end
    end
    endgenerate
      
   //-------------------------------------------------------------------------
   // Generation of bvalid when BID is not used 
   //-------------------------------------------------------------------------
   generate if(C_HAS_AXI_ID == 0) begin:gaxi_bvalid_noid_r
    always @(posedge S_ACLK or S_ARESETN) begin
        if (S_ARESETN == 1'b1) begin
          bvalid_r                   <=  0;
	end else begin
         //external bvalid signal generation
         if (bvalid_c == 1'b1) begin
           bvalid_r                <=   #FLOP_DELAY 1'b1 ;
	 end else if (bvalid_count_r <= 1 && S_AXI_BREADY == 1'b1) begin
           bvalid_r                <=   #FLOP_DELAY 0 ;
         end
       end
    end
    end
   endgenerate
    
    //-------------------------------------------------------------------------
    // Generation of Bready timeout
    //-------------------------------------------------------------------------
    always @(bvalid_count_r) begin
    	// bready_timeout_c generation
	if(bvalid_count_r == C_AXI_OS_WR-1) begin
	  bready_timeout_c        <=   1'b1;
	end else begin
	  bready_timeout_c        <=   1'b0;
	end
    end
    
    //-------------------------------------------------------------------------
    // Generation of BID 
    //-------------------------------------------------------------------------
    generate if(C_HAS_AXI_ID == 1) begin:gaxi_bid_gen

    always @(posedge S_ACLK or S_ARESETN) begin
        if (S_ARESETN == 1'b1) begin
            bvalid_wr_cnt_r   <= 0;
            bvalid_rd_cnt_r   <= 0;
	end else begin
          // STORE AWID IN AN ARRAY
          if(bvalid_c == 1'b1) begin
            bvalid_wr_cnt_r  <= bvalid_wr_cnt_r + 1;
          end
	  // generate BID FROM AWID ARRAY
	  bvalid_rd_cnt_r <= #FLOP_DELAY bvalid_rd_cnt_c ;
	  S_AXI_BID       <= axi_bid_array[bvalid_rd_cnt_c];
        end       
    end
    
    assign bvalid_rd_cnt_c = (bvalid_r == 1'b1 && S_AXI_BREADY == 1'b1)?bvalid_rd_cnt_r+1:bvalid_rd_cnt_r;
    
    //-------------------------------------------------------------------------
    // Storing AWID for generation of BID
    //-------------------------------------------------------------------------
    always @(posedge S_ACLK or S_ARESETN) begin
      if(S_ARESETN == 1'b1) begin
	axi_bid_array[0] = 0;
	axi_bid_array[1] = 0;
	axi_bid_array[2] = 0;
	axi_bid_array[3] = 0;
	end else if(aw_ready_r == 1'b1 && S_AXI_AWVALID == 1'b1) begin
	axi_bid_array[bvalid_wr_cnt_r] <= S_AXI_AWID;
      end
    end
  
  end
  endgenerate

  assign S_AXI_BVALID   =  bvalid_r;
  assign S_AXI_AWREADY  =  aw_ready_r;

  endmodule

module blk_mem_axi_read_wrapper_beh_v8_4
# (
    //// AXI Interface related parameters start here
    parameter  C_INTERFACE_TYPE           = 0,
    parameter  C_AXI_TYPE                 = 0,
    parameter  C_AXI_SLAVE_TYPE           = 0,
    parameter  C_MEMORY_TYPE              = 0,
    parameter  C_WRITE_WIDTH_A            = 4,
    parameter  C_WRITE_DEPTH_A            = 32,
    parameter  C_ADDRA_WIDTH              = 12,
    parameter  C_AXI_PIPELINE_STAGES      = 0,
    parameter  C_AXI_ARADDR_WIDTH         = 12,
    parameter  C_HAS_AXI_ID               = 0,
    parameter  C_AXI_ID_WIDTH             = 4,
    parameter  C_ADDRB_WIDTH              = 12
    )
   (

    //// AXI Global Signals
    input S_ACLK,
    input S_ARESETN,
    //// AXI Full/Lite Slave Read (Read side)
    input [C_AXI_ARADDR_WIDTH-1:0] S_AXI_ARADDR,
    input [7:0] S_AXI_ARLEN,
    input [2:0] S_AXI_ARSIZE,
    input [1:0] S_AXI_ARBURST,
    input S_AXI_ARVALID,
    output S_AXI_ARREADY,
    output S_AXI_RLAST, 
    output S_AXI_RVALID,
    input S_AXI_RREADY,
    input [C_AXI_ID_WIDTH-1:0] S_AXI_ARID,
    output reg [C_AXI_ID_WIDTH-1:0] S_AXI_RID = 0,
    //// AXI Full/Lite Read Address Signals to BRAM
    output [C_ADDRB_WIDTH-1:0] S_AXI_ARADDR_OUT,
    output S_AXI_RD_EN
    );

  localparam FLOP_DELAY  = 100;  // 100 ps
  localparam C_RANGE = ((C_WRITE_WIDTH_A == 8)?0:
                       ((C_WRITE_WIDTH_A==16)?1:
                       ((C_WRITE_WIDTH_A==32)?2:
                       ((C_WRITE_WIDTH_A==64)?3:
                       ((C_WRITE_WIDTH_A==128)?4:
                       ((C_WRITE_WIDTH_A==256)?5:0))))));



  reg [C_AXI_ID_WIDTH-1:0] ar_id_r=0;
  wire addr_en_c; 
  wire rd_en_c; 
  wire incr_addr_c; 
  wire single_trans_c; 
  wire dec_alen_c; 
  wire mux_sel_c; 
  wire r_last_c; 
  wire r_last_int_c; 
  wire [C_ADDRB_WIDTH-1 : 0] araddr_out; 

  reg [7:0] arlen_int_r=0; 
  reg [7:0] arlen_cntr=8'h01; 
  reg [1:0] arburst_int_c=0; 
  reg [1:0] arburst_int_r=0; 
  reg [((C_AXI_TYPE == 1 && C_AXI_SLAVE_TYPE == 0)?
        C_AXI_ARADDR_WIDTH:C_ADDRA_WIDTH)-1:0] araddr_reg =0;
  integer num_of_bytes_c           = 0;
  integer total_bytes              = 0;
  integer num_of_bytes_r           = 0;
  integer wrap_base_addr_r         = 0;
  integer wrap_boundary_r          = 0;

  reg [7:0] arlen_int_c=0;                  
  integer total_bytes_c            = 0;
  integer wrap_base_addr_c         = 0;
  integer wrap_boundary_c          = 0;

  assign dec_alen_c        = incr_addr_c | r_last_int_c;


  read_netlist_v8_4
  #(.C_AXI_TYPE      (1),
    .C_ADDRB_WIDTH   (C_ADDRB_WIDTH)) 
    axi_read_fsm (
    .S_AXI_INCR_ADDR(incr_addr_c),
    .S_AXI_ADDR_EN(addr_en_c),
    .S_AXI_SINGLE_TRANS(single_trans_c),
    .S_AXI_MUX_SEL(mux_sel_c),
    .S_AXI_R_LAST(r_last_c),
    .S_AXI_R_LAST_INT(r_last_int_c),

    //// AXI Global Signals
    .S_ACLK(S_ACLK),
    .S_ARESETN(S_ARESETN),
    //// AXI Full/Lite Slave Read (Read side)
    .S_AXI_ARLEN(S_AXI_ARLEN),
    .S_AXI_ARVALID(S_AXI_ARVALID),
    .S_AXI_ARREADY(S_AXI_ARREADY),
    .S_AXI_RLAST(S_AXI_RLAST),
    .S_AXI_RVALID(S_AXI_RVALID),
    .S_AXI_RREADY(S_AXI_RREADY),
    //// AXI Full/Lite Read Address Signals to BRAM
    .S_AXI_RD_EN(rd_en_c)
      );

   always@(*) begin
     num_of_bytes_c   = 2**((C_AXI_TYPE == 1 && C_AXI_SLAVE_TYPE == 0)?S_AXI_ARSIZE:0);
     total_bytes      = (num_of_bytes_r)*(arlen_int_r+1);
     wrap_base_addr_r = ((araddr_reg)/(total_bytes==0?1:total_bytes))*(total_bytes);
     wrap_boundary_r  = wrap_base_addr_r+total_bytes;

     //////// combinatorial from interface
     arlen_int_c      = (C_AXI_TYPE == 0?0:S_AXI_ARLEN);
     total_bytes_c    = (num_of_bytes_c)*(arlen_int_c+1);
     wrap_base_addr_c = ((S_AXI_ARADDR)/(total_bytes_c==0?1:total_bytes_c))*(total_bytes_c);
     wrap_boundary_c  = wrap_base_addr_c+total_bytes_c;
     
     arburst_int_c    = ((C_AXI_TYPE == 1 && C_AXI_SLAVE_TYPE == 0)?S_AXI_ARBURST:1);  
   end

  ////-------------------------------------------------------------------------
  //// BMG address generation
  ////-------------------------------------------------------------------------
   always @(posedge S_ACLK or S_ARESETN) begin
     if (S_ARESETN == 1'b1) begin
        araddr_reg 	<= 0;
   	arburst_int_r   <= 0;
	num_of_bytes_r  <= 0;
     end else begin
        if (incr_addr_c == 1'b1 && addr_en_c == 1'b1 && single_trans_c == 1'b0) begin
	      arburst_int_r    <= arburst_int_c;
	      num_of_bytes_r   <= num_of_bytes_c;
	      if (arburst_int_c == 2'b10) begin
		    if(S_AXI_ARADDR == (wrap_boundary_c-num_of_bytes_c)) begin
		      araddr_reg <= wrap_base_addr_c;
		    end else begin
		      araddr_reg <= S_AXI_ARADDR + num_of_bytes_c;
		    end
	      end else if (arburst_int_c == 2'b01 || arburst_int_c == 2'b11) begin
		    araddr_reg <= S_AXI_ARADDR + num_of_bytes_c;
	      end

        end else if (addr_en_c == 1'b1) begin
              araddr_reg       <= S_AXI_ARADDR;
	      num_of_bytes_r   <= num_of_bytes_c;
	      arburst_int_r    <= arburst_int_c;
	    end else if (incr_addr_c == 1'b1) begin
	      if (arburst_int_r == 2'b10) begin
	     	if(araddr_reg == (wrap_boundary_r-num_of_bytes_r)) begin
	     	  araddr_reg <= wrap_base_addr_r;
	     	end else begin
	     	  araddr_reg <= araddr_reg + num_of_bytes_r;
	     	end
	      end else if (arburst_int_r == 2'b01 || arburst_int_r == 2'b11) begin
		      araddr_reg   <= araddr_reg + num_of_bytes_r;
	      end
         end
         end
   end

assign araddr_out   =  ((C_AXI_TYPE == 1 && C_AXI_SLAVE_TYPE == 0)?araddr_reg[C_AXI_ARADDR_WIDTH-1:C_RANGE]:araddr_reg);
  

 ////-----------------------------------------------------------------------
    //// Counter to generate r_last_int_c from registered ARLEN  - AXI FULL FSM
 ////-----------------------------------------------------------------------
    always @(posedge S_ACLK or S_ARESETN) begin
        if (S_ARESETN == 1'b1) begin
          arlen_cntr        <= 8'h01;
	    arlen_int_r     <= 0;
	end else begin
          if (addr_en_c == 1'b1 && dec_alen_c == 1'b1 && single_trans_c == 1'b0) begin
	    arlen_int_r     <= (C_AXI_TYPE == 0?0:S_AXI_ARLEN) ;
            arlen_cntr      <= S_AXI_ARLEN - 1'b1;
	  end else if (addr_en_c == 1'b1) begin
	    arlen_int_r     <= (C_AXI_TYPE == 0?0:S_AXI_ARLEN) ;
	    arlen_cntr      <= (C_AXI_TYPE == 0?0:S_AXI_ARLEN) ;
	  end else if (dec_alen_c == 1'b1) begin
            arlen_cntr      <= arlen_cntr - 1'b1 ;
          end
	  else begin
	        arlen_cntr      <= arlen_cntr;
	  end
     end
   end

    assign r_last_int_c          = (arlen_cntr == 0 && S_AXI_RREADY == 1'b1)?1'b1:1'b0;


    ////------------------------------------------------------------------------
    //// AXI FULL FSM
    //// Mux Selection of ARADDR
    //// ARADDR is driven out from the read fsm based on the mux_sel_c
    //// Based on mux_sel either ARADDR is given out or the latched ARADDR is
    //// given out to BRAM
    ////------------------------------------------------------------------------
	assign S_AXI_ARADDR_OUT = (mux_sel_c == 1'b0)?((C_AXI_TYPE == 1 && C_AXI_SLAVE_TYPE == 0)?S_AXI_ARADDR[C_AXI_ARADDR_WIDTH-1:C_RANGE]:S_AXI_ARADDR):araddr_out;
    
    ////------------------------------------------------------------------------
    //// Assign output signals  - AXI FULL FSM
    ////------------------------------------------------------------------------
    assign S_AXI_RD_EN = rd_en_c;

    generate if (C_HAS_AXI_ID == 1) begin:gaxi_bvalid_id_r
      always @(posedge S_ACLK or S_ARESETN) begin
        if (S_ARESETN == 1'b1) begin
          S_AXI_RID <= 0;
          ar_id_r   <= 0;
	end else begin
          if (addr_en_c == 1'b1 && rd_en_c == 1'b1) begin
             S_AXI_RID <= S_AXI_ARID;
             ar_id_r <= S_AXI_ARID;
          end else if (addr_en_c == 1'b1 && rd_en_c == 1'b0) begin
	     ar_id_r <= S_AXI_ARID;
          end else if (rd_en_c == 1'b1) begin
             S_AXI_RID <= ar_id_r;
          end
        end
     end 
     end 
   endgenerate 

endmodule

module blk_mem_axi_regs_fwd_v8_4
  #(parameter C_DATA_WIDTH = 8
   )(
    input   ACLK,
    input   ARESET,
    input   S_VALID,
    output  S_READY,
    input   [C_DATA_WIDTH-1:0] S_PAYLOAD_DATA,
    output  M_VALID,
    input   M_READY,
    output  reg [C_DATA_WIDTH-1:0] M_PAYLOAD_DATA
    );

    reg  [C_DATA_WIDTH-1:0] STORAGE_DATA;
    wire S_READY_I;
    reg  M_VALID_I;
    reg  [1:0] ARESET_D;

      //assign local signal to its output signal
      assign S_READY = S_READY_I;
      assign M_VALID = M_VALID_I;

   always @(posedge ACLK) begin
	  ARESET_D <= {ARESET_D[0], ARESET};
	end
      
      //Save payload data whenever we have a transaction on the slave side
   always @(posedge ACLK or ARESET) begin
        if (ARESET == 1'b1) begin
  	    STORAGE_DATA <= 0;
	end else begin
	  if(S_VALID == 1'b1 && S_READY_I == 1'b1 ) begin
  	    STORAGE_DATA <= S_PAYLOAD_DATA;
  	  end
  	end
     end

   always @(posedge ACLK) begin
     M_PAYLOAD_DATA = STORAGE_DATA;
   end
      
      //M_Valid set to high when we have a completed transfer on slave side
      //Is removed on a M_READY except if we have a new transfer on the slave side
       
   always @(posedge ACLK or ARESET_D) begin
	if (ARESET_D != 2'b00) begin
  	    M_VALID_I <= 1'b0;
	end else begin
	  if (S_VALID == 1'b1) begin
	    //Always set M_VALID_I when slave side is valid
            M_VALID_I <= 1'b1;
	  end else if (M_READY == 1'b1 ) begin
	    //Clear (or keep) when no slave side is valid but master side is ready
	    M_VALID_I <= 1'b0;
	  end
	end
      end

      //Slave Ready is either when Master side drives M_READY or we have space in our storage data
      assign S_READY_I = (M_READY || (!M_VALID_I)) && !(|(ARESET_D));

  endmodule

//*****************************************************************************
// Output Register Stage module
//
// This module builds the output register stages of the memory. This module is 
// instantiated in the main memory module (blk_mem_gen_v8_4_4) which is
// declared/implemented further down in this file.
//*****************************************************************************
module blk_mem_gen_v8_4_4_output_stage
  #(parameter C_FAMILY              = "virtex7",
    parameter C_XDEVICEFAMILY       = "virtex7",
    parameter C_RST_TYPE            = "SYNC",
    parameter C_HAS_RST             = 0,
    parameter C_RSTRAM              = 0,
    parameter C_RST_PRIORITY        = "CE",
    parameter C_INIT_VAL            = "0",
    parameter C_HAS_EN              = 0,
    parameter C_HAS_REGCE           = 0,
    parameter C_DATA_WIDTH          = 32,
    parameter C_ADDRB_WIDTH         = 10,
    parameter C_HAS_MEM_OUTPUT_REGS = 0,
    parameter C_USE_SOFTECC         = 0,
    parameter C_USE_ECC             = 0,
    parameter NUM_STAGES            = 1,
	parameter C_EN_ECC_PIPE         = 0,
    parameter FLOP_DELAY            = 100
  )
  (
   input                         CLK,
   input                         RST,
   input                         EN,
   input                         REGCE,
   input      [C_DATA_WIDTH-1:0] DIN_I,
   output reg [C_DATA_WIDTH-1:0] DOUT,
   input                         SBITERR_IN_I,
   input                         DBITERR_IN_I,
   output reg                    SBITERR,
   output reg                    DBITERR,
   input      [C_ADDRB_WIDTH-1:0]    RDADDRECC_IN_I,
   input                         ECCPIPECE,    
   output reg [C_ADDRB_WIDTH-1:0]    RDADDRECC
);

//******************************
// Port and Generic Definitions
//******************************
  //////////////////////////////////////////////////////////////////////////
  // Generic Definitions
  //////////////////////////////////////////////////////////////////////////
  // C_FAMILY,C_XDEVICEFAMILY: Designates architecture targeted. The following
  //                           options are available - "spartan3", "spartan6", 
  //                           "virtex4", "virtex5", "virtex6" and "virtex6l".
  // C_RST_TYPE              : Type of reset - Synchronous or Asynchronous
  // C_HAS_RST               : Determines the presence of the RST port
  // C_RSTRAM                : Determines if special reset behavior is used
  // C_RST_PRIORITY          : Determines the priority between CE and SR
  // C_INIT_VAL              : Initialization value
  // C_HAS_EN                : Determines the presence of the EN port
  // C_HAS_REGCE             : Determines the presence of the REGCE port
  // C_DATA_WIDTH            : Memory write/read width
  // C_ADDRB_WIDTH           : Width of the ADDRB input port
  // C_HAS_MEM_OUTPUT_REGS   : Designates the use of a register at the output 
  //                           of the RAM primitive
  // C_USE_SOFTECC           : Determines if the Soft ECC feature is used or
  //                           not. Only applicable Spartan-6
  // C_USE_ECC               : Determines if the ECC feature is used or
  //                           not. Only applicable for V5 and V6
  // NUM_STAGES              : Determines the number of output stages
  // FLOP_DELAY              : Constant delay for register assignments
  //////////////////////////////////////////////////////////////////////////
  // Port Definitions
  //////////////////////////////////////////////////////////////////////////
  // CLK    : Clock to synchronize all read and write operations
  // RST    : Reset input to reset memory outputs to a user-defined 
  //           reset state
  // EN     : Enable all read and write operations
  // REGCE  : Register Clock Enable to control each pipeline output
  //           register stages
  // DIN    : Data input to the Output stage.
  // DOUT   : Final Data output
  // SBITERR_IN    : SBITERR input signal to the Output stage.
  // SBITERR       : Final SBITERR Output signal.
  // DBITERR_IN    : DBITERR input signal to the Output stage.
  // DBITERR       : Final DBITERR Output signal.
  // RDADDRECC_IN  : RDADDRECC input signal to the Output stage.
  // RDADDRECC     : Final RDADDRECC Output signal.
  //////////////////////////////////////////////////////////////////////////

//  Fix for CR-509792

  localparam REG_STAGES  = (NUM_STAGES < 2) ? 1 : NUM_STAGES-1;
  
  // Declare the pipeline registers 
  // (includes mem output reg, mux pipeline stages, and mux output reg)
  reg [C_DATA_WIDTH*REG_STAGES-1:0] out_regs;
  reg [C_ADDRB_WIDTH*REG_STAGES-1:0] rdaddrecc_regs;
  reg [REG_STAGES-1:0] sbiterr_regs;
  reg [REG_STAGES-1:0] dbiterr_regs;

  reg [C_DATA_WIDTH*8-1:0]          init_str = C_INIT_VAL;
  reg [C_DATA_WIDTH-1:0]            init_val ;

  //*********************************************
  // Wire off optional inputs based on parameters
  //*********************************************
  wire                              en_i;
  wire                              regce_i;
  wire                              rst_i;
  
  // Internal signals
  reg [C_DATA_WIDTH-1:0]     DIN;
  reg [C_ADDRB_WIDTH-1:0]    RDADDRECC_IN;
  reg                        SBITERR_IN;
  reg                        DBITERR_IN;


  // Internal enable for output registers is tied to user EN or '1' depending
  // on parameters
  assign   en_i    = (C_HAS_EN==0 || EN);

  // Internal register enable for output registers is tied to user REGCE, EN or
  // '1' depending on parameters
  // For V4 ECC, REGCE is always 1
  // Virtex-4 ECC Not Yet Supported
  assign   regce_i = ((C_HAS_REGCE==1) && REGCE) ||
                     ((C_HAS_REGCE==0) && (C_HAS_EN==0 || EN));
  
  //Internal SRR is tied to user RST or '0' depending on parameters
  assign   rst_i   = (C_HAS_RST==1) && RST;

  //****************************************************
  // Power on: load up the output registers and latches
  //****************************************************
  initial begin
    if (!($sscanf(init_str, "%h", init_val))) begin
      init_val = 0;
    end
    DOUT = init_val;
    RDADDRECC = 0;
    SBITERR = 1'b0;
    DBITERR = 1'b0;
	DIN     = {(C_DATA_WIDTH){1'b0}};
    RDADDRECC_IN = 0;
    SBITERR_IN = 0;
	DBITERR_IN = 0;
	// This will be one wider than need, but 0 is an error
    out_regs = {(REG_STAGES+1){init_val}};
    rdaddrecc_regs = 0;
    sbiterr_regs = {(REG_STAGES+1){1'b0}};
    dbiterr_regs = {(REG_STAGES+1){1'b0}};
  end

 //***********************************************
 // NUM_STAGES = 0 (No output registers. RAM only)
 //***********************************************
  generate if (NUM_STAGES == 0) begin : zero_stages
    always @* begin
      DOUT = DIN;
      RDADDRECC = RDADDRECC_IN;
      SBITERR = SBITERR_IN;
      DBITERR = DBITERR_IN;
    end
  end
  endgenerate

  generate if (C_EN_ECC_PIPE == 0) begin : no_ecc_pipe_reg
    always @* begin
      DIN = DIN_I;
	  SBITERR_IN = SBITERR_IN_I;
      DBITERR_IN = DBITERR_IN_I;
      RDADDRECC_IN = RDADDRECC_IN_I;
    end
  end
  endgenerate

  generate if (C_EN_ECC_PIPE == 1) begin : with_ecc_pipe_reg
    always @(posedge CLK) begin
      if(ECCPIPECE == 1) begin
	    DIN <= #FLOP_DELAY DIN_I;
        SBITERR_IN <= #FLOP_DELAY SBITERR_IN_I;
        DBITERR_IN <= #FLOP_DELAY DBITERR_IN_I;
        RDADDRECC_IN <= #FLOP_DELAY RDADDRECC_IN_I;
      end
	end
  end
  endgenerate


  //***********************************************
  // NUM_STAGES = 1 
  // (Mem Output Reg only or Mux Output Reg only)
  //***********************************************

  // Possible valid combinations: 
  // Note: C_HAS_MUX_OUTPUT_REGS_*=0 when (C_RSTRAM_*=1)
  //   +-----------------------------------------+
  //   |   C_RSTRAM_*   |  Reset Behavior        |
  //   +----------------+------------------------+
  //   |       0        |   Normal Behavior      |
  //   +----------------+------------------------+
  //   |       1        |  Special Behavior      |
  //   +----------------+------------------------+
  //
  // Normal = REGCE gates reset, as in the case of all families except S3ADSP.
  // Special = EN gates reset, as in the case of S3ADSP.

  generate if (NUM_STAGES == 1 && 
                 (C_RSTRAM == 0 || (C_RSTRAM == 1 && (C_XDEVICEFAMILY != "spartan3adsp" && C_XDEVICEFAMILY != "aspartan3adsp" )) ||
                  C_HAS_MEM_OUTPUT_REGS == 0 || C_HAS_RST == 0))
  begin : one_stages_norm

      always @(posedge CLK) begin
        if (C_RST_PRIORITY == "CE") begin //REGCE has priority
          if (regce_i && rst_i) begin
            DOUT    <= #FLOP_DELAY init_val;
            RDADDRECC <= #FLOP_DELAY 0;
            SBITERR <= #FLOP_DELAY 1'b0;
            DBITERR <= #FLOP_DELAY 1'b0;
          end else if (regce_i) begin
            DOUT    <= #FLOP_DELAY DIN;
            RDADDRECC <= #FLOP_DELAY RDADDRECC_IN;
            SBITERR <= #FLOP_DELAY SBITERR_IN;
            DBITERR <= #FLOP_DELAY DBITERR_IN;
          end //Output signal assignments
        end else begin             //RST has priority
          if (rst_i) begin
            DOUT    <= #FLOP_DELAY init_val;
            RDADDRECC <= #FLOP_DELAY RDADDRECC_IN;
            SBITERR <= #FLOP_DELAY 1'b0;
            DBITERR <= #FLOP_DELAY 1'b0;
          end else if (regce_i) begin
            DOUT    <= #FLOP_DELAY DIN;
            RDADDRECC <= #FLOP_DELAY RDADDRECC_IN;
            SBITERR <= #FLOP_DELAY SBITERR_IN;
            DBITERR <= #FLOP_DELAY DBITERR_IN;
          end //Output signal assignments
        end //end Priority conditions
    end //end RST Type conditions
  end //end one_stages_norm generate statement
  endgenerate

  // Special Reset Behavior for S3ADSP
  generate if (NUM_STAGES == 1 && C_RSTRAM == 1 && (C_XDEVICEFAMILY =="spartan3adsp" || C_XDEVICEFAMILY =="aspartan3adsp"))
  begin : one_stage_splbhv
    always @(posedge CLK) begin
      if (en_i && rst_i) begin
        DOUT <= #FLOP_DELAY init_val;
      end else if (regce_i && !rst_i) begin
        DOUT <= #FLOP_DELAY DIN;
      end //Output signal assignments
    end  //end CLK
  end //end one_stage_splbhv generate statement
  endgenerate

 //************************************************************
 // NUM_STAGES > 1 
 // Mem Output Reg + Mux Output Reg
 //              or 
 // Mem Output Reg + Mux Pipeline Stages (>0) + Mux Output Reg
 //              or 
 // Mux Pipeline Stages (>0) + Mux Output Reg
 //*************************************************************
 generate if (NUM_STAGES > 1) begin : multi_stage
       //Asynchronous Reset
      always @(posedge CLK) begin
        if (C_RST_PRIORITY == "CE") begin  //REGCE has priority
          if (regce_i && rst_i) begin
            DOUT    <= #FLOP_DELAY init_val;
            RDADDRECC <= #FLOP_DELAY 0;
            SBITERR <= #FLOP_DELAY 1'b0;
            DBITERR <= #FLOP_DELAY 1'b0;
          end else if (regce_i) begin
            DOUT    <= #FLOP_DELAY
                          out_regs[C_DATA_WIDTH*(NUM_STAGES-2)+:C_DATA_WIDTH];
            RDADDRECC <= #FLOP_DELAY rdaddrecc_regs[C_ADDRB_WIDTH*(NUM_STAGES-2)+:C_ADDRB_WIDTH];
            SBITERR <= #FLOP_DELAY sbiterr_regs[NUM_STAGES-2];
            DBITERR <= #FLOP_DELAY dbiterr_regs[NUM_STAGES-2];
          end //Output signal assignments
        end else begin                     //RST has priority
          if (rst_i) begin
            DOUT    <= #FLOP_DELAY init_val;
            RDADDRECC <= #FLOP_DELAY 0;
            SBITERR <= #FLOP_DELAY 1'b0;
            DBITERR <= #FLOP_DELAY 1'b0;
          end else if (regce_i) begin
            DOUT    <= #FLOP_DELAY
                          out_regs[C_DATA_WIDTH*(NUM_STAGES-2)+:C_DATA_WIDTH];
            RDADDRECC <= #FLOP_DELAY rdaddrecc_regs[C_ADDRB_WIDTH*(NUM_STAGES-2)+:C_ADDRB_WIDTH];
            SBITERR <= #FLOP_DELAY sbiterr_regs[NUM_STAGES-2];
            DBITERR <= #FLOP_DELAY dbiterr_regs[NUM_STAGES-2];
          end //Output signal assignments
        end   //end Priority conditions
         // Shift the data through the output stages
         if (en_i) begin
           out_regs     <= #FLOP_DELAY (out_regs << C_DATA_WIDTH) | DIN;
           rdaddrecc_regs <= #FLOP_DELAY (rdaddrecc_regs << C_ADDRB_WIDTH) | RDADDRECC_IN;
           sbiterr_regs <= #FLOP_DELAY (sbiterr_regs << 1) | SBITERR_IN;
           dbiterr_regs <= #FLOP_DELAY (dbiterr_regs << 1) | DBITERR_IN;
         end
      end  //end CLK
  end //end multi_stage generate statement
  endgenerate
endmodule

module blk_mem_gen_v8_4_4_softecc_output_reg_stage
  #(parameter C_DATA_WIDTH          = 32,
    parameter C_ADDRB_WIDTH         = 10,
    parameter C_HAS_SOFTECC_OUTPUT_REGS_B= 0,
    parameter C_USE_SOFTECC         = 0,
    parameter FLOP_DELAY            = 100
  )
  (
   input                         CLK,
   input      [C_DATA_WIDTH-1:0] DIN,
   output reg [C_DATA_WIDTH-1:0] DOUT,
   input                         SBITERR_IN,
   input                         DBITERR_IN,
   output reg                    SBITERR,
   output reg                    DBITERR,
   input      [C_ADDRB_WIDTH-1:0]             RDADDRECC_IN,
   output reg [C_ADDRB_WIDTH-1:0]             RDADDRECC
);

//******************************
// Port and Generic Definitions
//******************************
  //////////////////////////////////////////////////////////////////////////
  // Generic Definitions
  //////////////////////////////////////////////////////////////////////////
  // C_DATA_WIDTH                  : Memory write/read width
  // C_ADDRB_WIDTH                 : Width of the ADDRB input port
  // C_HAS_SOFTECC_OUTPUT_REGS_B   : Designates the use of a register at the output 
  //                                 of the RAM primitive
  // C_USE_SOFTECC                 : Determines if the Soft ECC feature is used or
  //                                 not. Only applicable Spartan-6
  // FLOP_DELAY                    : Constant delay for register assignments
  //////////////////////////////////////////////////////////////////////////
  // Port Definitions
  //////////////////////////////////////////////////////////////////////////
  // CLK    : Clock to synchronize all read and write operations
  // DIN    : Data input to the Output stage.
  // DOUT   : Final Data output
  // SBITERR_IN    : SBITERR input signal to the Output stage.
  // SBITERR       : Final SBITERR Output signal.
  // DBITERR_IN    : DBITERR input signal to the Output stage.
  // DBITERR       : Final DBITERR Output signal.
  // RDADDRECC_IN  : RDADDRECC input signal to the Output stage.
  // RDADDRECC     : Final RDADDRECC Output signal.
  //////////////////////////////////////////////////////////////////////////

  reg [C_DATA_WIDTH-1:0]           dout_i       = 0;
  reg                              sbiterr_i    = 0;
  reg                              dbiterr_i    = 0;
  reg [C_ADDRB_WIDTH-1:0]          rdaddrecc_i  = 0;

 //***********************************************
 // NO OUTPUT REGISTERS.
 //***********************************************
  generate if (C_HAS_SOFTECC_OUTPUT_REGS_B==0) begin : no_output_stage
    always @* begin
      DOUT = DIN;
      RDADDRECC = RDADDRECC_IN;
      SBITERR = SBITERR_IN;
      DBITERR = DBITERR_IN;
    end
  end
  endgenerate

 //***********************************************
 // WITH OUTPUT REGISTERS.
 //***********************************************
  generate if (C_HAS_SOFTECC_OUTPUT_REGS_B==1) begin : has_output_stage
      always @(posedge CLK) begin
      dout_i <= #FLOP_DELAY DIN;
      rdaddrecc_i <= #FLOP_DELAY RDADDRECC_IN;
      sbiterr_i <= #FLOP_DELAY SBITERR_IN;
      dbiterr_i <= #FLOP_DELAY DBITERR_IN;
      end

      always @* begin
      DOUT = dout_i;
      RDADDRECC = rdaddrecc_i;
      SBITERR = sbiterr_i;
      DBITERR = dbiterr_i;
      end //end always
      end //end in_or_out_stage generate statement
 endgenerate

endmodule


//*****************************************************************************
// Main Memory module
//
// This module is the top-level behavioral model and this implements the RAM 
//*****************************************************************************
module blk_mem_gen_v8_4_4_mem_module
  #(parameter C_CORENAME                = "blk_mem_gen_v8_4_4",
    parameter C_FAMILY                  = "virtex7",
    parameter C_XDEVICEFAMILY           = "virtex7",
    parameter C_MEM_TYPE                = 2,
    parameter C_BYTE_SIZE               = 9,
    parameter C_USE_BRAM_BLOCK          = 0,
    parameter C_ALGORITHM               = 1,
    parameter C_PRIM_TYPE               = 3,
    parameter C_LOAD_INIT_FILE          = 0,
    parameter C_INIT_FILE_NAME          = "",
    parameter C_INIT_FILE               = "",
    parameter C_USE_DEFAULT_DATA        = 0,
    parameter C_DEFAULT_DATA            = "0",
    parameter C_RST_TYPE                = "SYNC",
    parameter C_HAS_RSTA                = 0,
    parameter C_RST_PRIORITY_A          = "CE",
    parameter C_RSTRAM_A                = 0,
    parameter C_INITA_VAL               = "0",
    parameter C_HAS_ENA                 = 1,
    parameter C_HAS_REGCEA              = 0,
    parameter C_USE_BYTE_WEA            = 0,
    parameter C_WEA_WIDTH               = 1,
    parameter C_WRITE_MODE_A            = "WRITE_FIRST",
    parameter C_WRITE_WIDTH_A           = 32,
    parameter C_READ_WIDTH_A            = 32,
    parameter C_WRITE_DEPTH_A           = 64,
    parameter C_READ_DEPTH_A            = 64,
    parameter C_ADDRA_WIDTH             = 5,
    parameter C_HAS_RSTB                = 0,
    parameter C_RST_PRIORITY_B          = "CE",
    parameter C_RSTRAM_B                = 0,
    parameter C_INITB_VAL               = "",
    parameter C_HAS_ENB                 = 1,
    parameter C_HAS_REGCEB              = 0,
    parameter C_USE_BYTE_WEB            = 0,
    parameter C_WEB_WIDTH               = 1,
    parameter C_WRITE_MODE_B            = "WRITE_FIRST",
    parameter C_WRITE_WIDTH_B           = 32,
    parameter C_READ_WIDTH_B            = 32,
    parameter C_WRITE_DEPTH_B           = 64,
    parameter C_READ_DEPTH_B            = 64,
    parameter C_ADDRB_WIDTH             = 5,
    parameter C_HAS_MEM_OUTPUT_REGS_A   = 0,
    parameter C_HAS_MEM_OUTPUT_REGS_B   = 0,
    parameter C_HAS_MUX_OUTPUT_REGS_A   = 0,
    parameter C_HAS_MUX_OUTPUT_REGS_B   = 0,
    parameter C_HAS_SOFTECC_INPUT_REGS_A = 0,
    parameter C_HAS_SOFTECC_OUTPUT_REGS_B= 0,
    parameter C_MUX_PIPELINE_STAGES     = 0,
    parameter C_USE_SOFTECC             = 0,
    parameter C_USE_ECC                 = 0,
    parameter C_HAS_INJECTERR           = 0,
    parameter C_SIM_COLLISION_CHECK     = "NONE",
    parameter C_COMMON_CLK              = 1,
    parameter FLOP_DELAY                = 100,
    parameter C_DISABLE_WARN_BHV_COLL   = 0,
	parameter C_EN_ECC_PIPE             = 0,
    parameter C_DISABLE_WARN_BHV_RANGE  = 0
  )
  (input                       CLKA,
   input                       RSTA,
   input                       ENA,
   input                       REGCEA,
   input [C_WEA_WIDTH-1:0]     WEA,
   input [C_ADDRA_WIDTH-1:0]   ADDRA,
   input [C_WRITE_WIDTH_A-1:0] DINA,
   output [C_READ_WIDTH_A-1:0] DOUTA,
   input                       CLKB,
   input                       RSTB,
   input                       ENB,
   input                       REGCEB,
   input [C_WEB_WIDTH-1:0]     WEB,
   input [C_ADDRB_WIDTH-1:0]   ADDRB,
   input [C_WRITE_WIDTH_B-1:0] DINB,
   output [C_READ_WIDTH_B-1:0] DOUTB,
   input                       INJECTSBITERR,
   input                       INJECTDBITERR,
   input                       ECCPIPECE,
   input                       SLEEP,
   output                      SBITERR,
   output                      DBITERR,
   output [C_ADDRB_WIDTH-1:0]  RDADDRECC
  );
//******************************
// Port and Generic Definitions
//******************************
  //////////////////////////////////////////////////////////////////////////
  // Generic Definitions
  //////////////////////////////////////////////////////////////////////////
  // C_CORENAME              : Instance name of the Block Memory Generator core
  // C_FAMILY,C_XDEVICEFAMILY: Designates architecture targeted. The following
  //                           options are available - "spartan3", "spartan6", 
  //                           "virtex4", "virtex5", "virtex6" and "virtex6l".
  // C_MEM_TYPE              : Designates memory type.
  //                           It can be
  //                           0 - Single Port Memory
  //                           1 - Simple Dual Port Memory
  //                           2 - True Dual Port Memory
  //                           3 - Single Port Read Only Memory
  //                           4 - Dual Port Read Only Memory
  // C_BYTE_SIZE             : Size of a byte (8 or 9 bits)
  // C_ALGORITHM             : Designates the algorithm method used
  //                           for constructing the memory.
  //                           It can be Fixed_Primitives, Minimum_Area or 
  //                           Low_Power
  // C_PRIM_TYPE             : Designates the user selected primitive used to 
  //                           construct the memory.
  //
  // C_LOAD_INIT_FILE        : Designates the use of an initialization file to
  //                           initialize memory contents.
  // C_INIT_FILE_NAME        : Memory initialization file name.
  // C_USE_DEFAULT_DATA      : Designates whether to fill remaining
  //                           initialization space with default data
  // C_DEFAULT_DATA          : Default value of all memory locations
  //                           not initialized by the memory
  //                           initialization file.
  // C_RST_TYPE              : Type of reset - Synchronous or Asynchronous
  // C_HAS_RSTA              : Determines the presence of the RSTA port
  // C_RST_PRIORITY_A        : Determines the priority between CE and SR for 
  //                           Port A.
  // C_RSTRAM_A              : Determines if special reset behavior is used for
  //                           Port A
  // C_INITA_VAL             : The initialization value for Port A
  // C_HAS_ENA               : Determines the presence of the ENA port
  // C_HAS_REGCEA            : Determines the presence of the REGCEA port
  // C_USE_BYTE_WEA          : Determines if the Byte Write is used or not.
  // C_WEA_WIDTH             : The width of the WEA port
  // C_WRITE_MODE_A          : Configurable write mode for Port A. It can be
  //                           WRITE_FIRST, READ_FIRST or NO_CHANGE.
  // C_WRITE_WIDTH_A         : Memory write width for Port A.
  // C_READ_WIDTH_A          : Memory read width for Port A.
  // C_WRITE_DEPTH_A         : Memory write depth for Port A.
  // C_READ_DEPTH_A          : Memory read depth for Port A.
  // C_ADDRA_WIDTH           : Width of the ADDRA input port
  // C_HAS_RSTB              : Determines the presence of the RSTB port
  // C_RST_PRIORITY_B        : Determines the priority between CE and SR for 
  //                           Port B.
  // C_RSTRAM_B              : Determines if special reset behavior is used for
  //                           Port B
  // C_INITB_VAL             : The initialization value for Port B
  // C_HAS_ENB               : Determines the presence of the ENB port
  // C_HAS_REGCEB            : Determines the presence of the REGCEB port
  // C_USE_BYTE_WEB          : Determines if the Byte Write is used or not.
  // C_WEB_WIDTH             : The width of the WEB port
  // C_WRITE_MODE_B          : Configurable write mode for Port B. It can be
  //                           WRITE_FIRST, READ_FIRST or NO_CHANGE.
  // C_WRITE_WIDTH_B         : Memory write width for Port B.
  // C_READ_WIDTH_B          : Memory read width for Port B.
  // C_WRITE_DEPTH_B         : Memory write depth for Port B.
  // C_READ_DEPTH_B          : Memory read depth for Port B.
  // C_ADDRB_WIDTH           : Width of the ADDRB input port
  // C_HAS_MEM_OUTPUT_REGS_A : Designates the use of a register at the output 
  //                           of the RAM primitive for Port A.
  // C_HAS_MEM_OUTPUT_REGS_B : Designates the use of a register at the output 
  //                           of the RAM primitive for Port B.
  // C_HAS_MUX_OUTPUT_REGS_A : Designates the use of a register at the output
  //                           of the MUX for Port A.
  // C_HAS_MUX_OUTPUT_REGS_B : Designates the use of a register at the output
  //                           of the MUX for Port B.
  // C_MUX_PIPELINE_STAGES   : Designates the number of pipeline stages in 
  //                           between the muxes.
  // C_USE_SOFTECC           : Determines if the Soft ECC feature is used or
  //                           not. Only applicable Spartan-6
  // C_USE_ECC               : Determines if the ECC feature is used or
  //                           not. Only applicable for V5 and V6
  // C_HAS_INJECTERR         : Determines if the error injection pins
  //                           are present or not. If the ECC feature
  //                           is not used, this value is defaulted to
  //                           0, else the following are the allowed 
  //                           values:
  //                         0 : No INJECTSBITERR or INJECTDBITERR pins
  //                         1 : Only INJECTSBITERR pin exists
  //                         2 : Only INJECTDBITERR pin exists
  //                         3 : Both INJECTSBITERR and INJECTDBITERR pins exist
  // C_SIM_COLLISION_CHECK   : Controls the disabling of Unisim model collision
  //                           warnings. It can be "ALL", "NONE", 
  //                           "Warnings_Only" or "Generate_X_Only".
  // C_COMMON_CLK            : Determins if the core has a single CLK input.
  // C_DISABLE_WARN_BHV_COLL : Controls the Behavioral Model Collision warnings
  // C_DISABLE_WARN_BHV_RANGE: Controls the Behavioral Model Out of Range 
  //                           warnings
  //////////////////////////////////////////////////////////////////////////
  // Port Definitions
  //////////////////////////////////////////////////////////////////////////
  // CLKA    : Clock to synchronize all read and write operations of Port A.
  // RSTA    : Reset input to reset memory outputs to a user-defined 
  //           reset state for Port A.
  // ENA     : Enable all read and write operations of Port A.
  // REGCEA  : Register Clock Enable to control each pipeline output
  //           register stages for Port A.
  // WEA     : Write Enable to enable all write operations of Port A.
  // ADDRA   : Address of Port A.
  // DINA    : Data input of Port A.
  // DOUTA   : Data output of Port A.
  // CLKB    : Clock to synchronize all read and write operations of Port B.
  // RSTB    : Reset input to reset memory outputs to a user-defined 
  //           reset state for Port B.
  // ENB     : Enable all read and write operations of Port B.
  // REGCEB  : Register Clock Enable to control each pipeline output
  //           register stages for Port B.
  // WEB     : Write Enable to enable all write operations of Port B.
  // ADDRB   : Address of Port B.
  // DINB    : Data input of Port B.
  // DOUTB   : Data output of Port B.
  // INJECTSBITERR : Single Bit ECC Error Injection Pin.
  // INJECTDBITERR : Double Bit ECC Error Injection Pin.
  // SBITERR       : Output signal indicating that a Single Bit ECC Error has been
  //                 detected and corrected.
  // DBITERR       : Output signal indicating that a Double Bit ECC Error has been
  //                 detected.
  // RDADDRECC     : Read Address Output signal indicating address at which an
  //                 ECC error has occurred.
  //////////////////////////////////////////////////////////////////////////


// Note: C_CORENAME parameter is hard-coded to "blk_mem_gen_v8_4_4" and it is
// only used by this module to print warning messages. It is neither passed 
// down from blk_mem_gen_v8_4_4_xst.v nor present in the instantiation template
// coregen generates
  
  //***************************************************************************
  // constants for the core behavior
  //***************************************************************************
  // file handles for logging
  //--------------------------------------------------
  localparam ADDRFILE           = 32'h8000_0001; //stdout for addr out of range
  localparam COLLFILE           = 32'h8000_0001; //stdout for coll detection
  localparam ERRFILE            = 32'h8000_0001; //stdout for file I/O errors

  // other constants
  //--------------------------------------------------
  localparam COLL_DELAY         = 100;  // 100 ps

  // locally derived parameters to determine memory shape
  //-----------------------------------------------------

  localparam CHKBIT_WIDTH = (C_WRITE_WIDTH_A>57 ? 8 : (C_WRITE_WIDTH_A>26 ? 7 : (C_WRITE_WIDTH_A>11 ? 6 : (C_WRITE_WIDTH_A>4 ? 5 : (C_WRITE_WIDTH_A<5 ? 4 :0))))); 

  localparam MIN_WIDTH_A = (C_WRITE_WIDTH_A < C_READ_WIDTH_A) ?
             C_WRITE_WIDTH_A : C_READ_WIDTH_A;
  localparam MIN_WIDTH_B = (C_WRITE_WIDTH_B < C_READ_WIDTH_B) ?
             C_WRITE_WIDTH_B : C_READ_WIDTH_B;
  localparam MIN_WIDTH = (MIN_WIDTH_A < MIN_WIDTH_B) ?
             MIN_WIDTH_A : MIN_WIDTH_B;

  localparam MAX_DEPTH_A = (C_WRITE_DEPTH_A > C_READ_DEPTH_A) ?
             C_WRITE_DEPTH_A : C_READ_DEPTH_A;
  localparam MAX_DEPTH_B = (C_WRITE_DEPTH_B > C_READ_DEPTH_B) ?
             C_WRITE_DEPTH_B : C_READ_DEPTH_B;
  localparam MAX_DEPTH = (MAX_DEPTH_A > MAX_DEPTH_B) ?
             MAX_DEPTH_A : MAX_DEPTH_B;


  // locally derived parameters to assist memory access
  //----------------------------------------------------
  // Calculate the width ratios of each port with respect to the narrowest
  // port
  localparam WRITE_WIDTH_RATIO_A = C_WRITE_WIDTH_A/MIN_WIDTH;
  localparam READ_WIDTH_RATIO_A  = C_READ_WIDTH_A/MIN_WIDTH;
  localparam WRITE_WIDTH_RATIO_B = C_WRITE_WIDTH_B/MIN_WIDTH;
  localparam READ_WIDTH_RATIO_B  = C_READ_WIDTH_B/MIN_WIDTH;

  // To modify the LSBs of the 'wider' data to the actual
  // address value
  //----------------------------------------------------
  localparam WRITE_ADDR_A_DIV  = C_WRITE_WIDTH_A/MIN_WIDTH_A;
  localparam READ_ADDR_A_DIV   = C_READ_WIDTH_A/MIN_WIDTH_A;
  localparam WRITE_ADDR_B_DIV  = C_WRITE_WIDTH_B/MIN_WIDTH_B;
  localparam READ_ADDR_B_DIV   = C_READ_WIDTH_B/MIN_WIDTH_B;

  // If byte writes aren't being used, make sure BYTE_SIZE is not
  // wider than the memory elements to avoid compilation warnings
  localparam BYTE_SIZE   = (C_BYTE_SIZE < MIN_WIDTH) ? C_BYTE_SIZE : MIN_WIDTH;

  // The memory
  reg [MIN_WIDTH-1:0]      memory [0:MAX_DEPTH-1];
  reg [MIN_WIDTH-1:0]      temp_mem_array [0:MAX_DEPTH-1];
  reg [C_WRITE_WIDTH_A+CHKBIT_WIDTH-1:0] doublebit_error = 3;
  // ECC error arrays
  reg                      sbiterr_arr [0:MAX_DEPTH-1];
  reg                      dbiterr_arr [0:MAX_DEPTH-1];

  reg                 softecc_sbiterr_arr [0:MAX_DEPTH-1];
  reg                 softecc_dbiterr_arr [0:MAX_DEPTH-1];
  // Memory output 'latches'
  reg [C_READ_WIDTH_A-1:0] memory_out_a;
  reg [C_READ_WIDTH_B-1:0] memory_out_b;

  // ECC error inputs and outputs from output_stage module:
  reg                      sbiterr_in;
  wire                     sbiterr_sdp;
  reg                      dbiterr_in;
  wire                     dbiterr_sdp;

  wire [C_READ_WIDTH_B-1:0]            dout_i;
  wire                     dbiterr_i;
  wire                     sbiterr_i;
  wire [C_ADDRB_WIDTH-1:0]  rdaddrecc_i;

  reg [C_ADDRB_WIDTH-1:0]  rdaddrecc_in;
  wire [C_ADDRB_WIDTH-1:0]  rdaddrecc_sdp;

  // Reset values
  reg [C_READ_WIDTH_A-1:0] inita_val;
  reg [C_READ_WIDTH_B-1:0] initb_val;

  // Collision detect
  reg                      is_collision;
  reg                      is_collision_a, is_collision_delay_a;
  reg                      is_collision_b, is_collision_delay_b;

  // Temporary variables for initialization
  //---------------------------------------
  integer                  status;
  integer                  initfile;
  integer                  meminitfile;
  // data input buffer
  reg [C_WRITE_WIDTH_A-1:0]    mif_data;
  reg [C_WRITE_WIDTH_A-1:0]    mem_data;
  // string values in hex
  reg [C_READ_WIDTH_A*8-1:0]   inita_str       = C_INITA_VAL;
  reg [C_READ_WIDTH_B*8-1:0]   initb_str       = C_INITB_VAL;
  reg [C_WRITE_WIDTH_A*8-1:0]  default_data_str = C_DEFAULT_DATA;
  // initialization filename
  reg [1023*8-1:0]             init_file_str    = C_INIT_FILE_NAME;
  reg [1023*8-1:0]             mem_init_file_str    = C_INIT_FILE;


  //Constants used to calculate the effective address widths for each of the 
  //four ports. 
  integer cnt = 1;
  integer write_addr_a_width, read_addr_a_width;
  integer write_addr_b_width, read_addr_b_width;

    localparam C_FAMILY_LOCALPARAM =      (C_FAMILY=="virtexuplushbm"?"virtex7":(C_FAMILY=="zynquplusrfsoc"?"virtex7":(C_FAMILY=="zynquplus"?"virtex7":(C_FAMILY=="kintexuplus"?"virtex7":(C_FAMILY=="virtexuplus"?"virtex7":(C_FAMILY=="virtexu"?"virtex7":(C_FAMILY=="kintexu" ? "virtex7":(C_FAMILY=="virtex7" ? "virtex7" : (C_FAMILY=="virtex7l" ? "virtex7" : (C_FAMILY=="qvirtex7" ? "virtex7" : (C_FAMILY=="qvirtex7l" ? "virtex7" : (C_FAMILY=="kintex7" ? "virtex7" : (C_FAMILY=="kintex7l" ? "virtex7" : (C_FAMILY=="qkintex7" ? "virtex7" : (C_FAMILY=="qkintex7l" ? "virtex7" : (C_FAMILY=="artix7" ? "virtex7" : (C_FAMILY=="artix7l" ? "virtex7" : (C_FAMILY=="qartix7" ? "virtex7" : (C_FAMILY=="qartix7l" ? "virtex7" : (C_FAMILY=="aartix7" ? "virtex7" : (C_FAMILY=="zynq" ? "virtex7" : (C_FAMILY=="azynq" ? "virtex7" : (C_FAMILY=="qzynq" ? "virtex7" : C_FAMILY)))))))))))))))))))))));

  // Internal configuration parameters
  //---------------------------------------------
  localparam SINGLE_PORT = (C_MEM_TYPE==0 || C_MEM_TYPE==3);
  localparam IS_ROM      = (C_MEM_TYPE==3 || C_MEM_TYPE==4);
  localparam HAS_A_WRITE = (!IS_ROM);
  localparam HAS_B_WRITE = (C_MEM_TYPE==2);
  localparam HAS_A_READ  = (C_MEM_TYPE!=1);
  localparam HAS_B_READ  = (!SINGLE_PORT);
  localparam HAS_B_PORT  = (HAS_B_READ || HAS_B_WRITE);

  // Calculate the mux pipeline register stages for Port A and Port B
  //------------------------------------------------------------------
  localparam MUX_PIPELINE_STAGES_A = (C_HAS_MUX_OUTPUT_REGS_A) ?
                             C_MUX_PIPELINE_STAGES : 0;
  localparam MUX_PIPELINE_STAGES_B = (C_HAS_MUX_OUTPUT_REGS_B) ?
                             C_MUX_PIPELINE_STAGES : 0;
  
  // Calculate total number of register stages in the core
  // -----------------------------------------------------
  localparam NUM_OUTPUT_STAGES_A = (C_HAS_MEM_OUTPUT_REGS_A+MUX_PIPELINE_STAGES_A+C_HAS_MUX_OUTPUT_REGS_A);

  localparam NUM_OUTPUT_STAGES_B = (C_HAS_MEM_OUTPUT_REGS_B+MUX_PIPELINE_STAGES_B+C_HAS_MUX_OUTPUT_REGS_B);

  wire                   ena_i;
  wire                   enb_i;
  wire                   reseta_i;
  wire                   resetb_i;
  wire [C_WEA_WIDTH-1:0] wea_i;
  wire [C_WEB_WIDTH-1:0] web_i;
  wire                   rea_i;
  wire                   reb_i;
  wire                   rsta_outp_stage;
  wire                   rstb_outp_stage;
  // ECC SBITERR/DBITERR Outputs
  //  The ECC Behavior is modeled by the behavioral models only for Virtex-6.
  //  For Virtex-5, these outputs will be tied to 0.
   assign SBITERR = ((C_MEM_TYPE == 1 && C_USE_ECC == 1) || C_USE_SOFTECC == 1)?sbiterr_sdp:0;
   assign DBITERR = ((C_MEM_TYPE == 1 && C_USE_ECC == 1) || C_USE_SOFTECC == 1)?dbiterr_sdp:0;
   assign RDADDRECC = (((C_FAMILY_LOCALPARAM == "virtex7") && C_MEM_TYPE == 1 && C_USE_ECC == 1) || C_USE_SOFTECC == 1)?rdaddrecc_sdp:0;


  // This effectively wires off optional inputs
  assign ena_i = (C_HAS_ENA==0) || ENA;
  assign enb_i = ((C_HAS_ENB==0) || ENB) && HAS_B_PORT;
  // To match RTL : In RTL, write enable of the primitive is tied to all 1's and
  // the enable of the primitive is ANDing of wea(0) and ena. so eventually, the
  // write operation depends on both enable and write enable. So, the below code
  // which is actually doing the write operation only on enable ignoring the wea
  // is removed to be in consistent with RTL.
  // To Fix CR855535 (The fix to this CR is reverted to match RTL)
  //assign wea_i = (HAS_A_WRITE == 1 && C_MEM_TYPE == 1 &&C_USE_ECC == 1 && C_HAS_ENA == 1 && ENA == 1) ? 'b1 :(HAS_A_WRITE == 1 && C_MEM_TYPE == 1 &&C_USE_ECC == 1 && C_HAS_ENA == 0) ? WEA : (HAS_A_WRITE && ena_i && C_USE_ECC == 0) ? WEA : 'b0;
  assign wea_i = (HAS_A_WRITE && ena_i) ? WEA : 'b0;
  assign web_i = (HAS_B_WRITE && enb_i) ? WEB : 'b0;
  assign rea_i = (HAS_A_READ)  ? ena_i : 'b0;
  assign reb_i = (HAS_B_READ)  ? enb_i : 'b0;

  // These signals reset the memory latches

  assign reseta_i = 
     ((C_HAS_RSTA==1 && RSTA && NUM_OUTPUT_STAGES_A==0) ||
      (C_HAS_RSTA==1 && RSTA && C_RSTRAM_A==1));

  assign resetb_i = 
     ((C_HAS_RSTB==1 && RSTB && NUM_OUTPUT_STAGES_B==0) ||
      (C_HAS_RSTB==1 && RSTB && C_RSTRAM_B==1));

  // Tasks to access the memory
  //---------------------------
  //**************
  // write_a
  //**************
  task write_a
    (input  reg [C_ADDRA_WIDTH-1:0]   addr,
     input  reg [C_WEA_WIDTH-1:0]     byte_en,
     input  reg [C_WRITE_WIDTH_A-1:0] data,
     input  inj_sbiterr,
     input  inj_dbiterr);
    reg [C_WRITE_WIDTH_A-1:0] current_contents;
    reg [C_ADDRA_WIDTH-1:0] address;
    integer i;
    begin
      // Shift the address by the ratio
      address = (addr/WRITE_ADDR_A_DIV);
      if (address >= C_WRITE_DEPTH_A) begin
        if (!C_DISABLE_WARN_BHV_RANGE) begin
          $fdisplay(ADDRFILE,
                    "%0s WARNING: Address %0h is outside range for A Write",
                    C_CORENAME, addr);
        end

      // valid address
      end else begin

        // Combine w/ byte writes
        if (C_USE_BYTE_WEA) begin

          // Get the current memory contents
          if (WRITE_WIDTH_RATIO_A == 1) begin
            // Workaround for IUS 5.5 part-select issue
            current_contents = memory[address];
          end else begin
            for (i = 0; i < WRITE_WIDTH_RATIO_A; i = i + 1) begin
              current_contents[MIN_WIDTH*i+:MIN_WIDTH]
                = memory[address*WRITE_WIDTH_RATIO_A + i];
            end
          end

          // Apply incoming bytes
          if (C_WEA_WIDTH == 1) begin
            // Workaround for IUS 5.5 part-select issue
            if (byte_en[0]) begin
              current_contents = data;
            end
          end else begin
            for (i = 0; i < C_WEA_WIDTH; i = i + 1) begin
              if (byte_en[i]) begin
                current_contents[BYTE_SIZE*i+:BYTE_SIZE]
                  = data[BYTE_SIZE*i+:BYTE_SIZE];
              end
            end
          end

        // No byte-writes, overwrite the whole word
        end else begin
          current_contents = data;
        end

        // Insert double bit errors:
        if (C_USE_ECC == 1) begin
          if ((C_HAS_INJECTERR == 2 || C_HAS_INJECTERR == 3) && inj_dbiterr == 1'b1) begin
// Modified for Implementing CR_859399            
            current_contents[0] = !(current_contents[30]);
            current_contents[1] = !(current_contents[62]);
            
            /*current_contents[0] = !(current_contents[0]);
            current_contents[1] = !(current_contents[1]);*/
          end
        end
    
        // Insert softecc double bit errors:
        if (C_USE_SOFTECC == 1) begin
          if ((C_HAS_INJECTERR == 2 || C_HAS_INJECTERR == 3) && inj_dbiterr == 1'b1) begin
            doublebit_error[C_WRITE_WIDTH_A+CHKBIT_WIDTH-1:2] = doublebit_error[C_WRITE_WIDTH_A+CHKBIT_WIDTH-3:0];
            doublebit_error[0] = doublebit_error[C_WRITE_WIDTH_A+CHKBIT_WIDTH-1];
            doublebit_error[1] = doublebit_error[C_WRITE_WIDTH_A+CHKBIT_WIDTH-2];
            current_contents = current_contents ^ doublebit_error[C_WRITE_WIDTH_A-1:0];
          end
        end
    
        // Write data to memory
        if (WRITE_WIDTH_RATIO_A == 1) begin
          // Workaround for IUS 5.5 part-select issue
          memory[address*WRITE_WIDTH_RATIO_A] = current_contents;
        end else begin
          for (i = 0; i < WRITE_WIDTH_RATIO_A; i = i + 1) begin
            memory[address*WRITE_WIDTH_RATIO_A + i]
              = current_contents[MIN_WIDTH*i+:MIN_WIDTH];
          end
        end

        // Store the address at which error is injected:
        if ((C_FAMILY_LOCALPARAM == "virtex7") && C_USE_ECC == 1) begin
          if ((C_HAS_INJECTERR == 1 && inj_sbiterr == 1'b1) || 
            (C_HAS_INJECTERR == 3 && inj_sbiterr == 1'b1 && inj_dbiterr != 1'b1))
          begin
            sbiterr_arr[addr] = 1;
          end else begin
            sbiterr_arr[addr] = 0;
          end
  
          if ((C_HAS_INJECTERR == 2 || C_HAS_INJECTERR == 3) && inj_dbiterr == 1'b1) begin
            dbiterr_arr[addr] = 1;
          end else begin
            dbiterr_arr[addr] = 0;
          end
        end

        // Store the address at which softecc error is injected:
        if (C_USE_SOFTECC == 1) begin
          if ((C_HAS_INJECTERR == 1 && inj_sbiterr == 1'b1) || 
            (C_HAS_INJECTERR == 3 && inj_sbiterr == 1'b1 && inj_dbiterr != 1'b1))
          begin
            softecc_sbiterr_arr[addr] = 1;
          end else begin
            softecc_sbiterr_arr[addr] = 0;
          end
  
          if ((C_HAS_INJECTERR == 2 || C_HAS_INJECTERR == 3) && inj_dbiterr == 1'b1) begin
            softecc_dbiterr_arr[addr] = 1;
          end else begin
            softecc_dbiterr_arr[addr] = 0;
          end
        end

      end
    end
  endtask

  //**************
  // write_b
  //**************
  task write_b
    (input  reg [C_ADDRB_WIDTH-1:0]   addr,
     input  reg [C_WEB_WIDTH-1:0]     byte_en,
     input  reg [C_WRITE_WIDTH_B-1:0] data);
    reg [C_WRITE_WIDTH_B-1:0] current_contents;
    reg [C_ADDRB_WIDTH-1:0]   address;
    integer i;
    begin
      // Shift the address by the ratio
      address = (addr/WRITE_ADDR_B_DIV);
      if (address >= C_WRITE_DEPTH_B) begin
        if (!C_DISABLE_WARN_BHV_RANGE) begin
          $fdisplay(ADDRFILE,
                    "%0s WARNING: Address %0h is outside range for B Write",
                    C_CORENAME, addr);
        end

      // valid address
      end else begin

        // Combine w/ byte writes
        if (C_USE_BYTE_WEB) begin

          // Get the current memory contents
          if (WRITE_WIDTH_RATIO_B == 1) begin
            // Workaround for IUS 5.5 part-select issue
            current_contents = memory[address];
          end else begin
            for (i = 0; i < WRITE_WIDTH_RATIO_B; i = i + 1) begin
              current_contents[MIN_WIDTH*i+:MIN_WIDTH]
                = memory[address*WRITE_WIDTH_RATIO_B + i];
            end
          end

          // Apply incoming bytes
          if (C_WEB_WIDTH == 1) begin
            // Workaround for IUS 5.5 part-select issue
            if (byte_en[0]) begin
              current_contents = data;
            end
          end else begin
            for (i = 0; i < C_WEB_WIDTH; i = i + 1) begin
              if (byte_en[i]) begin
                current_contents[BYTE_SIZE*i+:BYTE_SIZE]
                  = data[BYTE_SIZE*i+:BYTE_SIZE];
              end
            end
          end

        // No byte-writes, overwrite the whole word
        end else begin
          current_contents = data;
        end

        // Write data to memory
        if (WRITE_WIDTH_RATIO_B == 1) begin
          // Workaround for IUS 5.5 part-select issue
          memory[address*WRITE_WIDTH_RATIO_B] = current_contents;
        end else begin
          for (i = 0; i < WRITE_WIDTH_RATIO_B; i = i + 1) begin
            memory[address*WRITE_WIDTH_RATIO_B + i]
              = current_contents[MIN_WIDTH*i+:MIN_WIDTH];
          end
        end
      end
    end
  endtask

  //**************
  // read_a
  //**************
  task read_a
    (input reg [C_ADDRA_WIDTH-1:0] addr,
     input reg reset);
    reg [C_ADDRA_WIDTH-1:0] address;
    integer i;
  begin

    if (reset) begin
      memory_out_a <= #FLOP_DELAY inita_val;
    end else begin
      // Shift the address by the ratio
      address = (addr/READ_ADDR_A_DIV);
      if (address >= C_READ_DEPTH_A) begin
        if (!C_DISABLE_WARN_BHV_RANGE) begin
          $fdisplay(ADDRFILE,
                    "%0s WARNING: Address %0h is outside range for A Read",
                    C_CORENAME, addr);
        end
        memory_out_a <= #FLOP_DELAY 'bX;
      // valid address
      end else begin
        if (READ_WIDTH_RATIO_A==1) begin
          memory_out_a <= #FLOP_DELAY memory[address*READ_WIDTH_RATIO_A];
        end else begin
          // Increment through the 'partial' words in the memory
          for (i = 0; i < READ_WIDTH_RATIO_A; i = i + 1) begin
            memory_out_a[MIN_WIDTH*i+:MIN_WIDTH]
              <= #FLOP_DELAY memory[address*READ_WIDTH_RATIO_A + i];
          end
        end //end READ_WIDTH_RATIO_A==1 loop

      end //end valid address loop
    end //end reset-data assignment loops
  end
  endtask

  //**************
  // read_b
  //**************
  task read_b
    (input reg [C_ADDRB_WIDTH-1:0] addr,
     input reg reset);
    reg [C_ADDRB_WIDTH-1:0] address;
    integer i;
    begin

    if (reset) begin
      memory_out_b <= #FLOP_DELAY initb_val;
      sbiterr_in   <= #FLOP_DELAY 1'b0;
      dbiterr_in   <= #FLOP_DELAY 1'b0;
      rdaddrecc_in <= #FLOP_DELAY 0;
    end else begin
      // Shift the address
      address = (addr/READ_ADDR_B_DIV);
      if (address >= C_READ_DEPTH_B) begin
        if (!C_DISABLE_WARN_BHV_RANGE) begin
          $fdisplay(ADDRFILE,
                    "%0s WARNING: Address %0h is outside range for B Read",
                    C_CORENAME, addr);
        end
        memory_out_b <= #FLOP_DELAY 'bX;
        sbiterr_in <= #FLOP_DELAY 1'bX;
        dbiterr_in <= #FLOP_DELAY 1'bX;
        rdaddrecc_in <= #FLOP_DELAY 'bX;
        // valid address
      end else begin
        if (READ_WIDTH_RATIO_B==1) begin
          memory_out_b <= #FLOP_DELAY memory[address*READ_WIDTH_RATIO_B];
        end else begin
          // Increment through the 'partial' words in the memory
          for (i = 0; i < READ_WIDTH_RATIO_B; i = i + 1) begin
            memory_out_b[MIN_WIDTH*i+:MIN_WIDTH]
              <= #FLOP_DELAY memory[address*READ_WIDTH_RATIO_B + i];
          end
        end

        if ((C_FAMILY_LOCALPARAM == "virtex7") && C_USE_ECC == 1) begin
          rdaddrecc_in <= #FLOP_DELAY addr;
          if (sbiterr_arr[addr] == 1) begin
            sbiterr_in <= #FLOP_DELAY 1'b1;
          end else begin
            sbiterr_in <= #FLOP_DELAY 1'b0;
          end

          if (dbiterr_arr[addr] == 1) begin
            dbiterr_in <= #FLOP_DELAY 1'b1;
          end else begin
            dbiterr_in <= #FLOP_DELAY 1'b0;
          end

         end else  if (C_USE_SOFTECC == 1) begin
          rdaddrecc_in <= #FLOP_DELAY addr;
          if (softecc_sbiterr_arr[addr] == 1) begin
            sbiterr_in <= #FLOP_DELAY 1'b1;
          end else begin
            sbiterr_in <= #FLOP_DELAY 1'b0;
          end

          if (softecc_dbiterr_arr[addr] == 1) begin
            dbiterr_in <= #FLOP_DELAY 1'b1;
          end else begin
            dbiterr_in <= #FLOP_DELAY 1'b0;
          end
        end else begin
          rdaddrecc_in <= #FLOP_DELAY 0;
          dbiterr_in <= #FLOP_DELAY 1'b0;
          sbiterr_in <= #FLOP_DELAY 1'b0;
        end //end SOFTECC Loop
      end //end Valid address loop
    end //end reset-data assignment loops
  end
  endtask

  //**************
  // reset_a
  //**************
  task reset_a (input reg reset);
  begin
    if (reset) memory_out_a <= #FLOP_DELAY inita_val;
  end
  endtask

  //**************
  // reset_b
  //**************
  task reset_b (input reg reset);
  begin
    if (reset) memory_out_b <= #FLOP_DELAY initb_val;
  end
  endtask

  //**************
  // init_memory
  //**************
  task init_memory;
    integer i, j, addr_step;
    integer status;
    reg [C_WRITE_WIDTH_A-1:0] default_data;
    begin
      default_data = 0;

      //Display output message indicating that the behavioral model is being 
      //initialized
      if (C_USE_DEFAULT_DATA || C_LOAD_INIT_FILE) $display(" Block Memory Generator module loading initial data...");

      // Convert the default to hex
      if (C_USE_DEFAULT_DATA) begin
        if (default_data_str == "") begin
         $fdisplay(ERRFILE, "%0s ERROR: C_DEFAULT_DATA is empty!", C_CORENAME);
          $finish;
        end else begin
          status = $sscanf(default_data_str, "%h", default_data);
          if (status == 0) begin
            $fdisplay(ERRFILE, {"%0s ERROR: Unsuccessful hexadecimal read",
                                "from C_DEFAULT_DATA: %0s"},
                      C_CORENAME, C_DEFAULT_DATA);
            $finish;
          end
        end
      end

      // Step by WRITE_ADDR_A_DIV through the memory via the
      // Port A write interface to hit every location once
      addr_step = WRITE_ADDR_A_DIV;

      // 'write' to every location with default (or 0)
      for (i = 0; i < C_WRITE_DEPTH_A*addr_step; i = i + addr_step) begin
        write_a(i, {C_WEA_WIDTH{1'b1}}, default_data, 1'b0, 1'b0);
      end

      // Get specialized data from the MIF file
      if (C_LOAD_INIT_FILE) begin
        if (init_file_str == "") begin
          $fdisplay(ERRFILE, "%0s ERROR: C_INIT_FILE_NAME is empty!",
                    C_CORENAME);
          $finish;
        end else begin
          initfile = $fopen(init_file_str, "r");
          if (initfile == 0) begin
            $fdisplay(ERRFILE, {"%0s, ERROR: Problem opening",
                                "C_INIT_FILE_NAME: %0s!"},
                      C_CORENAME, init_file_str);
            $finish;
          end else begin
            // loop through the mif file, loading in the data
            for (i = 0; i < C_WRITE_DEPTH_A*addr_step; i = i + addr_step) begin
              status = $fscanf(initfile, "%b", mif_data);
              if (status > 0) begin
                write_a(i, {C_WEA_WIDTH{1'b1}}, mif_data, 1'b0, 1'b0);
              end
            end
            $fclose(initfile);
          end //initfile
        end //init_file_str
      end //C_LOAD_INIT_FILE


      if (C_USE_BRAM_BLOCK) begin
            // Get specialized data from the MIF file
            if (C_INIT_FILE != "NONE") begin
              if (mem_init_file_str == "") begin
                $fdisplay(ERRFILE, "%0s ERROR: C_INIT_FILE is empty!",
                          C_CORENAME);
                $finish;
              end else begin
                meminitfile = $fopen(mem_init_file_str, "r");
                if (meminitfile == 0) begin
                  $fdisplay(ERRFILE, {"%0s, ERROR: Problem opening",
                                      "C_INIT_FILE: %0s!"},
                            C_CORENAME, mem_init_file_str);
                  $finish;
                end else begin
                  // loop through the mif file, loading in the data
                    $readmemh(mem_init_file_str, memory );
                      for (j = 0; j < MAX_DEPTH-1 ; j = j + 1) begin
                      end 
                  $fclose(meminitfile);
                end //meminitfile
              end //mem_init_file_str
            end //C_INIT_FILE
      end //C_USE_BRAM_BLOCK

      //Display output message indicating that the behavioral model is done 
      //initializing
      if (C_USE_DEFAULT_DATA || C_LOAD_INIT_FILE) 
          $display(" Block Memory Generator data initialization complete.");
    end
  endtask

  //**************
  // log2roundup
  //**************
  function integer log2roundup (input integer data_value);
      integer width;
      integer cnt;
      begin
         width = 0;

         if (data_value > 1) begin
            for(cnt=1 ; cnt < data_value ; cnt = cnt * 2) begin
               width = width + 1;
            end //loop
         end //if

         log2roundup = width;

      end //log2roundup
   endfunction


  //*******************
  // collision_check
  //*******************
  function integer collision_check (input reg [C_ADDRA_WIDTH-1:0] addr_a,
                                    input integer iswrite_a,
                                    input reg [C_ADDRB_WIDTH-1:0] addr_b,
                                    input integer iswrite_b);
    reg c_aw_bw, c_aw_br, c_ar_bw;
    integer scaled_addra_to_waddrb_width;
    integer scaled_addrb_to_waddrb_width;
    integer scaled_addra_to_waddra_width;
    integer scaled_addrb_to_waddra_width;
    integer scaled_addra_to_raddrb_width;
    integer scaled_addrb_to_raddrb_width;
    integer scaled_addra_to_raddra_width;
    integer scaled_addrb_to_raddra_width;



    begin

    c_aw_bw = 0;
    c_aw_br = 0;
    c_ar_bw = 0;

    //If write_addr_b_width is smaller, scale both addresses to that width for 
    //comparing write_addr_a and write_addr_b; addr_a starts as C_ADDRA_WIDTH,
    //scale it down to write_addr_b_width. addr_b starts as C_ADDRB_WIDTH,
    //scale it down to write_addr_b_width. Once both are scaled to 
    //write_addr_b_width, compare.
    scaled_addra_to_waddrb_width  = ((addr_a)/
                                        2**(C_ADDRA_WIDTH-write_addr_b_width));
    scaled_addrb_to_waddrb_width  = ((addr_b)/
                                        2**(C_ADDRB_WIDTH-write_addr_b_width));

    //If write_addr_a_width is smaller, scale both addresses to that width for 
    //comparing write_addr_a and write_addr_b; addr_a starts as C_ADDRA_WIDTH,
    //scale it down to write_addr_a_width. addr_b starts as C_ADDRB_WIDTH,
    //scale it down to write_addr_a_width. Once both are scaled to 
    //write_addr_a_width, compare.
    scaled_addra_to_waddra_width  = ((addr_a)/
                                        2**(C_ADDRA_WIDTH-write_addr_a_width));
    scaled_addrb_to_waddra_width  = ((addr_b)/
                                        2**(C_ADDRB_WIDTH-write_addr_a_width));

    //If read_addr_b_width is smaller, scale both addresses to that width for 
    //comparing write_addr_a and read_addr_b; addr_a starts as C_ADDRA_WIDTH,
    //scale it down to read_addr_b_width. addr_b starts as C_ADDRB_WIDTH,
    //scale it down to read_addr_b_width. Once both are scaled to 
    //read_addr_b_width, compare.
    scaled_addra_to_raddrb_width  = ((addr_a)/
                                         2**(C_ADDRA_WIDTH-read_addr_b_width));
    scaled_addrb_to_raddrb_width  = ((addr_b)/
                                         2**(C_ADDRB_WIDTH-read_addr_b_width));

    //If read_addr_a_width is smaller, scale both addresses to that width for 
    //comparing read_addr_a and write_addr_b; addr_a starts as C_ADDRA_WIDTH,
    //scale it down to read_addr_a_width. addr_b starts as C_ADDRB_WIDTH,
    //scale it down to read_addr_a_width. Once both are scaled to 
    //read_addr_a_width, compare.
    scaled_addra_to_raddra_width  = ((addr_a)/
                                         2**(C_ADDRA_WIDTH-read_addr_a_width));
    scaled_addrb_to_raddra_width  = ((addr_b)/
                                         2**(C_ADDRB_WIDTH-read_addr_a_width));

    //Look for a write-write collision. In order for a write-write
    //collision to exist, both ports must have a write transaction.
    if (iswrite_a && iswrite_b) begin
      if (write_addr_a_width > write_addr_b_width) begin
        if (scaled_addra_to_waddrb_width == scaled_addrb_to_waddrb_width) begin
          c_aw_bw = 1;
        end else begin
          c_aw_bw = 0;
        end
      end else begin
        if (scaled_addrb_to_waddra_width == scaled_addra_to_waddra_width) begin
          c_aw_bw = 1;
        end else begin
          c_aw_bw = 0;
        end
      end //width
    end //iswrite_a and iswrite_b

    //If the B port is reading (which means it is enabled - so could be
    //a TX_WRITE or TX_READ), then check for a write-read collision).
    //This could happen whether or not a write-write collision exists due
    //to asymmetric write/read ports.
    if (iswrite_a) begin
      if (write_addr_a_width > read_addr_b_width) begin
        if (scaled_addra_to_raddrb_width == scaled_addrb_to_raddrb_width) begin
          c_aw_br = 1;
        end else begin
          c_aw_br = 0;
        end
    end else begin
        if (scaled_addrb_to_waddra_width == scaled_addra_to_waddra_width) begin
          c_aw_br = 1;
        end else begin
          c_aw_br = 0;
        end
      end //width
    end //iswrite_a

    //If the A port is reading (which means it is enabled - so could be
    //  a TX_WRITE or TX_READ), then check for a write-read collision).
    //This could happen whether or not a write-write collision exists due
    //  to asymmetric write/read ports.
    if (iswrite_b) begin
      if (read_addr_a_width > write_addr_b_width) begin
        if (scaled_addra_to_waddrb_width == scaled_addrb_to_waddrb_width) begin
          c_ar_bw = 1;
        end else begin
          c_ar_bw = 0;
        end
      end else begin
        if (scaled_addrb_to_raddra_width == scaled_addra_to_raddra_width) begin
          c_ar_bw = 1;
        end else begin
          c_ar_bw = 0;
        end
      end //width
    end //iswrite_b



      collision_check = c_aw_bw | c_aw_br | c_ar_bw;

    end
  endfunction

  //*******************************
  // power on values
  //*******************************
  initial begin
    // Load up the memory
    init_memory;
    // Load up the output registers and latches
    if ($sscanf(inita_str, "%h", inita_val)) begin
      memory_out_a = inita_val;
    end else begin
      memory_out_a = 0;
    end
    if ($sscanf(initb_str, "%h", initb_val)) begin
      memory_out_b = initb_val;
    end else begin
      memory_out_b = 0;
    end

    sbiterr_in   = 1'b0;
    dbiterr_in   = 1'b0;
    rdaddrecc_in = 0;

    // Determine the effective address widths for each of the 4 ports
    write_addr_a_width = C_ADDRA_WIDTH - log2roundup(WRITE_ADDR_A_DIV);
    read_addr_a_width  = C_ADDRA_WIDTH - log2roundup(READ_ADDR_A_DIV);
    write_addr_b_width = C_ADDRB_WIDTH - log2roundup(WRITE_ADDR_B_DIV);
    read_addr_b_width  = C_ADDRB_WIDTH - log2roundup(READ_ADDR_B_DIV);

    $display("Block Memory Generator module %m is using a behavioral model for simulation which will not precisely model memory collision behavior.");

  end

  //***************************************************************************
  // These are the main blocks which schedule read and write operations
  // Note that the reset priority feature at the latch stage is only supported
  // for Spartan-6. For other families, the default priority at the latch stage
  // is "CE"
  //***************************************************************************
      // Synchronous clocks: schedule port operations with respect to
      // both write operating modes
  generate
    if(C_COMMON_CLK && (C_WRITE_MODE_A == "WRITE_FIRST") && (C_WRITE_MODE_B ==
                    "WRITE_FIRST")) begin : com_clk_sched_wf_wf
      always @(posedge CLKA) begin
        //Write A
        if (wea_i) write_a(ADDRA, wea_i, DINA, INJECTSBITERR, INJECTDBITERR);
        //Write B
        if (web_i) write_b(ADDRB, web_i, DINB);
        
        if (rea_i) read_a(ADDRA, reseta_i);
 
       //Read B
          if (reb_i) read_b(ADDRB, resetb_i);
      end
    end
    else 
    if(C_COMMON_CLK && (C_WRITE_MODE_A == "READ_FIRST") && (C_WRITE_MODE_B ==
                    "WRITE_FIRST")) begin : com_clk_sched_rf_wf
      always @(posedge CLKA) begin
        //Write B
        if (web_i) write_b(ADDRB, web_i, DINB);
        //Read B
         if (reb_i) read_b(ADDRB, resetb_i);
        //Read A
          if (rea_i) read_a(ADDRA, reseta_i);
        //Write A
        if (wea_i) write_a(ADDRA, wea_i, DINA, INJECTSBITERR, INJECTDBITERR);
      end
    end
    else 
    if(C_COMMON_CLK && (C_WRITE_MODE_A == "WRITE_FIRST") && (C_WRITE_MODE_B ==
                    "READ_FIRST")) begin : com_clk_sched_wf_rf
      always @(posedge CLKA) begin
        //Write A
        if (wea_i) write_a(ADDRA, wea_i, DINA, INJECTSBITERR, INJECTDBITERR);
        //Read A
          if (rea_i) read_a(ADDRA, reseta_i);
        //Read B
          if (reb_i) read_b(ADDRB, resetb_i);
        //Write B
        if (web_i) write_b(ADDRB, web_i, DINB);
      end
    end
    else 
    if(C_COMMON_CLK && (C_WRITE_MODE_A == "READ_FIRST") && (C_WRITE_MODE_B ==
                    "READ_FIRST")) begin : com_clk_sched_rf_rf
      always @(posedge CLKA) begin
        //Read A
          if (rea_i) read_a(ADDRA, reseta_i);
        //Read B
          if (reb_i) read_b(ADDRB, resetb_i);
        //Write A
        if (wea_i) write_a(ADDRA, wea_i, DINA, INJECTSBITERR, INJECTDBITERR);
        //Write B
        if (web_i) write_b(ADDRB, web_i, DINB);
      end
    end
    else if(C_COMMON_CLK && (C_WRITE_MODE_A =="WRITE_FIRST") && (C_WRITE_MODE_B ==
                    "NO_CHANGE")) begin : com_clk_sched_wf_nc
      always @(posedge CLKA) begin
        //Write A
        if (wea_i) write_a(ADDRA, wea_i, DINA, INJECTSBITERR, INJECTDBITERR);
        //Read A
          if (rea_i) read_a(ADDRA, reseta_i);
        //Read B
          if (reb_i && (!web_i || resetb_i)) read_b(ADDRB, resetb_i);
        //Write B
        if (web_i) write_b(ADDRB, web_i, DINB);
      end
    end
    else if(C_COMMON_CLK && (C_WRITE_MODE_A =="READ_FIRST") && (C_WRITE_MODE_B ==
                    "NO_CHANGE")) begin : com_clk_sched_rf_nc
      always @(posedge CLKA) begin
        //Read A
          if (rea_i) read_a(ADDRA, reseta_i);
        //Read B
          if (reb_i && (!web_i || resetb_i)) read_b(ADDRB, resetb_i);
        //Write A
        if (wea_i) write_a(ADDRA, wea_i, DINA, INJECTSBITERR, INJECTDBITERR);
        //Write B
        if (web_i) write_b(ADDRB, web_i, DINB);
      end
    end
    else if(C_COMMON_CLK && (C_WRITE_MODE_A =="NO_CHANGE") && (C_WRITE_MODE_B ==
                    "WRITE_FIRST")) begin : com_clk_sched_nc_wf
      always @(posedge CLKA) begin
        //Write A
        if (wea_i) write_a(ADDRA, wea_i, DINA, INJECTSBITERR, INJECTDBITERR);
        //Write B
        if (web_i) write_b(ADDRB, web_i, DINB);
        //Read A
          if (rea_i && (!wea_i || reseta_i)) read_a(ADDRA, reseta_i);
        //Read B
          if (reb_i) read_b(ADDRB, resetb_i);
      end
    end
    else if(C_COMMON_CLK && (C_WRITE_MODE_A =="NO_CHANGE") && (C_WRITE_MODE_B == 
                    "READ_FIRST")) begin : com_clk_sched_nc_rf
      always @(posedge CLKA) begin
        //Read B
          if (reb_i) read_b(ADDRB, resetb_i);
        //Read A
          if (rea_i && (!wea_i || reseta_i)) read_a(ADDRA, reseta_i);
        //Write A
        if (wea_i) write_a(ADDRA, wea_i, DINA, INJECTSBITERR, INJECTDBITERR);
        //Write B
        if (web_i) write_b(ADDRB, web_i, DINB);
      end
    end
    else if(C_COMMON_CLK && (C_WRITE_MODE_A =="NO_CHANGE") && (C_WRITE_MODE_B ==
                    "NO_CHANGE")) begin : com_clk_sched_nc_nc
      always @(posedge CLKA) begin
        //Write A
        if (wea_i) write_a(ADDRA, wea_i, DINA, INJECTSBITERR, INJECTDBITERR);
        //Write B
        if (web_i) write_b(ADDRB, web_i, DINB);
        //Read A
          if (rea_i && (!wea_i || reseta_i)) read_a(ADDRA, reseta_i);
        //Read B
          if (reb_i && (!web_i || resetb_i)) read_b(ADDRB, resetb_i);
      end
    end
    else if(C_COMMON_CLK) begin: com_clk_sched_default
      always @(posedge CLKA) begin
        //Write A
        if (wea_i) write_a(ADDRA, wea_i, DINA, INJECTSBITERR, INJECTDBITERR);
        //Write B
        if (web_i) write_b(ADDRB, web_i, DINB);
        //Read A
          if (rea_i) read_a(ADDRA, reseta_i);
        //Read B
          if (reb_i) read_b(ADDRB, resetb_i);
      end
    end
  endgenerate

      // Asynchronous clocks: port operation is independent
  generate
    if((!C_COMMON_CLK) && (C_WRITE_MODE_A == "WRITE_FIRST")) begin : async_clk_sched_clka_wf
      always @(posedge CLKA) begin
        //Write A
        if (wea_i) write_a(ADDRA, wea_i, DINA, INJECTSBITERR, INJECTDBITERR);
        //Read A
          if (rea_i) read_a(ADDRA, reseta_i);
      end
    end
    else if((!C_COMMON_CLK) && (C_WRITE_MODE_A == "READ_FIRST")) begin : async_clk_sched_clka_rf
      always @(posedge CLKA) begin
        //Read A
        if (rea_i) read_a(ADDRA, reseta_i);
        //Write A
        if (wea_i) write_a(ADDRA, wea_i, DINA, INJECTSBITERR, INJECTDBITERR);
      end
    end
    else if((!C_COMMON_CLK) && (C_WRITE_MODE_A == "NO_CHANGE")) begin : async_clk_sched_clka_nc
      always @(posedge CLKA) begin
        //Write A
        if (wea_i) write_a(ADDRA, wea_i, DINA, INJECTSBITERR, INJECTDBITERR);
        //Read A
         if (rea_i && (!wea_i || reseta_i)) read_a(ADDRA, reseta_i);
      end
    end
  endgenerate

  generate 
    if ((!C_COMMON_CLK) && (C_WRITE_MODE_B == "WRITE_FIRST")) begin: async_clk_sched_clkb_wf
      always @(posedge CLKB) begin
        //Write B
        if (web_i) write_b(ADDRB, web_i, DINB);
        //Read B
          if (reb_i) read_b(ADDRB, resetb_i);
      end
    end
    else if ((!C_COMMON_CLK) && (C_WRITE_MODE_B == "READ_FIRST")) begin: async_clk_sched_clkb_rf
      always @(posedge CLKB) begin
        //Read B
          if (reb_i) read_b(ADDRB, resetb_i);
        //Write B
        if (web_i) write_b(ADDRB, web_i, DINB);
      end
    end
    else if ((!C_COMMON_CLK) && (C_WRITE_MODE_B == "NO_CHANGE")) begin: async_clk_sched_clkb_nc
      always @(posedge CLKB) begin
        //Write B
        if (web_i) write_b(ADDRB, web_i, DINB);
        //Read B
          if (reb_i && (!web_i || resetb_i)) read_b(ADDRB, resetb_i);
      end
    end
  endgenerate

  
  //***************************************************************
  //  Instantiate the variable depth output register stage module
  //***************************************************************
  // Port A
  
  assign rsta_outp_stage = RSTA & (~SLEEP);

  blk_mem_gen_v8_4_4_output_stage
    #(.C_FAMILY                 (C_FAMILY),
      .C_XDEVICEFAMILY          (C_XDEVICEFAMILY),
      .C_RST_TYPE               ("SYNC"),
      .C_HAS_RST                (C_HAS_RSTA),
      .C_RSTRAM                 (C_RSTRAM_A),
      .C_RST_PRIORITY           (C_RST_PRIORITY_A),
      .C_INIT_VAL               (C_INITA_VAL),
      .C_HAS_EN                 (C_HAS_ENA),
      .C_HAS_REGCE              (C_HAS_REGCEA),
      .C_DATA_WIDTH             (C_READ_WIDTH_A),
      .C_ADDRB_WIDTH            (C_ADDRB_WIDTH),
      .C_HAS_MEM_OUTPUT_REGS    (C_HAS_MEM_OUTPUT_REGS_A),
      .C_USE_SOFTECC            (C_USE_SOFTECC),
      .C_USE_ECC                (C_USE_ECC),
      .NUM_STAGES               (NUM_OUTPUT_STAGES_A),
	  .C_EN_ECC_PIPE            (0),
      .FLOP_DELAY               (FLOP_DELAY))
      reg_a
        (.CLK         (CLKA),
         .RST         (rsta_outp_stage),//(RSTA),
         .EN          (ENA),
         .REGCE       (REGCEA),
         .DIN_I       (memory_out_a),
         .DOUT        (DOUTA),
         .SBITERR_IN_I  (1'b0),
         .DBITERR_IN_I  (1'b0),
         .SBITERR     (),
         .DBITERR     (),
         .RDADDRECC_IN_I ({C_ADDRB_WIDTH{1'b0}}),
		 .ECCPIPECE (1'b0),
         .RDADDRECC   ()
        );

  assign rstb_outp_stage = RSTB & (~SLEEP);

  // Port B 
  blk_mem_gen_v8_4_4_output_stage
    #(.C_FAMILY                 (C_FAMILY),
      .C_XDEVICEFAMILY          (C_XDEVICEFAMILY),
      .C_RST_TYPE               ("SYNC"),
      .C_HAS_RST                (C_HAS_RSTB),
      .C_RSTRAM                 (C_RSTRAM_B),
      .C_RST_PRIORITY           (C_RST_PRIORITY_B),
      .C_INIT_VAL               (C_INITB_VAL),
      .C_HAS_EN                 (C_HAS_ENB),
      .C_HAS_REGCE              (C_HAS_REGCEB),
      .C_DATA_WIDTH             (C_READ_WIDTH_B),
      .C_ADDRB_WIDTH            (C_ADDRB_WIDTH),
      .C_HAS_MEM_OUTPUT_REGS    (C_HAS_MEM_OUTPUT_REGS_B),
      .C_USE_SOFTECC            (C_USE_SOFTECC),
      .C_USE_ECC                (C_USE_ECC),
      .NUM_STAGES               (NUM_OUTPUT_STAGES_B),
      .C_EN_ECC_PIPE            (C_EN_ECC_PIPE),
      .FLOP_DELAY               (FLOP_DELAY))
      reg_b
        (.CLK         (CLKB),
         .RST         (rstb_outp_stage),//(RSTB),
         .EN          (ENB),
         .REGCE       (REGCEB),
         .DIN_I       (memory_out_b),
         .DOUT        (dout_i),
         .SBITERR_IN_I  (sbiterr_in),
         .DBITERR_IN_I  (dbiterr_in),
         .SBITERR     (sbiterr_i),
         .DBITERR     (dbiterr_i),
         .RDADDRECC_IN_I (rdaddrecc_in),
         .ECCPIPECE   (ECCPIPECE),
         .RDADDRECC   (rdaddrecc_i)
        );

  //***************************************************************
  //  Instantiate the Input and Output register stages
  //***************************************************************
blk_mem_gen_v8_4_4_softecc_output_reg_stage
    #(.C_DATA_WIDTH                 (C_READ_WIDTH_B),
      .C_ADDRB_WIDTH                (C_ADDRB_WIDTH),
      .C_HAS_SOFTECC_OUTPUT_REGS_B  (C_HAS_SOFTECC_OUTPUT_REGS_B),
      .C_USE_SOFTECC                (C_USE_SOFTECC),
      .FLOP_DELAY                   (FLOP_DELAY))
  has_softecc_output_reg_stage
      (.CLK       (CLKB),
      .DIN        (dout_i),
      .DOUT        (DOUTB),
      .SBITERR_IN        (sbiterr_i),
      .DBITERR_IN        (dbiterr_i),
      .SBITERR        (sbiterr_sdp),
      .DBITERR        (dbiterr_sdp),
      .RDADDRECC_IN        (rdaddrecc_i),
      .RDADDRECC        (rdaddrecc_sdp)
);

  //****************************************************
  // Synchronous collision checks
  //****************************************************
// CR 780544 : To make verilog model's collison warnings in consistant with
// vhdl model, the non-blocking assignments are replaced with blocking 
// assignments.
  generate if (!C_DISABLE_WARN_BHV_COLL && C_COMMON_CLK) begin : sync_coll
    always @(posedge CLKA) begin
      // Possible collision if both are enabled and the addresses match
      if (ena_i && enb_i) begin
        if (wea_i || web_i) begin
          is_collision = collision_check(ADDRA, wea_i, ADDRB, web_i);
        end else begin
          is_collision = 0;
        end
      end else begin
          is_collision = 0;
      end

      // If the write port is in READ_FIRST mode, there is no collision
      if (C_WRITE_MODE_A=="READ_FIRST" && wea_i && !web_i) begin
        is_collision = 0;
      end
      if (C_WRITE_MODE_B=="READ_FIRST" && web_i && !wea_i) begin
        is_collision = 0;
      end

      // Only flag if one of the accesses is a write
      if (is_collision && (wea_i || web_i)) begin
        $fwrite(COLLFILE, "%0s collision detected at time: %0d, ",
                C_CORENAME, $time);
        $fwrite(COLLFILE, "Instance: %m, A %0s address: %0h, B %0s address: %0h\n",
                wea_i ? "write" : "read", ADDRA,
                web_i ? "write" : "read", ADDRB);
      end
    end

  //****************************************************
  // Asynchronous collision checks
  //****************************************************
  end else if (!C_DISABLE_WARN_BHV_COLL && !C_COMMON_CLK) begin : async_coll

    // Delay A and B addresses in order to mimic setup/hold times
    wire [C_ADDRA_WIDTH-1:0]  #COLL_DELAY addra_delay = ADDRA;
    wire [0:0]                #COLL_DELAY wea_delay   = wea_i;
    wire                      #COLL_DELAY ena_delay   = ena_i;
    wire [C_ADDRB_WIDTH-1:0]  #COLL_DELAY addrb_delay = ADDRB;
    wire [0:0]                #COLL_DELAY web_delay   = web_i;
    wire                      #COLL_DELAY enb_delay   = enb_i;

    // Do the checks w/rt A
    always @(posedge CLKA) begin
      // Possible collision if both are enabled and the addresses match
      if (ena_i && enb_i) begin
        if (wea_i || web_i) begin
          is_collision_a = collision_check(ADDRA, wea_i, ADDRB, web_i);
        end else begin
          is_collision_a = 0;
        end
      end else begin
        is_collision_a = 0;
      end

      if (ena_i && enb_delay) begin
        if(wea_i || web_delay) begin
          is_collision_delay_a = collision_check(ADDRA, wea_i, addrb_delay,
                                                                    web_delay);
        end else begin
          is_collision_delay_a = 0;
        end
      end else begin
        is_collision_delay_a = 0;
      end

      // Only flag if B access is a write
      if (is_collision_a && web_i) begin
        $fwrite(COLLFILE, "%0s collision detected at time: %0d, ",
                C_CORENAME, $time);
        $fwrite(COLLFILE, "Instance: %m, A %0s address: %0h, B write address: %0h\n",
                wea_i ? "write" : "read", ADDRA, ADDRB);

      end else if (is_collision_delay_a && web_delay) begin
        $fwrite(COLLFILE, "%0s collision detected at time: %0d, ",
                C_CORENAME, $time);
        $fwrite(COLLFILE, "Instance: %m, A %0s address: %0h, B write address: %0h\n",
                wea_i ? "write" : "read", ADDRA, addrb_delay);
      end

    end

    // Do the checks w/rt B
    always @(posedge CLKB) begin

      // Possible collision if both are enabled and the addresses match
      if (ena_i && enb_i) begin
        if (wea_i || web_i) begin
          is_collision_b = collision_check(ADDRA, wea_i, ADDRB, web_i);
        end else begin
          is_collision_b = 0;
        end
      end else begin
        is_collision_b = 0;
      end

      if (ena_delay && enb_i) begin
        if (wea_delay || web_i) begin
          is_collision_delay_b = collision_check(addra_delay, wea_delay, ADDRB,
                                                                        web_i);
        end else begin
          is_collision_delay_b = 0;
        end
      end else begin
        is_collision_delay_b = 0;
      end


      // Only flag if A access is a write
      if (is_collision_b && wea_i) begin
        $fwrite(COLLFILE, "%0s collision detected at time: %0d, ",
                C_CORENAME, $time);
        $fwrite(COLLFILE, "Instance: %m, A write address: %0h, B %s address: %0h\n",
                ADDRA, web_i ? "write" : "read", ADDRB);

      end else if (is_collision_delay_b && wea_delay) begin
        $fwrite(COLLFILE, "%0s collision detected at time: %0d, ",
                C_CORENAME, $time);
        $fwrite(COLLFILE, "Instance: %m, A write address: %0h, B %s address: %0h\n",
                addra_delay, web_i ? "write" : "read", ADDRB);
      end

    end
  end
  endgenerate

endmodule
//*****************************************************************************
// Top module wraps Input register and Memory module
//
// This module is the top-level behavioral model and this implements the memory 
// module and the input registers
//*****************************************************************************
module blk_mem_gen_v8_4_4
  #(parameter C_CORENAME                = "blk_mem_gen_v8_4_4",
    parameter C_FAMILY                  = "virtex7",
    parameter C_XDEVICEFAMILY           = "virtex7",
    parameter C_ELABORATION_DIR         = "",
    parameter C_INTERFACE_TYPE          = 0,
    parameter C_USE_BRAM_BLOCK          = 0,
    parameter C_CTRL_ECC_ALGO           = "NONE",
    parameter C_ENABLE_32BIT_ADDRESS    = 0,
    parameter C_AXI_TYPE                = 0,
    parameter C_AXI_SLAVE_TYPE          = 0,
    parameter C_HAS_AXI_ID              = 0,
    parameter C_AXI_ID_WIDTH            = 4,
    parameter C_MEM_TYPE                = 2,
    parameter C_BYTE_SIZE               = 9,
    parameter C_ALGORITHM               = 1,
    parameter C_PRIM_TYPE               = 3,
    parameter C_LOAD_INIT_FILE          = 0,
    parameter C_INIT_FILE_NAME          = "",
    parameter C_INIT_FILE               = "",
    parameter C_USE_DEFAULT_DATA        = 0,
    parameter C_DEFAULT_DATA            = "0",
    //parameter C_RST_TYPE                = "SYNC",
    parameter C_HAS_RSTA                = 0,
    parameter C_RST_PRIORITY_A          = "CE",
    parameter C_RSTRAM_A                = 0,
    parameter C_INITA_VAL               = "0",
    parameter C_HAS_ENA                 = 1,
    parameter C_HAS_REGCEA              = 0,
    parameter C_USE_BYTE_WEA            = 0,
    parameter C_WEA_WIDTH               = 1,
    parameter C_WRITE_MODE_A            = "WRITE_FIRST",
    parameter C_WRITE_WIDTH_A           = 32,
    parameter C_READ_WIDTH_A            = 32,
    parameter C_WRITE_DEPTH_A           = 64,
    parameter C_READ_DEPTH_A            = 64,
    parameter C_ADDRA_WIDTH             = 5,
    parameter C_HAS_RSTB                = 0,
    parameter C_RST_PRIORITY_B          = "CE",
    parameter C_RSTRAM_B                = 0,
    parameter C_INITB_VAL               = "",
    parameter C_HAS_ENB                 = 1,
    parameter C_HAS_REGCEB              = 0,
    parameter C_USE_BYTE_WEB            = 0,
    parameter C_WEB_WIDTH               = 1,
    parameter C_WRITE_MODE_B            = "WRITE_FIRST",
    parameter C_WRITE_WIDTH_B           = 32,
    parameter C_READ_WIDTH_B            = 32,
    parameter C_WRITE_DEPTH_B           = 64,
    parameter C_READ_DEPTH_B            = 64,
    parameter C_ADDRB_WIDTH             = 5,
    parameter C_HAS_MEM_OUTPUT_REGS_A   = 0,
    parameter C_HAS_MEM_OUTPUT_REGS_B   = 0,
    parameter C_HAS_MUX_OUTPUT_REGS_A   = 0,
    parameter C_HAS_MUX_OUTPUT_REGS_B   = 0,
    parameter C_HAS_SOFTECC_INPUT_REGS_A = 0,
    parameter C_HAS_SOFTECC_OUTPUT_REGS_B= 0,
    parameter C_MUX_PIPELINE_STAGES     = 0,
    parameter C_USE_SOFTECC             = 0,
    parameter C_READ_LATENCY_A          = 1,
    parameter C_READ_LATENCY_B          = 1,
    parameter C_USE_ECC                 = 0,
	parameter C_EN_ECC_PIPE             = 0,
    parameter C_HAS_INJECTERR           = 0,
    parameter C_SIM_COLLISION_CHECK     = "NONE",
    parameter C_COMMON_CLK              = 1,
    parameter C_DISABLE_WARN_BHV_COLL   = 0,
	parameter C_EN_SLEEP_PIN            = 0,
    parameter C_USE_URAM                = 0,
    parameter C_EN_RDADDRA_CHG          = 0,
    parameter C_EN_RDADDRB_CHG          = 0,
    parameter C_EN_DEEPSLEEP_PIN        = 0,
    parameter C_EN_SHUTDOWN_PIN         = 0,
	parameter C_EN_SAFETY_CKT           = 0,
	parameter C_COUNT_36K_BRAM          = "",
	parameter C_COUNT_18K_BRAM          = "",
	parameter C_EST_POWER_SUMMARY       = "",
	parameter C_DISABLE_WARN_BHV_RANGE  = 0
	
  )
  (input                       clka,
   input                       rsta,
   input                       ena,
   input                       regcea,
   input [C_WEA_WIDTH-1:0]     wea,
   input [C_ADDRA_WIDTH-1:0]   addra,
   input [C_WRITE_WIDTH_A-1:0] dina,
   output [C_READ_WIDTH_A-1:0] douta,
   input                       clkb,
   input                       rstb,
   input                       enb,
   input                       regceb,
   input [C_WEB_WIDTH-1:0]     web,
   input [C_ADDRB_WIDTH-1:0]   addrb,
   input [C_WRITE_WIDTH_B-1:0] dinb,
   output [C_READ_WIDTH_B-1:0] doutb,
   input                       injectsbiterr,
   input                       injectdbiterr,
   output                      sbiterr,
   output                      dbiterr,
   output [C_ADDRB_WIDTH-1:0]  rdaddrecc,
   input                       eccpipece,
   input                       sleep,
   input                       deepsleep,
   input                       shutdown,
   output                      rsta_busy, 
   output                      rstb_busy, 
   //AXI BMG Input and Output Port Declarations
 
   //AXI Global Signals
   input                         s_aclk,
   input                         s_aresetn,
 
   //AXI                        Full/lite slave write (write side)
   input  [C_AXI_ID_WIDTH-1:0]   s_axi_awid,
   input  [31:0]                 s_axi_awaddr,
   input  [7:0]                  s_axi_awlen,
   input  [2:0]                  s_axi_awsize,
   input  [1:0]                  s_axi_awburst,
   input                         s_axi_awvalid,
   output                        s_axi_awready,
   input  [C_WRITE_WIDTH_A-1:0]  s_axi_wdata,
   input  [C_WEA_WIDTH-1:0]      s_axi_wstrb,
   input                         s_axi_wlast,
   input                         s_axi_wvalid,
   output                        s_axi_wready,
   output [C_AXI_ID_WIDTH-1:0]   s_axi_bid,
   output [1:0]                  s_axi_bresp,
   output                        s_axi_bvalid,
   input                         s_axi_bready,
 
   //AXI                        Full/lite slave read (write side)
   input  [C_AXI_ID_WIDTH-1:0]   s_axi_arid,
   input  [31:0]                 s_axi_araddr,
   input  [7:0]                  s_axi_arlen,
   input  [2:0]                  s_axi_arsize,
   input  [1:0]                  s_axi_arburst,
   input                         s_axi_arvalid,
   output                        s_axi_arready,
   output [C_AXI_ID_WIDTH-1:0]   s_axi_rid,
   output [C_WRITE_WIDTH_B-1:0]  s_axi_rdata,
   output [1:0]                  s_axi_rresp,
   output                        s_axi_rlast,
   output                        s_axi_rvalid,
   input                         s_axi_rready,
 
   //AXI                        Full/lite sideband signals
   input                         s_axi_injectsbiterr,
   input                         s_axi_injectdbiterr,
   output                        s_axi_sbiterr,
   output                        s_axi_dbiterr,
   output [C_ADDRB_WIDTH-1:0]    s_axi_rdaddrecc 
 
  );
//******************************
// Port and Generic Definitions
//******************************
  //////////////////////////////////////////////////////////////////////////
  // Generic Definitions
  //////////////////////////////////////////////////////////////////////////
  // C_CORENAME              : Instance name of the Block Memory Generator core
  // C_FAMILY,C_XDEVICEFAMILY: Designates architecture targeted. The following
  //                           options are available - "spartan3", "spartan6", 
  //                           "virtex4", "virtex5", "virtex6" and "virtex6l".
  // C_MEM_TYPE              : Designates memory type.
  //                           It can be
  //                           0 - Single Port Memory
  //                           1 - Simple Dual Port Memory
  //                           2 - True Dual Port Memory
  //                           3 - Single Port Read Only Memory
  //                           4 - Dual Port Read Only Memory
  // C_BYTE_SIZE             : Size of a byte (8 or 9 bits)
  // C_ALGORITHM             : Designates the algorithm method used
  //                           for constructing the memory.
  //                           It can be Fixed_Primitives, Minimum_Area or 
  //                           Low_Power
  // C_PRIM_TYPE             : Designates the user selected primitive used to 
  //                           construct the memory.
  //
  // C_LOAD_INIT_FILE        : Designates the use of an initialization file to
  //                           initialize memory contents.
  // C_INIT_FILE_NAME        : Memory initialization file name.
  // C_USE_DEFAULT_DATA      : Designates whether to fill remaining
  //                           initialization space with default data
  // C_DEFAULT_DATA          : Default value of all memory locations
  //                           not initialized by the memory
  //                           initialization file.
  // C_RST_TYPE              : Type of reset - Synchronous or Asynchronous
  // C_HAS_RSTA              : Determines the presence of the RSTA port
  // C_RST_PRIORITY_A        : Determines the priority between CE and SR for 
  //                           Port A.
  // C_RSTRAM_A              : Determines if special reset behavior is used for
  //                           Port A
  // C_INITA_VAL             : The initialization value for Port A
  // C_HAS_ENA               : Determines the presence of the ENA port
  // C_HAS_REGCEA            : Determines the presence of the REGCEA port
  // C_USE_BYTE_WEA          : Determines if the Byte Write is used or not.
  // C_WEA_WIDTH             : The width of the WEA port
  // C_WRITE_MODE_A          : Configurable write mode for Port A. It can be
  //                           WRITE_FIRST, READ_FIRST or NO_CHANGE.
  // C_WRITE_WIDTH_A         : Memory write width for Port A.
  // C_READ_WIDTH_A          : Memory read width for Port A.
  // C_WRITE_DEPTH_A         : Memory write depth for Port A.
  // C_READ_DEPTH_A          : Memory read depth for Port A.
  // C_ADDRA_WIDTH           : Width of the ADDRA input port
  // C_HAS_RSTB              : Determines the presence of the RSTB port
  // C_RST_PRIORITY_B        : Determines the priority between CE and SR for 
  //                           Port B.
  // C_RSTRAM_B              : Determines if special reset behavior is used for
  //                           Port B
  // C_INITB_VAL             : The initialization value for Port B
  // C_HAS_ENB               : Determines the presence of the ENB port
  // C_HAS_REGCEB            : Determines the presence of the REGCEB port
  // C_USE_BYTE_WEB          : Determines if the Byte Write is used or not.
  // C_WEB_WIDTH             : The width of the WEB port
  // C_WRITE_MODE_B          : Configurable write mode for Port B. It can be
  //                           WRITE_FIRST, READ_FIRST or NO_CHANGE.
  // C_WRITE_WIDTH_B         : Memory write width for Port B.
  // C_READ_WIDTH_B          : Memory read width for Port B.
  // C_WRITE_DEPTH_B         : Memory write depth for Port B.
  // C_READ_DEPTH_B          : Memory read depth for Port B.
  // C_ADDRB_WIDTH           : Width of the ADDRB input port
  // C_HAS_MEM_OUTPUT_REGS_A : Designates the use of a register at the output 
  //                           of the RAM primitive for Port A.
  // C_HAS_MEM_OUTPUT_REGS_B : Designates the use of a register at the output 
  //                           of the RAM primitive for Port B.
  // C_HAS_MUX_OUTPUT_REGS_A : Designates the use of a register at the output
  //                           of the MUX for Port A.
  // C_HAS_MUX_OUTPUT_REGS_B : Designates the use of a register at the output
  //                           of the MUX for Port B.
  // C_HAS_SOFTECC_INPUT_REGS_A  : 
  // C_HAS_SOFTECC_OUTPUT_REGS_B : 
  // C_MUX_PIPELINE_STAGES   : Designates the number of pipeline stages in 
  //                           between the muxes.
  // C_USE_SOFTECC           : Determines if the Soft ECC feature is used or
  //                           not. Only applicable Spartan-6
  // C_USE_ECC               : Determines if the ECC feature is used or
  //                           not. Only applicable for V5 and V6
  // C_HAS_INJECTERR         : Determines if the error injection pins
  //                           are present or not. If the ECC feature
  //                           is not used, this value is defaulted to
  //                           0, else the following are the allowed 
  //                           values:
  //                         0 : No INJECTSBITERR or INJECTDBITERR pins
  //                         1 : Only INJECTSBITERR pin exists
  //                         2 : Only INJECTDBITERR pin exists
  //                         3 : Both INJECTSBITERR and INJECTDBITERR pins exist
  // C_SIM_COLLISION_CHECK   : Controls the disabling of Unisim model collision
  //                           warnings. It can be "ALL", "NONE", 
  //                           "Warnings_Only" or "Generate_X_Only".
  // C_COMMON_CLK            : Determins if the core has a single CLK input.
  // C_DISABLE_WARN_BHV_COLL : Controls the Behavioral Model Collision warnings
  // C_DISABLE_WARN_BHV_RANGE: Controls the Behavioral Model Out of Range 
  //                           warnings
  //////////////////////////////////////////////////////////////////////////
  // Port Definitions
  //////////////////////////////////////////////////////////////////////////
  // CLKA    : Clock to synchronize all read and write operations of Port A.
  // RSTA    : Reset input to reset memory outputs to a user-defined 
  //           reset state for Port A.
  // ENA     : Enable all read and write operations of Port A.
  // REGCEA  : Register Clock Enable to control each pipeline output
  //           register stages for Port A.
  // WEA     : Write Enable to enable all write operations of Port A.
  // ADDRA   : Address of Port A.
  // DINA    : Data input of Port A.
  // DOUTA   : Data output of Port A.
  // CLKB    : Clock to synchronize all read and write operations of Port B.
  // RSTB    : Reset input to reset memory outputs to a user-defined 
  //           reset state for Port B.
  // ENB     : Enable all read and write operations of Port B.
  // REGCEB  : Register Clock Enable to control each pipeline output
  //           register stages for Port B.
  // WEB     : Write Enable to enable all write operations of Port B.
  // ADDRB   : Address of Port B.
  // DINB    : Data input of Port B.
  // DOUTB   : Data output of Port B.
  // INJECTSBITERR : Single Bit ECC Error Injection Pin.
  // INJECTDBITERR : Double Bit ECC Error Injection Pin.
  // SBITERR       : Output signal indicating that a Single Bit ECC Error has been
  //                 detected and corrected.
  // DBITERR       : Output signal indicating that a Double Bit ECC Error has been
  //                 detected.
  // RDADDRECC     : Read Address Output signal indicating address at which an
  //                 ECC error has occurred.
  //////////////////////////////////////////////////////////////////////////

  wire SBITERR;
  wire DBITERR;
  wire S_AXI_AWREADY;
  wire S_AXI_WREADY;
  wire S_AXI_BVALID;
  wire S_AXI_ARREADY;
  wire S_AXI_RLAST;
  wire S_AXI_RVALID;
  wire S_AXI_SBITERR;
  wire S_AXI_DBITERR;

  wire [C_WEA_WIDTH-1:0]       WEA              = wea;
  wire [C_ADDRA_WIDTH-1:0]     ADDRA            = addra;
  wire [C_WRITE_WIDTH_A-1:0]   DINA             = dina;
  wire [C_READ_WIDTH_A-1:0]    DOUTA;
  wire [C_WEB_WIDTH-1:0]       WEB              = web;
  wire [C_ADDRB_WIDTH-1:0]     ADDRB            = addrb;
  wire [C_WRITE_WIDTH_B-1:0]   DINB             = dinb;
  wire [C_READ_WIDTH_B-1:0]    DOUTB;
  wire [C_ADDRB_WIDTH-1:0]     RDADDRECC;
  wire [C_AXI_ID_WIDTH-1:0]    S_AXI_AWID       = s_axi_awid;
  wire [31:0]                  S_AXI_AWADDR     = s_axi_awaddr;
  wire [7:0]                   S_AXI_AWLEN      = s_axi_awlen;
  wire [2:0]                   S_AXI_AWSIZE     = s_axi_awsize;
  wire [1:0]                   S_AXI_AWBURST    = s_axi_awburst;
  wire [C_WRITE_WIDTH_A-1:0]   S_AXI_WDATA      = s_axi_wdata;
  wire [C_WEA_WIDTH-1:0]       S_AXI_WSTRB      = s_axi_wstrb;
  wire [C_AXI_ID_WIDTH-1:0]    S_AXI_BID;
  wire [1:0]                   S_AXI_BRESP;
  wire [C_AXI_ID_WIDTH-1:0]    S_AXI_ARID       = s_axi_arid;
  wire [31:0]                  S_AXI_ARADDR     = s_axi_araddr;
  wire [7:0]                   S_AXI_ARLEN      = s_axi_arlen;
  wire [2:0]                   S_AXI_ARSIZE     = s_axi_arsize;
  wire [1:0]                   S_AXI_ARBURST    = s_axi_arburst;
  wire [C_AXI_ID_WIDTH-1:0]    S_AXI_RID;
  wire [C_WRITE_WIDTH_B-1:0]   S_AXI_RDATA;
  wire [1:0]                   S_AXI_RRESP;
  wire [C_ADDRB_WIDTH-1:0]     S_AXI_RDADDRECC;
  // Added to fix the simulation warning #CR731605
  wire [C_WEB_WIDTH-1:0]       WEB_parameterized = 0;
  wire                         ECCPIPECE;
  wire                         SLEEP;
  reg                          RSTA_BUSY = 0;
  reg                          RSTB_BUSY = 0;
  // Declaration of internal signals to avoid warnings #927399
  wire                         CLKA;
  wire                         RSTA;
  wire                         ENA;
  wire                         REGCEA;
  wire                         CLKB;
  wire                         RSTB;
  wire                         ENB;
  wire                         REGCEB;
  wire                         INJECTSBITERR;
  wire                         INJECTDBITERR;
  wire                         S_ACLK;
  wire                         S_ARESETN;
  wire                         S_AXI_AWVALID;
  wire                         S_AXI_WLAST;
  wire                         S_AXI_WVALID;
  wire                         S_AXI_BREADY;
  wire                         S_AXI_ARVALID;
  wire                         S_AXI_RREADY;
  wire                         S_AXI_INJECTSBITERR;
  wire                         S_AXI_INJECTDBITERR;

  assign CLKA                 = clka;
  assign RSTA                 = rsta;
  assign ENA                  = ena;
  assign REGCEA               = regcea;
  assign CLKB                 = clkb;
  assign RSTB                 = rstb;
  assign ENB                  = enb;
  assign REGCEB               = regceb;
  assign INJECTSBITERR        = injectsbiterr;
  assign INJECTDBITERR        = injectdbiterr;
  assign ECCPIPECE            = eccpipece;
  assign SLEEP                = sleep;
  assign sbiterr              = SBITERR;
  assign dbiterr              = DBITERR;
  assign S_ACLK               = s_aclk;
  assign S_ARESETN            = s_aresetn;
  assign S_AXI_AWVALID        = s_axi_awvalid;
  assign s_axi_awready        = S_AXI_AWREADY;
  assign S_AXI_WLAST          = s_axi_wlast;
  assign S_AXI_WVALID         = s_axi_wvalid;
  assign s_axi_wready         = S_AXI_WREADY;
  assign s_axi_bvalid         = S_AXI_BVALID;
  assign S_AXI_BREADY         = s_axi_bready;
  assign S_AXI_ARVALID        = s_axi_arvalid;
  assign s_axi_arready        = S_AXI_ARREADY;
  assign s_axi_rlast          = S_AXI_RLAST;
  assign s_axi_rvalid         = S_AXI_RVALID;
  assign S_AXI_RREADY         = s_axi_rready;
  assign S_AXI_INJECTSBITERR  = s_axi_injectsbiterr;
  assign S_AXI_INJECTDBITERR  = s_axi_injectdbiterr;
  assign s_axi_sbiterr        = S_AXI_SBITERR;
  assign s_axi_dbiterr        = S_AXI_DBITERR;

  assign rsta_busy            = RSTA_BUSY;
  assign rstb_busy            = RSTB_BUSY;

  assign doutb            = DOUTB;
  assign douta            = DOUTA;
  assign rdaddrecc        = RDADDRECC;
  assign s_axi_bid        = S_AXI_BID;
  assign s_axi_bresp      = S_AXI_BRESP;
  assign s_axi_rid        = S_AXI_RID;
  assign s_axi_rdata      = S_AXI_RDATA;
  assign s_axi_rresp      = S_AXI_RRESP;
  assign s_axi_rdaddrecc  = S_AXI_RDADDRECC;

  localparam FLOP_DELAY  = 100;  // 100 ps

   reg                       injectsbiterr_in;
   reg                       injectdbiterr_in;
   reg                       rsta_in;
   reg                       ena_in;
   reg                       regcea_in;
   reg [C_WEA_WIDTH-1:0]     wea_in;
   reg [C_ADDRA_WIDTH-1:0]   addra_in;
   reg [C_WRITE_WIDTH_A-1:0] dina_in;

  wire [C_ADDRA_WIDTH-1:0] s_axi_awaddr_out_c;
  wire [C_ADDRB_WIDTH-1:0] s_axi_araddr_out_c;
  wire s_axi_wr_en_c;
  wire s_axi_rd_en_c;
  wire s_aresetn_a_c;
  wire [7:0] s_axi_arlen_c ;


  wire [C_AXI_ID_WIDTH-1 : 0] s_axi_rid_c;
  wire [C_WRITE_WIDTH_B-1 : 0] s_axi_rdata_c;
  wire [1:0] s_axi_rresp_c;
  wire s_axi_rlast_c;
  wire s_axi_rvalid_c;
  wire s_axi_rready_c;
  wire regceb_c;

  localparam C_AXI_PAYLOAD = (C_HAS_MUX_OUTPUT_REGS_B == 1)?C_WRITE_WIDTH_B+C_AXI_ID_WIDTH+3:C_AXI_ID_WIDTH+3;
  wire [C_AXI_PAYLOAD-1 : 0] s_axi_payload_c;
  wire [C_AXI_PAYLOAD-1 : 0] m_axi_payload_c;

// Safety logic related signals

  reg [4:0] RSTA_SHFT_REG = 0;
  reg POR_A = 0; 
  reg [4:0] RSTB_SHFT_REG = 0;
  reg POR_B = 0;
 
  reg ENA_dly = 0;
  reg ENA_dly_D = 0;

  reg ENB_dly = 0;
  reg ENB_dly_D = 0;

  wire RSTA_I_SAFE;
  wire RSTB_I_SAFE;

  wire ENA_I_SAFE;
  wire ENB_I_SAFE;
  
  reg ram_rstram_a_busy = 0;
  reg ram_rstreg_a_busy = 0;
  reg ram_rstram_b_busy = 0;
  reg ram_rstreg_b_busy = 0;

  reg ENA_dly_reg = 0;
  reg ENB_dly_reg = 0;
 
  reg ENA_dly_reg_D = 0;
  reg ENB_dly_reg_D = 0;

  //**************
  // log2roundup
  //**************
  function integer log2roundup (input integer data_value);
      integer width;
      integer cnt;
      begin
         width = 0;

         if (data_value > 1) begin
            for(cnt=1 ; cnt < data_value ; cnt = cnt * 2) begin
               width = width + 1;
            end //loop
         end //if

         log2roundup = width;

      end //log2roundup
   endfunction

  //**************
  // log2int
  //**************
  function integer log2int (input integer data_value);
      integer width;
      integer cnt;
      begin
         width = 0;
		 cnt= data_value;

            for(cnt=data_value ; cnt >1 ; cnt = cnt / 2) begin
               width = width + 1;
            end //loop

         log2int = width;

      end //log2int
   endfunction

 //**************************************************************************
 // FUNCTION : divroundup
 // Returns the ceiling value of the division
 // Data_value - the quantity to be divided, dividend
 // Divisor - the value to divide the data_value by
 //**************************************************************************
  function integer divroundup (input integer data_value,input integer divisor);
      integer div;
      begin
    div   = data_value/divisor;
         if ((data_value % divisor) != 0) begin
      div = div+1;
         end //if
         divroundup = div;
         end //if
   endfunction

  localparam AXI_FULL_MEMORY_SLAVE = ((C_AXI_SLAVE_TYPE == 0 && C_AXI_TYPE == 1)?1:0);
  localparam C_AXI_ADDR_WIDTH_MSB = C_ADDRA_WIDTH+log2roundup(C_WRITE_WIDTH_A/8);
  localparam C_AXI_ADDR_WIDTH     = C_AXI_ADDR_WIDTH_MSB;
 
  //Data Width        Number of LSB address bits to be discarded
  //1 to 16                      1
  //17 to 32                     2
  //33 to 64                     3
  //65 to 128                    4
  //129 to 256                   5
  //257 to 512                   6
  //513 to 1024                  7
  // The following two constants determine this.

  localparam LOWER_BOUND_VAL = (log2roundup(divroundup(C_WRITE_WIDTH_A,8) == 0))?0:(log2roundup(divroundup(C_WRITE_WIDTH_A,8)));
  localparam C_AXI_ADDR_WIDTH_LSB = ((AXI_FULL_MEMORY_SLAVE == 1)?0:LOWER_BOUND_VAL);
  localparam C_AXI_OS_WR = 2;

 //***********************************************
 // INPUT REGISTERS.
 //***********************************************
  generate if (C_HAS_SOFTECC_INPUT_REGS_A==0) begin : no_softecc_input_reg_stage
      always @* begin
      injectsbiterr_in = INJECTSBITERR;
      injectdbiterr_in = INJECTDBITERR;
      rsta_in    = RSTA;
      ena_in     = ENA;
      regcea_in  = REGCEA;
      wea_in     = WEA;
      addra_in   = ADDRA;
      dina_in    = DINA;
      end //end always
      end //end no_softecc_input_reg_stage
 endgenerate

  generate if (C_HAS_SOFTECC_INPUT_REGS_A==1) begin : has_softecc_input_reg_stage
      always @(posedge CLKA) begin
      injectsbiterr_in <= #FLOP_DELAY INJECTSBITERR;
      injectdbiterr_in <= #FLOP_DELAY INJECTDBITERR;
      rsta_in     <= #FLOP_DELAY RSTA;
      ena_in     <= #FLOP_DELAY ENA;
      regcea_in  <= #FLOP_DELAY REGCEA;
      wea_in     <= #FLOP_DELAY WEA;
      addra_in   <= #FLOP_DELAY ADDRA;
      dina_in    <= #FLOP_DELAY DINA;
      end //end always
      end //end input_reg_stages generate statement
 endgenerate

  //**************************************************************************
  // NO SAFETY LOGIC
  //**************************************************************************

   generate 
     if (C_EN_SAFETY_CKT == 0) begin : NO_SAFETY_CKT_GEN
       assign ENA_I_SAFE     = ena_in;
       assign ENB_I_SAFE     = ENB;
       assign RSTA_I_SAFE    = rsta_in;
       assign RSTB_I_SAFE    = RSTB;
     end
   endgenerate

  //***************************************************************************
  // SAFETY LOGIC
  // Power-ON Reset Generation
  //***************************************************************************
  generate 
    if (C_EN_SAFETY_CKT == 1) begin
      always @(posedge clka)  RSTA_SHFT_REG <= #FLOP_DELAY {RSTA_SHFT_REG[3:0],1'b1} ;
      always @(posedge clka)  POR_A <= #FLOP_DELAY RSTA_SHFT_REG[4] ^ RSTA_SHFT_REG[0];
      always @(posedge clkb)  RSTB_SHFT_REG <= #FLOP_DELAY {RSTB_SHFT_REG[3:0],1'b1} ;
      always @(posedge clkb)  POR_B <= #FLOP_DELAY RSTB_SHFT_REG[4] ^ RSTB_SHFT_REG[0]; 
 
      assign RSTA_I_SAFE = rsta_in | POR_A;  
      assign RSTB_I_SAFE = (C_MEM_TYPE == 0 || C_MEM_TYPE == 3) ? 1'b0 : (RSTB | POR_B);
    end
  endgenerate

  //-----------------------------------------------------------------------------
  //  -- RSTA/B_BUSY Generation
  //-----------------------------------------------------------------------------

  generate 
    if ((C_HAS_MEM_OUTPUT_REGS_A==0 || (C_HAS_MEM_OUTPUT_REGS_A==1 && C_RSTRAM_A==1)) && (C_EN_SAFETY_CKT == 1)) begin : RSTA_BUSY_NO_REG
      always @(*) ram_rstram_a_busy = RSTA_I_SAFE | ENA_dly | ENA_dly_D;
      always @(posedge clka) RSTA_BUSY <= #FLOP_DELAY ram_rstram_a_busy;
    end
  endgenerate
  
  generate 
    if (C_HAS_MEM_OUTPUT_REGS_A==1 && C_RSTRAM_A==0 && C_EN_SAFETY_CKT == 1) begin : RSTA_BUSY_WITH_REG
      always @(*) ram_rstreg_a_busy = RSTA_I_SAFE | ENA_dly_reg | ENA_dly_reg_D;
      always @(posedge clka) RSTA_BUSY <= #FLOP_DELAY ram_rstreg_a_busy;
    end
  endgenerate

  generate 
    if ( (C_MEM_TYPE == 0 || C_MEM_TYPE == 3) && C_EN_SAFETY_CKT == 1) begin : SPRAM_RST_BUSY
      always @(*) RSTB_BUSY = 1'b0;
    end
  endgenerate

  generate 
    if ( (C_HAS_MEM_OUTPUT_REGS_B==0 || (C_HAS_MEM_OUTPUT_REGS_B==1 && C_RSTRAM_B==1)) && (C_MEM_TYPE != 0 && C_MEM_TYPE != 3) && C_EN_SAFETY_CKT == 1)  begin : RSTB_BUSY_NO_REG
      always @(*) ram_rstram_b_busy = RSTB_I_SAFE | ENB_dly | ENB_dly_D;
      always @(posedge clkb) RSTB_BUSY <= #FLOP_DELAY ram_rstram_b_busy;
    end
  endgenerate
    
  generate 
    if (C_HAS_MEM_OUTPUT_REGS_B==1 && C_RSTRAM_B==0 && C_MEM_TYPE != 0 && C_MEM_TYPE != 3 && C_EN_SAFETY_CKT == 1) begin : RSTB_BUSY_WITH_REG  
      always @(*) ram_rstreg_b_busy = RSTB_I_SAFE | ENB_dly_reg | ENB_dly_reg_D;
      always @(posedge clkb) RSTB_BUSY <= #FLOP_DELAY ram_rstreg_b_busy;
    end
  endgenerate

  //-----------------------------------------------------------------------------
  //  -- ENA/ENB Generation
  //-----------------------------------------------------------------------------
  
  generate 
    if ((C_HAS_MEM_OUTPUT_REGS_A==0 || (C_HAS_MEM_OUTPUT_REGS_A==1 && C_RSTRAM_A==1)) && C_EN_SAFETY_CKT == 1) begin : ENA_NO_REG    
      always @(posedge clka) begin
        ENA_dly   <= #FLOP_DELAY RSTA_I_SAFE;
        ENA_dly_D <= #FLOP_DELAY ENA_dly;
      end
      assign ENA_I_SAFE = (C_HAS_ENA == 0)? 1'b1 : (ENA_dly_D | ena_in);
    end
  endgenerate

  generate 
    if ( (C_HAS_MEM_OUTPUT_REGS_A==1 && C_RSTRAM_A==0) && C_EN_SAFETY_CKT == 1) begin : ENA_WITH_REG
      always @(posedge clka) begin
        ENA_dly_reg   <= #FLOP_DELAY RSTA_I_SAFE;
        ENA_dly_reg_D <= #FLOP_DELAY ENA_dly_reg;
      end
      assign ENA_I_SAFE = (C_HAS_ENA == 0)? 1'b1 : (ENA_dly_reg_D | ena_in);
    end
  endgenerate

  generate 
    if (C_MEM_TYPE == 0 || C_MEM_TYPE == 3) begin : SPRAM_ENB
      assign ENB_I_SAFE = 1'b0;
    end
  endgenerate

  generate 
    if ((C_HAS_MEM_OUTPUT_REGS_B==0 || (C_HAS_MEM_OUTPUT_REGS_B==1 && C_RSTRAM_B==1)) && C_MEM_TYPE != 0 && C_MEM_TYPE != 3 && C_EN_SAFETY_CKT == 1) begin : ENB_NO_REG
      always @(posedge clkb) begin : PROC_ENB_GEN
        ENB_dly   <= #FLOP_DELAY RSTB_I_SAFE;
        ENB_dly_D <= #FLOP_DELAY ENB_dly;
      end
      assign ENB_I_SAFE = (C_HAS_ENB == 0)? 1'b1 : (ENB_dly_D | ENB);
    end
  endgenerate
  
  generate 
    if (C_HAS_MEM_OUTPUT_REGS_B==1 && C_RSTRAM_B==0 && C_MEM_TYPE != 0 && C_MEM_TYPE != 3 && C_EN_SAFETY_CKT == 1)begin : ENB_WITH_REG
      always @(posedge clkb) begin : PROC_ENB_GEN
        ENB_dly_reg    <= #FLOP_DELAY RSTB_I_SAFE;
        ENB_dly_reg_D  <= #FLOP_DELAY ENB_dly_reg;
      end
      assign ENB_I_SAFE = (C_HAS_ENB == 0)? 1'b1 : (ENB_dly_reg_D | ENB);
    end
  endgenerate

  generate if ((C_INTERFACE_TYPE == 0) && (C_ENABLE_32BIT_ADDRESS == 0)) begin : native_mem_module
blk_mem_gen_v8_4_4_mem_module
  #(.C_CORENAME                        (C_CORENAME),
    .C_FAMILY                          (C_FAMILY),
    .C_XDEVICEFAMILY                   (C_XDEVICEFAMILY),
    .C_MEM_TYPE                        (C_MEM_TYPE),
    .C_BYTE_SIZE                       (C_BYTE_SIZE),
    .C_ALGORITHM                       (C_ALGORITHM),
    .C_USE_BRAM_BLOCK                  (C_USE_BRAM_BLOCK),
    .C_PRIM_TYPE                       (C_PRIM_TYPE),
    .C_LOAD_INIT_FILE                  (C_LOAD_INIT_FILE),
    .C_INIT_FILE_NAME                  (C_INIT_FILE_NAME),
    .C_INIT_FILE                       (C_INIT_FILE),
    .C_USE_DEFAULT_DATA                (C_USE_DEFAULT_DATA),
    .C_DEFAULT_DATA                    (C_DEFAULT_DATA),
    .C_RST_TYPE                        ("SYNC"),
    .C_HAS_RSTA                        (C_HAS_RSTA),
    .C_RST_PRIORITY_A                  (C_RST_PRIORITY_A),
    .C_RSTRAM_A                        (C_RSTRAM_A),
    .C_INITA_VAL                       (C_INITA_VAL),
    .C_HAS_ENA                         (C_HAS_ENA),
    .C_HAS_REGCEA                      (C_HAS_REGCEA),
    .C_USE_BYTE_WEA                    (C_USE_BYTE_WEA),
    .C_WEA_WIDTH                       (C_WEA_WIDTH),
    .C_WRITE_MODE_A                    (C_WRITE_MODE_A),
    .C_WRITE_WIDTH_A                   (C_WRITE_WIDTH_A),
    .C_READ_WIDTH_A                    (C_READ_WIDTH_A),
    .C_WRITE_DEPTH_A                   (C_WRITE_DEPTH_A),
    .C_READ_DEPTH_A                    (C_READ_DEPTH_A),
    .C_ADDRA_WIDTH                     (C_ADDRA_WIDTH),
    .C_HAS_RSTB                        (C_HAS_RSTB),
    .C_RST_PRIORITY_B                  (C_RST_PRIORITY_B),
    .C_RSTRAM_B                        (C_RSTRAM_B),
    .C_INITB_VAL                       (C_INITB_VAL),
    .C_HAS_ENB                         (C_HAS_ENB),
    .C_HAS_REGCEB                      (C_HAS_REGCEB),
    .C_USE_BYTE_WEB                    (C_USE_BYTE_WEB),
    .C_WEB_WIDTH                       (C_WEB_WIDTH),
    .C_WRITE_MODE_B                    (C_WRITE_MODE_B),
    .C_WRITE_WIDTH_B                   (C_WRITE_WIDTH_B),
    .C_READ_WIDTH_B                    (C_READ_WIDTH_B),
    .C_WRITE_DEPTH_B                   (C_WRITE_DEPTH_B),
    .C_READ_DEPTH_B                    (C_READ_DEPTH_B),
    .C_ADDRB_WIDTH                     (C_ADDRB_WIDTH),
    .C_HAS_MEM_OUTPUT_REGS_A           (C_HAS_MEM_OUTPUT_REGS_A),
    .C_HAS_MEM_OUTPUT_REGS_B           (C_HAS_MEM_OUTPUT_REGS_B),
    .C_HAS_MUX_OUTPUT_REGS_A           (C_HAS_MUX_OUTPUT_REGS_A),
    .C_HAS_MUX_OUTPUT_REGS_B           (C_HAS_MUX_OUTPUT_REGS_B),
    .C_HAS_SOFTECC_INPUT_REGS_A        (C_HAS_SOFTECC_INPUT_REGS_A),
    .C_HAS_SOFTECC_OUTPUT_REGS_B       (C_HAS_SOFTECC_OUTPUT_REGS_B),
    .C_MUX_PIPELINE_STAGES             (C_MUX_PIPELINE_STAGES),
    .C_USE_SOFTECC                     (C_USE_SOFTECC),
    .C_USE_ECC                         (C_USE_ECC),
    .C_HAS_INJECTERR                   (C_HAS_INJECTERR),
    .C_SIM_COLLISION_CHECK             (C_SIM_COLLISION_CHECK),
    .C_COMMON_CLK                      (C_COMMON_CLK),
    .FLOP_DELAY                        (FLOP_DELAY),
    .C_DISABLE_WARN_BHV_COLL           (C_DISABLE_WARN_BHV_COLL),
 .C_EN_ECC_PIPE                     (C_EN_ECC_PIPE),
    .C_DISABLE_WARN_BHV_RANGE          (C_DISABLE_WARN_BHV_RANGE))
    blk_mem_gen_v8_4_4_inst
   (.CLKA            (CLKA),
   .RSTA             (RSTA_I_SAFE),//(rsta_in),
   .ENA              (ENA_I_SAFE),//(ena_in),
   .REGCEA           (regcea_in),
   .WEA              (wea_in),
   .ADDRA            (addra_in),
   .DINA             (dina_in),
   .DOUTA            (DOUTA),
   .CLKB             (CLKB),
   .RSTB             (RSTB_I_SAFE),//(RSTB),
   .ENB              (ENB_I_SAFE),//(ENB),
   .REGCEB           (REGCEB),
   .WEB              (WEB),
   .ADDRB            (ADDRB),
   .DINB             (DINB),
   .DOUTB            (DOUTB),
   .INJECTSBITERR    (injectsbiterr_in),
   .INJECTDBITERR    (injectdbiterr_in),
   .ECCPIPECE        (ECCPIPECE),
   .SLEEP            (SLEEP),
   .SBITERR          (SBITERR),
   .DBITERR          (DBITERR),
   .RDADDRECC        (RDADDRECC)
  );
 end
 endgenerate

  generate if((C_INTERFACE_TYPE == 0) && (C_ENABLE_32BIT_ADDRESS == 1)) begin : native_mem_mapped_module

  localparam C_ADDRA_WIDTH_ACTUAL = log2roundup(C_WRITE_DEPTH_A);
  localparam C_ADDRB_WIDTH_ACTUAL = log2roundup(C_WRITE_DEPTH_B);

  localparam C_ADDRA_WIDTH_MSB = C_ADDRA_WIDTH_ACTUAL+log2int(C_WRITE_WIDTH_A/8);
  localparam C_ADDRB_WIDTH_MSB = C_ADDRB_WIDTH_ACTUAL+log2int(C_WRITE_WIDTH_B/8);
 // localparam C_ADDRA_WIDTH_MSB = C_ADDRA_WIDTH_ACTUAL+log2roundup(C_WRITE_WIDTH_A/8);
 // localparam C_ADDRB_WIDTH_MSB = C_ADDRB_WIDTH_ACTUAL+log2roundup(C_WRITE_WIDTH_B/8);
  localparam C_MEM_MAP_ADDRA_WIDTH_MSB     = C_ADDRA_WIDTH_MSB;
  localparam C_MEM_MAP_ADDRB_WIDTH_MSB     = C_ADDRB_WIDTH_MSB;

  // Data Width        Number of LSB address bits to be discarded
  //  1 to 16                      1
  //  17 to 32                     2
  //  33 to 64                     3
  //  65 to 128                    4
  //  129 to 256                   5
  //  257 to 512                   6
  //  513 to 1024                  7
  // The following two constants determine this.

  localparam MEM_MAP_LOWER_BOUND_VAL_A      = (log2int(divroundup(C_WRITE_WIDTH_A,8)==0)) ? 0:(log2int(divroundup(C_WRITE_WIDTH_A,8)));
  localparam MEM_MAP_LOWER_BOUND_VAL_B      = (log2int(divroundup(C_WRITE_WIDTH_B,8)==0)) ? 0:(log2int(divroundup(C_WRITE_WIDTH_B,8)));
  localparam C_MEM_MAP_ADDRA_WIDTH_LSB = MEM_MAP_LOWER_BOUND_VAL_A;
  localparam C_MEM_MAP_ADDRB_WIDTH_LSB = MEM_MAP_LOWER_BOUND_VAL_B;

  wire [C_ADDRB_WIDTH_ACTUAL-1 :0] rdaddrecc_i;
  wire [C_ADDRB_WIDTH-1:C_MEM_MAP_ADDRB_WIDTH_MSB] msb_zero_i;
  wire [C_MEM_MAP_ADDRB_WIDTH_LSB-1:0] lsb_zero_i;
  
  assign msb_zero_i = 0;
  assign lsb_zero_i = 0;
  assign RDADDRECC  = {msb_zero_i,rdaddrecc_i,lsb_zero_i};

blk_mem_gen_v8_4_4_mem_module
  #(.C_CORENAME                        (C_CORENAME),
    .C_FAMILY                          (C_FAMILY),
    .C_XDEVICEFAMILY                   (C_XDEVICEFAMILY),
    .C_MEM_TYPE                        (C_MEM_TYPE),
    .C_BYTE_SIZE                       (C_BYTE_SIZE),
    .C_USE_BRAM_BLOCK                  (C_USE_BRAM_BLOCK),
    .C_ALGORITHM                       (C_ALGORITHM),
    .C_PRIM_TYPE                       (C_PRIM_TYPE),
    .C_LOAD_INIT_FILE                  (C_LOAD_INIT_FILE),
    .C_INIT_FILE_NAME                  (C_INIT_FILE_NAME),
    .C_INIT_FILE                       (C_INIT_FILE),
    .C_USE_DEFAULT_DATA                (C_USE_DEFAULT_DATA),
    .C_DEFAULT_DATA                    (C_DEFAULT_DATA),
    .C_RST_TYPE                        ("SYNC"),
    .C_HAS_RSTA                        (C_HAS_RSTA),
    .C_RST_PRIORITY_A                  (C_RST_PRIORITY_A),
    .C_RSTRAM_A                        (C_RSTRAM_A),
    .C_INITA_VAL                       (C_INITA_VAL),
    .C_HAS_ENA                         (C_HAS_ENA),
    .C_HAS_REGCEA                      (C_HAS_REGCEA),
    .C_USE_BYTE_WEA                    (C_USE_BYTE_WEA),
    .C_WEA_WIDTH                       (C_WEA_WIDTH),
    .C_WRITE_MODE_A                    (C_WRITE_MODE_A),
    .C_WRITE_WIDTH_A                   (C_WRITE_WIDTH_A),
    .C_READ_WIDTH_A                    (C_READ_WIDTH_A),
    .C_WRITE_DEPTH_A                   (C_WRITE_DEPTH_A),
    .C_READ_DEPTH_A                    (C_READ_DEPTH_A),
    .C_ADDRA_WIDTH                     (C_ADDRA_WIDTH_ACTUAL),
    .C_HAS_RSTB                        (C_HAS_RSTB),
    .C_RST_PRIORITY_B                  (C_RST_PRIORITY_B),
    .C_RSTRAM_B                        (C_RSTRAM_B),
    .C_INITB_VAL                       (C_INITB_VAL),
    .C_HAS_ENB                         (C_HAS_ENB),
    .C_HAS_REGCEB                      (C_HAS_REGCEB),
    .C_USE_BYTE_WEB                    (C_USE_BYTE_WEB),
    .C_WEB_WIDTH                       (C_WEB_WIDTH),
    .C_WRITE_MODE_B                    (C_WRITE_MODE_B),
    .C_WRITE_WIDTH_B                   (C_WRITE_WIDTH_B),
    .C_READ_WIDTH_B                    (C_READ_WIDTH_B),
    .C_WRITE_DEPTH_B                   (C_WRITE_DEPTH_B),
    .C_READ_DEPTH_B                    (C_READ_DEPTH_B),
    .C_ADDRB_WIDTH                     (C_ADDRB_WIDTH_ACTUAL),
    .C_HAS_MEM_OUTPUT_REGS_A           (C_HAS_MEM_OUTPUT_REGS_A),
    .C_HAS_MEM_OUTPUT_REGS_B           (C_HAS_MEM_OUTPUT_REGS_B),
    .C_HAS_MUX_OUTPUT_REGS_A           (C_HAS_MUX_OUTPUT_REGS_A),
    .C_HAS_MUX_OUTPUT_REGS_B           (C_HAS_MUX_OUTPUT_REGS_B),
    .C_HAS_SOFTECC_INPUT_REGS_A        (C_HAS_SOFTECC_INPUT_REGS_A),
    .C_HAS_SOFTECC_OUTPUT_REGS_B       (C_HAS_SOFTECC_OUTPUT_REGS_B),
    .C_MUX_PIPELINE_STAGES             (C_MUX_PIPELINE_STAGES),
    .C_USE_SOFTECC                     (C_USE_SOFTECC),
    .C_USE_ECC                         (C_USE_ECC),
    .C_HAS_INJECTERR                   (C_HAS_INJECTERR),
    .C_SIM_COLLISION_CHECK             (C_SIM_COLLISION_CHECK),
    .C_COMMON_CLK                      (C_COMMON_CLK),
    .FLOP_DELAY                        (FLOP_DELAY),
    .C_DISABLE_WARN_BHV_COLL           (C_DISABLE_WARN_BHV_COLL),
 .C_EN_ECC_PIPE                     (C_EN_ECC_PIPE),
    .C_DISABLE_WARN_BHV_RANGE          (C_DISABLE_WARN_BHV_RANGE))
    blk_mem_gen_v8_4_4_inst
   (.CLKA            (CLKA),
   .RSTA             (RSTA_I_SAFE),//(rsta_in),
   .ENA              (ENA_I_SAFE),//(ena_in),
   .REGCEA           (regcea_in),
   .WEA              (wea_in),
   .ADDRA            (addra_in[C_MEM_MAP_ADDRA_WIDTH_MSB-1:C_MEM_MAP_ADDRA_WIDTH_LSB]),
   .DINA             (dina_in),
   .DOUTA            (DOUTA),
   .CLKB             (CLKB),
   .RSTB             (RSTB_I_SAFE),//(RSTB),
   .ENB              (ENB_I_SAFE),//(ENB),
   .REGCEB           (REGCEB),
   .WEB              (WEB),
   .ADDRB            (ADDRB[C_MEM_MAP_ADDRB_WIDTH_MSB-1:C_MEM_MAP_ADDRB_WIDTH_LSB]),
   .DINB             (DINB),
   .DOUTB            (DOUTB),
   .INJECTSBITERR    (injectsbiterr_in),
   .INJECTDBITERR    (injectdbiterr_in),
   .ECCPIPECE        (ECCPIPECE),
   .SLEEP            (SLEEP),
   .SBITERR          (SBITERR),
   .DBITERR          (DBITERR),
   .RDADDRECC        (rdaddrecc_i)
  );
 end
 endgenerate

  generate if (C_HAS_MEM_OUTPUT_REGS_B == 0 && C_HAS_MUX_OUTPUT_REGS_B == 0 ) begin : no_regs
      assign S_AXI_RDATA    = s_axi_rdata_c;
      assign S_AXI_RLAST    = s_axi_rlast_c;
      assign S_AXI_RVALID   = s_axi_rvalid_c;
      assign S_AXI_RID      = s_axi_rid_c;
      assign S_AXI_RRESP    = s_axi_rresp_c;
      assign s_axi_rready_c = S_AXI_RREADY;
 end
 endgenerate

     generate if (C_HAS_MEM_OUTPUT_REGS_B == 1) begin : has_regceb
        assign regceb_c = s_axi_rvalid_c && s_axi_rready_c;
 end
     endgenerate

     generate if (C_HAS_MEM_OUTPUT_REGS_B == 0) begin : no_regceb
        assign regceb_c = REGCEB;
 end
     endgenerate

     generate if (C_HAS_MUX_OUTPUT_REGS_B == 1) begin : only_core_op_regs
        assign s_axi_payload_c = {s_axi_rid_c,s_axi_rdata_c,s_axi_rresp_c,s_axi_rlast_c};
        assign S_AXI_RID       = m_axi_payload_c[C_AXI_PAYLOAD-1 : C_AXI_PAYLOAD-C_AXI_ID_WIDTH];
        assign S_AXI_RDATA     = m_axi_payload_c[C_AXI_PAYLOAD-C_AXI_ID_WIDTH-1 : C_AXI_PAYLOAD-C_AXI_ID_WIDTH-C_WRITE_WIDTH_B];
        assign S_AXI_RRESP     = m_axi_payload_c[2:1];
        assign S_AXI_RLAST     = m_axi_payload_c[0];
 end
     endgenerate

     generate if (C_HAS_MEM_OUTPUT_REGS_B == 1) begin : only_emb_op_regs
        assign s_axi_payload_c = {s_axi_rid_c,s_axi_rresp_c,s_axi_rlast_c};
        assign S_AXI_RDATA     = s_axi_rdata_c;
        assign S_AXI_RID       = m_axi_payload_c[C_AXI_PAYLOAD-1 : C_AXI_PAYLOAD-C_AXI_ID_WIDTH];
        assign S_AXI_RRESP     = m_axi_payload_c[2:1];
        assign S_AXI_RLAST     = m_axi_payload_c[0];
 end
     endgenerate

  generate if (C_HAS_MUX_OUTPUT_REGS_B == 1 || C_HAS_MEM_OUTPUT_REGS_B == 1) begin : has_regs_fwd

    blk_mem_axi_regs_fwd_v8_4
      #(.C_DATA_WIDTH    (C_AXI_PAYLOAD))
    axi_regs_inst (
        .ACLK           (S_ACLK), 
        .ARESET         (s_aresetn_a_c),
        .S_VALID        (s_axi_rvalid_c), 
        .S_READY        (s_axi_rready_c),
        .S_PAYLOAD_DATA (s_axi_payload_c),
        .M_VALID        (S_AXI_RVALID),
        .M_READY        (S_AXI_RREADY),
        .M_PAYLOAD_DATA (m_axi_payload_c)
    );
 end
 endgenerate

  generate if (C_INTERFACE_TYPE == 1) begin : axi_mem_module

assign s_aresetn_a_c = !S_ARESETN;
assign S_AXI_BRESP = 2'b00;
assign s_axi_rresp_c = 2'b00;
assign s_axi_arlen_c = (C_AXI_TYPE == 1)?S_AXI_ARLEN:8'h0;

  blk_mem_axi_write_wrapper_beh_v8_4
    #(.C_INTERFACE_TYPE           (C_INTERFACE_TYPE),
      .C_AXI_TYPE                 (C_AXI_TYPE),
      .C_AXI_SLAVE_TYPE           (C_AXI_SLAVE_TYPE),
      .C_MEMORY_TYPE              (C_MEM_TYPE),
      .C_WRITE_DEPTH_A            (C_WRITE_DEPTH_A),
      .C_AXI_AWADDR_WIDTH         ((AXI_FULL_MEMORY_SLAVE == 1)?C_AXI_ADDR_WIDTH:C_AXI_ADDR_WIDTH-C_AXI_ADDR_WIDTH_LSB),
      .C_HAS_AXI_ID               (C_HAS_AXI_ID),
      .C_AXI_ID_WIDTH             (C_AXI_ID_WIDTH),
      .C_ADDRA_WIDTH              (C_ADDRA_WIDTH),
      .C_AXI_WDATA_WIDTH          (C_WRITE_WIDTH_A),
      .C_AXI_OS_WR                (C_AXI_OS_WR))
  axi_wr_fsm (
      // AXI Global Signals
      .S_ACLK                     (S_ACLK),
      .S_ARESETN                  (s_aresetn_a_c),
      // AXI Full/Lite Slave Write interface
      .S_AXI_AWADDR               (S_AXI_AWADDR[C_AXI_ADDR_WIDTH_MSB-1:C_AXI_ADDR_WIDTH_LSB]),
      .S_AXI_AWLEN                (S_AXI_AWLEN),
      .S_AXI_AWID                 (S_AXI_AWID),
      .S_AXI_AWSIZE               (S_AXI_AWSIZE),
      .S_AXI_AWBURST              (S_AXI_AWBURST),
      .S_AXI_AWVALID              (S_AXI_AWVALID),
      .S_AXI_AWREADY              (S_AXI_AWREADY),
      .S_AXI_WVALID               (S_AXI_WVALID),
      .S_AXI_WREADY               (S_AXI_WREADY),
      .S_AXI_BVALID               (S_AXI_BVALID),
      .S_AXI_BREADY               (S_AXI_BREADY),
      .S_AXI_BID                  (S_AXI_BID),
      // Signals for BRAM interfac(
      .S_AXI_AWADDR_OUT           (s_axi_awaddr_out_c),
      .S_AXI_WR_EN                (s_axi_wr_en_c)
      );

  blk_mem_axi_read_wrapper_beh_v8_4
  #(.C_INTERFACE_TYPE             (C_INTERFACE_TYPE), 
    .C_AXI_TYPE		          (C_AXI_TYPE), 
    .C_AXI_SLAVE_TYPE             (C_AXI_SLAVE_TYPE), 
    .C_MEMORY_TYPE                (C_MEM_TYPE), 
    .C_WRITE_WIDTH_A              (C_WRITE_WIDTH_A), 
    .C_ADDRA_WIDTH                (C_ADDRA_WIDTH), 
    .C_AXI_PIPELINE_STAGES        (1), 
    .C_AXI_ARADDR_WIDTH	          ((AXI_FULL_MEMORY_SLAVE == 1)?C_AXI_ADDR_WIDTH:C_AXI_ADDR_WIDTH-C_AXI_ADDR_WIDTH_LSB), 
    .C_HAS_AXI_ID                 (C_HAS_AXI_ID), 
    .C_AXI_ID_WIDTH               (C_AXI_ID_WIDTH), 
    .C_ADDRB_WIDTH                (C_ADDRB_WIDTH)) 
  axi_rd_sm(
    //AXI Global Signals
    .S_ACLK                       (S_ACLK), 
    .S_ARESETN                    (s_aresetn_a_c),
    //AXI Full/Lite Read Side
    .S_AXI_ARADDR                 (S_AXI_ARADDR[C_AXI_ADDR_WIDTH_MSB-1:C_AXI_ADDR_WIDTH_LSB]),
    .S_AXI_ARLEN                  (s_axi_arlen_c),
    .S_AXI_ARSIZE                 (S_AXI_ARSIZE),
    .S_AXI_ARBURST                (S_AXI_ARBURST),
    .S_AXI_ARVALID                (S_AXI_ARVALID),
    .S_AXI_ARREADY                (S_AXI_ARREADY),
    .S_AXI_RLAST                  (s_axi_rlast_c),
    .S_AXI_RVALID                 (s_axi_rvalid_c),
    .S_AXI_RREADY                 (s_axi_rready_c),
    .S_AXI_ARID                   (S_AXI_ARID),
    .S_AXI_RID                    (s_axi_rid_c),
    //AXI Full/Lite Read FSM Outputs
    .S_AXI_ARADDR_OUT             (s_axi_araddr_out_c),
    .S_AXI_RD_EN                  (s_axi_rd_en_c)
  );

blk_mem_gen_v8_4_4_mem_module
  #(.C_CORENAME                        (C_CORENAME),
    .C_FAMILY                          (C_FAMILY),
    .C_XDEVICEFAMILY                   (C_XDEVICEFAMILY),
    .C_MEM_TYPE                        (C_MEM_TYPE),
    .C_BYTE_SIZE                       (C_BYTE_SIZE),
    .C_USE_BRAM_BLOCK                  (C_USE_BRAM_BLOCK),
    .C_ALGORITHM                       (C_ALGORITHM),
    .C_PRIM_TYPE                       (C_PRIM_TYPE),
    .C_LOAD_INIT_FILE                  (C_LOAD_INIT_FILE),
    .C_INIT_FILE_NAME                  (C_INIT_FILE_NAME),
    .C_INIT_FILE                       (C_INIT_FILE),
    .C_USE_DEFAULT_DATA                (C_USE_DEFAULT_DATA),
    .C_DEFAULT_DATA                    (C_DEFAULT_DATA),
    .C_RST_TYPE                        ("SYNC"),
    .C_HAS_RSTA                        (C_HAS_RSTA),
    .C_RST_PRIORITY_A                  (C_RST_PRIORITY_A),
    .C_RSTRAM_A                        (C_RSTRAM_A),
    .C_INITA_VAL                       (C_INITA_VAL),
    .C_HAS_ENA                         (1),
    .C_HAS_REGCEA                      (C_HAS_REGCEA),
    .C_USE_BYTE_WEA                    (1),
    .C_WEA_WIDTH                       (C_WEA_WIDTH),
    .C_WRITE_MODE_A                    (C_WRITE_MODE_A),
    .C_WRITE_WIDTH_A                   (C_WRITE_WIDTH_A),
    .C_READ_WIDTH_A                    (C_READ_WIDTH_A),
    .C_WRITE_DEPTH_A                   (C_WRITE_DEPTH_A),
    .C_READ_DEPTH_A                    (C_READ_DEPTH_A),
    .C_ADDRA_WIDTH                     (C_ADDRA_WIDTH),
    .C_HAS_RSTB                        (C_HAS_RSTB),
    .C_RST_PRIORITY_B                  (C_RST_PRIORITY_B),
    .C_RSTRAM_B                        (C_RSTRAM_B),
    .C_INITB_VAL                       (C_INITB_VAL),
    .C_HAS_ENB                         (1),
    .C_HAS_REGCEB                      (C_HAS_MEM_OUTPUT_REGS_B),
    .C_USE_BYTE_WEB                    (1),
    .C_WEB_WIDTH                       (C_WEB_WIDTH),
    .C_WRITE_MODE_B                    (C_WRITE_MODE_B),
    .C_WRITE_WIDTH_B                   (C_WRITE_WIDTH_B),
    .C_READ_WIDTH_B                    (C_READ_WIDTH_B),
    .C_WRITE_DEPTH_B                   (C_WRITE_DEPTH_B),
    .C_READ_DEPTH_B                    (C_READ_DEPTH_B),
    .C_ADDRB_WIDTH                     (C_ADDRB_WIDTH),
    .C_HAS_MEM_OUTPUT_REGS_A           (0),
    .C_HAS_MEM_OUTPUT_REGS_B           (C_HAS_MEM_OUTPUT_REGS_B),
    .C_HAS_MUX_OUTPUT_REGS_A           (0),
    .C_HAS_MUX_OUTPUT_REGS_B           (0),
    .C_HAS_SOFTECC_INPUT_REGS_A        (C_HAS_SOFTECC_INPUT_REGS_A),
    .C_HAS_SOFTECC_OUTPUT_REGS_B       (C_HAS_SOFTECC_OUTPUT_REGS_B),
    .C_MUX_PIPELINE_STAGES             (C_MUX_PIPELINE_STAGES),
    .C_USE_SOFTECC                     (C_USE_SOFTECC),
    .C_USE_ECC                         (C_USE_ECC),
    .C_HAS_INJECTERR                   (C_HAS_INJECTERR),
    .C_SIM_COLLISION_CHECK             (C_SIM_COLLISION_CHECK),
    .C_COMMON_CLK                      (C_COMMON_CLK),
    .FLOP_DELAY                        (FLOP_DELAY),
    .C_DISABLE_WARN_BHV_COLL           (C_DISABLE_WARN_BHV_COLL),
	.C_EN_ECC_PIPE                     (0),
    .C_DISABLE_WARN_BHV_RANGE          (C_DISABLE_WARN_BHV_RANGE))
    blk_mem_gen_v8_4_4_inst
   (.CLKA            (S_ACLK),
   .RSTA             (s_aresetn_a_c),
   .ENA              (s_axi_wr_en_c),
   .REGCEA           (regcea_in),
   .WEA              (S_AXI_WSTRB),
   .ADDRA            (s_axi_awaddr_out_c),
   .DINA             (S_AXI_WDATA),
   .DOUTA            (DOUTA),
   .CLKB             (S_ACLK),
   .RSTB             (s_aresetn_a_c),
   .ENB              (s_axi_rd_en_c),
   .REGCEB           (regceb_c),
   .WEB              (WEB_parameterized),
   .ADDRB            (s_axi_araddr_out_c),
   .DINB             (DINB),
   .DOUTB            (s_axi_rdata_c),
   .INJECTSBITERR    (injectsbiterr_in),
   .INJECTDBITERR    (injectdbiterr_in),
   .SBITERR          (SBITERR),
   .DBITERR          (DBITERR),
   .ECCPIPECE        (1'b0),
   .SLEEP            (1'b0),
   .RDADDRECC        (RDADDRECC)
  );
 end
 endgenerate
endmodule



