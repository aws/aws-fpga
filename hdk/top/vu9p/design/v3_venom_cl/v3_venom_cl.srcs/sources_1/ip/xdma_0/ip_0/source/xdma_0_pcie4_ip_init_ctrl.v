//-----------------------------------------------------------------------------
//
// (c) Copyright 2012-2012 Xilinx, Inc. All rights reserved.
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
//
//-----------------------------------------------------------------------------
//
// Project    : UltraScale+ FPGA PCI Express v4.0 Integrated Block
// File       : xdma_0_pcie4_ip_init_ctrl.v
// Version    : 1.1 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
//**  Description: PCI Express Gen4 Block Initialization Controller
//**  Revision: $Revision: #19 $
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module xdma_0_pcie4_ip_init_ctrl #(
     parameter           TCQ = 100
   , parameter           PL_UPSTREAM_FACING = "TRUE"
   , parameter           IS_SWITCH_PORT = "FALSE"
   , parameter           CRM_CORE_CLK_FREQ_500="TRUE"
   , parameter [1:0]     CRM_USER_CLK_FREQ=2'b10
)(
  input  wire         core_clk_i,
  input  wire         user_clk_i,
  input  wire         phy_rdy_i,
  input  wire         cfg_hot_reset_in_i,
  input  wire         cfg_phy_link_down_i,
  output reg          cfg_phy_link_down_user_clk_o,
  output wire   [2:0] state_o,

  (* keep = "true", max_fanout = 1000 *) output reg          reset_n_o,
  output wire                                                pipe_reset_n_o,
  (* keep = "true", max_fanout = 1000 *) output reg          mgmt_reset_n_o,
  (* keep = "true", max_fanout = 1000 *) output reg          mgmt_sticky_reset_n_o,

  output wire         user_clk_en_o,
  output wire         user_clkgate_en_o
  );

   localparam STATE_RESET   = 3'b000;
   localparam STATE_MGMT_RESET_DEASSERT = 3'b001;
   localparam STATE_PHY_RDY = 3'b100;
   localparam STATE_RESET_DEASSERT = 3'b101;
   
   localparam CLK_QUARTER0  = 3'b0_00; // core=250, user=62.5, user2 = 62.5 
   localparam CLK_HALF0     = 3'b0_01; // core=250, user=125,  user2 = 125
   localparam CLK_EQUAL0    = 3'b0_10; // core=250, user=250,  user2 = 250
   localparam CLK_INVALID0  = 3'b0_11; // core=250, user=250,  user2 = 500
   localparam CLK_INVALID1  = 3'b1_00; // core=500, user=62.5, user2 = 62.5
   localparam CLK_QUARTER1  = 3'b1_01; // core=500, user=125,  user2 = 125
   localparam CLK_HALF1     = 3'b1_10; // core=500, user=250,  user2 = 250
   localparam CLK_HALF2     = 3'b1_11; // core=500, user=250,  user2 = 500

   reg           [2:0] reg_state;
   reg           [2:0] reg_next_state;
(* ASYNC_REG = "TRUE", SHIFT_EXTRACT = "NO" *)    reg           [1:0] reg_phy_rdy = 2'b00; 
   reg           [1:0] reg_cold_reset = 2'b11;
   reg                 reg_reset_n_o;
   reg                 reg_pipe_reset_n_o;
   reg                 reg_mgmt_reset_n_o;
   reg                 reg_mgmt_sticky_reset_n_o;
   reg           [1:0] reg_reset_timer;
   wire          [2:0] state_w;
   wire          [2:0] next_state_w;
   wire                phy_rdy;
   wire                cold_reset_n;
   wire          [1:0] reset_timer_w;
   wire                attr_pl_upstream_facing;
   wire                attr_is_switch_port;

   wire 	       attr_crm_core_clk_freq_500;
   wire [1:0] 	       attr_crm_user_clk_freq;
   wire 	       user2_eq_core;
   reg [1:0] 	       counter;
   
   (* keep = "true", max_fanout = 1000 *) reg 		       user_clk_en_int;
   
   reg 		       user_clkgate_en_int;
   
   
   assign attr_crm_core_clk_freq_500 = (CRM_CORE_CLK_FREQ_500 == "TRUE") ? 1'b1 : 1'b0;
   assign attr_crm_user_clk_freq = CRM_USER_CLK_FREQ[1:0];
				       
   wire [2:0]  coreuser_clk_ratio  = {attr_crm_core_clk_freq_500, attr_crm_user_clk_freq};

  // common values for {attr_crm_core_clk_freq_500, attr_crm_user_clk_freq}
  // attr_crm_core_clk_freq_500,
  // 0 == 250, 1 == 500
  // attr_crm_user_clk_freq,
  // 0 = 62.5/62.5, 1 = 125/125, 2 = 250/250, 3 = 250/500
  //---------------------------------------------------
  // ratios: c:u(:u2)
  // 0/0 250:62.5(62.5)  -> 1/4(/4) CLK_QUARTER0       // user2_eq_core == 0
  // 0/1 250:125 (125)   -> 1/2(/2) CLK_HALF0          // user2_eq_core == 0
  // 0/2 250:250 (250)   -> 1/1(/1) CLK_EQUAL0         // user2_eq_core == 0
  // 0/3 250:250 (500)   -> 1/1(x2) CLK_INVALID0/EQUAL // user2_eq_core == 1
  // 1/0 500:62.5(62.5)  -> 1/8(/8) CLK_INVALID1/EQUAL // user2_eq_core == 0
  // 1/1 500:125 (125)   -> 1/4(/4) CLK_QUARTER1       // user2_eq_core == 0
  // 1/2 500:250 (250)   -> 1/2(/2) CLK_HALF1          // user2_eq_core == 0
  // 1/3 500:250 (500)   -> 1/2(/1) CLK_HALF2          // user2_eq_core == 1
   
   // user2_eq_core high when user_clk2 is equal to core_clk (and faster than user_clk) else equal to user_clk
   //OBSOLETE// assign user2_eq_core = {attr_crm_user_clk_freq == 2'b11};
      
   // when user2_clk is same as core_clk assign coreuser2_clk_ratio to EQUAL, else
   // user2_clk is same as user_clk so use the coreuser_clk_ratio
   //OBSOLETE// wire [2:0]  coreuser2_clk_ratio = user2_eq_core ? CLK_EQUAL0 : coreuser_clk_ratio;


  always @(posedge core_clk_i or negedge mgmt_reset_n_o) begin

    // hold the count during power-on reset
    if (!mgmt_reset_n_o) begin
      user_clkgate_en_int  <= #TCQ 1'b0;
      user_clk_en_int      <= #TCQ 1'b0;
      counter              <= #TCQ 2'h0;
    // normal free-running operation
    end else begin
      // counter always increments and rolls over, no matter the ratio
      counter <= #TCQ counter + 1;

      // Choose the valid based on the table above
      case (coreuser_clk_ratio)
        CLK_HALF0, CLK_HALF1, CLK_HALF2: begin
	   // one core_clk cycle advanced for _e4 input
          user_clkgate_en_int <= #TCQ counter[0];
          user_clk_en_int     <= #TCQ !counter[0];
        end
        CLK_QUARTER0, CLK_QUARTER1: begin
	   // one core_clk cycle advanced for _e4 input 
          user_clkgate_en_int <= #TCQ (counter == 2'h1);
          user_clk_en_int     <= #TCQ (counter == 2'h2);
        end
        default: begin  // and CLK_EQUAL* case which ties off to high
          user_clkgate_en_int <= #TCQ 1'b1;
          user_clk_en_int     <= #TCQ 1'b1;
        end
      endcase

    end

  end
  // }}} user_clk_en generation
 
  assign attr_pl_upstream_facing = (PL_UPSTREAM_FACING == "TRUE") ? 1'b1 : 1'b0 ;
  assign attr_is_switch_port     = (IS_SWITCH_PORT == "TRUE") ? 1'b1 : 1'b0 ;

  // Generate PHY Ready

  always @(posedge user_clk_i)
  begin
    reg_phy_rdy[1:0] <= #TCQ {reg_phy_rdy[0], phy_rdy_i};
  end

  assign phy_rdy = reg_phy_rdy[1];
  
   // Generate Cold reset

  always @(posedge user_clk_i)
  begin
    if (!phy_rdy && reg_cold_reset[1] )
      reg_cold_reset[1:0] <= #TCQ 2'b11;
    else
      reg_cold_reset[1:0] <= #TCQ {reg_cold_reset[0], 1'b0};
  end

  assign cold_reset_n = !reg_cold_reset[1];
  
  // Reset Timer
  
  always @(posedge user_clk_i)
  begin
    if (!phy_rdy_i)
        reg_reset_timer <= #TCQ 2'b00;
    else if ((state_w == STATE_MGMT_RESET_DEASSERT) && (reset_timer_w != 2'b11))
        reg_reset_timer <= #TCQ reset_timer_w + 1'b1;
    else
        reg_reset_timer <= #TCQ reset_timer_w;    
  end
  
  
  // Reset SM
  
  always @(posedge user_clk_i or negedge cold_reset_n)
  begin
    if (!cold_reset_n)
      reg_state <= #TCQ STATE_RESET;
    else
      reg_state <= #TCQ reg_next_state;
  end
  
  always @* begin

    if (attr_pl_upstream_facing) begin // Design is a Upstream Port 

      reg_next_state = STATE_RESET;
      reg_mgmt_reset_n_o = 1'b1;
      reg_mgmt_sticky_reset_n_o = 1'b1;
      reg_reset_n_o = 1'b0;
      reg_pipe_reset_n_o = 1'b0;
      case (state_w)
        STATE_RESET:
        begin
          reg_mgmt_reset_n_o = 1'b0;
          reg_mgmt_sticky_reset_n_o = 1'b0;
          if (phy_rdy)
            reg_next_state = STATE_MGMT_RESET_DEASSERT;
          else
            reg_next_state = STATE_RESET;
          end
        STATE_MGMT_RESET_DEASSERT:
        begin
          if (reset_timer_w == 2'b11)
          reg_next_state = STATE_RESET_DEASSERT;
          else
          reg_next_state = STATE_MGMT_RESET_DEASSERT;
        end
        STATE_RESET_DEASSERT:
        begin
          reg_reset_n_o = 1'b1;
          reg_pipe_reset_n_o = 1'b1;
          if (!phy_rdy)
            reg_next_state = STATE_RESET;
          else
            reg_next_state = STATE_RESET_DEASSERT;
            end
      endcase

    end else  begin // Design is a Downstream Port
      
      reg_next_state = STATE_RESET;
      reg_mgmt_reset_n_o = 1'b1;
      reg_mgmt_sticky_reset_n_o = 1'b1;
      reg_reset_n_o = 1'b0;
      reg_pipe_reset_n_o = 1'b0;
      case (state_w)
        STATE_RESET:
        begin
          reg_mgmt_reset_n_o = 1'b0;
          reg_mgmt_sticky_reset_n_o = 1'b0;
          if (phy_rdy)
            reg_next_state = STATE_MGMT_RESET_DEASSERT;
          else
            reg_next_state = STATE_RESET;
        end
        STATE_MGMT_RESET_DEASSERT:
        begin
          if (reset_timer_w == 2'b11)
            reg_next_state = STATE_PHY_RDY;
          else
            reg_next_state = STATE_MGMT_RESET_DEASSERT;
          end
        STATE_PHY_RDY:
        begin
          if (phy_rdy)
            reg_next_state = STATE_RESET_DEASSERT;
          else
            reg_next_state = STATE_PHY_RDY;
        end
        STATE_RESET_DEASSERT:
        begin
          reg_reset_n_o = 1'b1;
          reg_pipe_reset_n_o = 1'b1;
          if (!phy_rdy)
            reg_next_state = STATE_PHY_RDY;
          else if (attr_is_switch_port && cfg_hot_reset_in_i) begin  // Downstream Port Only
            reg_next_state = STATE_RESET_DEASSERT;
            reg_mgmt_reset_n_o = 1'b0;  
          end else
            reg_next_state = STATE_RESET_DEASSERT;
        end
      endcase
     
    end

  end // 

  // Reset registers pipeline

  (* keep = "true", max_fanout = 1000 *) reg reg_reset_n_2;
  (* keep = "true", max_fanout = 1000 *) reg mgmt_reset_n_2;
  (* keep = "true", max_fanout = 1000 *) reg mgmt_sticky_reset_n_2;
  
  always @(posedge user_clk_i or negedge phy_rdy)
  begin
    if (!phy_rdy)
    begin
      reg_reset_n_2         <= #TCQ 1'b0;
      mgmt_reset_n_2        <= #TCQ 1'b0;
      mgmt_sticky_reset_n_2 <= #TCQ 1'b0;
      
      reset_n_o             <= #TCQ 1'b0;
      mgmt_reset_n_o        <= #TCQ 1'b0;
      mgmt_sticky_reset_n_o <= #TCQ 1'b0;
    end
    else
    begin
      reg_reset_n_2         <= #TCQ reg_reset_n_o;
      mgmt_reset_n_2        <= #TCQ reg_mgmt_reset_n_o;
      mgmt_sticky_reset_n_2 <= #TCQ reg_mgmt_sticky_reset_n_o;
      
      reset_n_o             <= #TCQ reg_reset_n_2;
      mgmt_reset_n_o        <= #TCQ mgmt_reset_n_2;
      mgmt_sticky_reset_n_o <= #TCQ mgmt_sticky_reset_n_2;
    end
  end

   assign state_w = reg_state;
   assign next_state_w = reg_next_state;
   assign pipe_reset_n_o = reg_pipe_reset_n_o;
   assign state_o = reg_state;
   assign reset_timer_w = reg_reset_timer;

   assign user_clkgate_en_o  = user_clkgate_en_int;

   assign user_clk_en_o  = user_clk_en_int;

     // Retime cfg_phy_link_down to user clock

  always @(posedge user_clk_i or negedge phy_rdy)
  begin
    if (!phy_rdy)
      cfg_phy_link_down_user_clk_o <= #TCQ 1'b1;
    else
      cfg_phy_link_down_user_clk_o <= #TCQ cfg_phy_link_down_i;
  end

endmodule
