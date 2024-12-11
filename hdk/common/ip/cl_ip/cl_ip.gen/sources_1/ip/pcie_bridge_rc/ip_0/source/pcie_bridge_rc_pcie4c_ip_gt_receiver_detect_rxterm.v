//-----------------------------------------------------------------------------
//
// (c) Copyright 1995, 2007, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// AMD, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) AMD shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or AMD had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// AMD products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of AMD products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
//
//-----------------------------------------------------------------------------
//
// Project    : UltraScale+ FPGA PCI Express CCIX v4.0 Integrated Block
// File       : pcie_bridge_rc_pcie4c_ip_gt_receiver_detect_rxterm.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//------------------------------------------------------------------------------
//  Filename     :  diablo_gt_receiver_detect_rxterm.v
//  Description  :  
//  Version      :  
//------------------------------------------------------------------------------



`timescale 1ns / 1ps



//-------------------------------------------------------------
(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_rc_pcie4c_ip_gt_receiver_detect_rxterm #
(
    parameter SYNC_STAGE       = 3, 
    parameter CONSECUTIVE_CYCLE_OF_RXELECIDLE = 64
)
(
    
    //---------- Input -------------------------------------
    input               RXTERM_CLK, 
    input               RXTERM_RST_N, 
    input               RXTERM_RXELECIDLE, 
    input               RXTERM_MAC_IN_DETECT,
    
    //---------- Output ------------------------------------
    output              RXTERM_RXTERMINATION,
    output      [ 6:0]  RXTERM_FSM
);
    
    //---------- Internal Signals --------------------------
    reg                 rxelecidle_deasserted = 1'b0;
    
    //---------- Output Registers --------------------------
    reg         [ 2:0]  ctrl_fsm =  0;
    reg                 rxelecidle_int = 0;
    
    reg        [6:0]    rxelecidle_cycle_count;
    reg                 rxtermination = 0;

    wire        ctrl_fsm_not_in_solid_deassert;
    
    //---------- Control FSM ------------------------------------
    localparam          FSM_CTRL_IDLE                         = 0;
    localparam          FSM_ASSERT_AVTT                       = 1;
    localparam          FSM_CHECK_RXELECIDLE_ASSERTED         = 2; 
    localparam          FSM_CHECK_RXELECIDLE_SOLID_DEASSERT   = 3;
    localparam          FSM_ASSERT_PROG                       = 4;

    //--------------------------------------------------------------------------
    //  Synchronized Signals
    //--------------------------------------------------------------------------                                  
    wire                rxelecidle_a;
    wire                mac_in_detect_a;
    
    reg   [1:0]         rxelecidle_r;
    reg   [1:0]         mac_in_detect_r;

  pcie_bridge_rc_pcie4c_ip_sync #(.WIDTH (1), .STAGE (SYNC_STAGE)) sync_rxelecidle (.CLK (RXTERM_CLK), .D (RXTERM_RXELECIDLE), .Q (rxelecidle_a));
  pcie_bridge_rc_pcie4c_ip_sync #(.WIDTH (1), .STAGE (SYNC_STAGE)) sync_mac_in_detect (.CLK (RXTERM_CLK), .D (RXTERM_MAC_IN_DETECT), .Q (mac_in_detect_a));

  always @ (posedge RXTERM_CLK) 
  begin
    if (!RXTERM_RST_N) begin
      mac_in_detect_r <= 2'd3;
      rxelecidle_r <= 2'd3;
    end 
    else begin 
        rxelecidle_r <= {rxelecidle_r[0], rxelecidle_a}; 
        mac_in_detect_r <= {mac_in_detect_r[0], mac_in_detect_a};
    end
  end 
  
  always @ (posedge RXTERM_CLK) 
  begin 
    if (ctrl_fsm_not_in_solid_deassert) begin
      rxelecidle_cycle_count <= 7'd0;
    end 
    else begin
      if (!rxelecidle_a)
        rxelecidle_cycle_count <= rxelecidle_cycle_count + 7'd1;        
      else 
        rxelecidle_cycle_count <= 7'd0;
    end
  end
  
  always @(posedge RXTERM_CLK)
  begin 
    if (ctrl_fsm_not_in_solid_deassert) begin
      rxelecidle_int <= 1'b0;
    end 
    else begin
      if (rxelecidle_cycle_count > CONSECUTIVE_CYCLE_OF_RXELECIDLE)
        rxelecidle_int <= 1'b1;
      else 
        rxelecidle_int <= rxelecidle_int;
    end
  end
  
  //---------- FSM to determine when to change RX termination  --------------------
  // counter for rxelecidle. filter for consecutive #, x cycles (parameter) drive our own rxelecidle into state machine. 
  // 
  always @ (posedge RXTERM_CLK) 
  begin 
    if (!RXTERM_RST_N) begin
      ctrl_fsm   <= FSM_ASSERT_AVTT;
      rxtermination <= 1'b1;
    end
    else begin
    
      case (ctrl_fsm)
      
          //---------- Idle State ----------------------------
          FSM_CTRL_IDLE :  
            
              begin
              //----------------------------------------------
              if (!mac_in_detect_r[1]&mac_in_detect_r[0])
                  begin
                    ctrl_fsm  <= FSM_ASSERT_AVTT;
                    rxtermination <= 1'b1;
                  end
              //---------- Idle ------------------------------
              else      
                  begin
                    ctrl_fsm   <= FSM_CTRL_IDLE;
                    rxtermination <= 1'b0;
                  end
              end
              
          //---------- Assert AVTT TERMINATION ----------------
          FSM_ASSERT_AVTT :
          
              begin
                ctrl_fsm <= FSM_CHECK_RXELECIDLE_ASSERTED;
                rxtermination <= 1'b1;
              end
          
          //---------- Check RXELECIDLE is asserted --------------------
          FSM_CHECK_RXELECIDLE_ASSERTED : 
          
            begin 
              ctrl_fsm <= rxelecidle_a ? FSM_CHECK_RXELECIDLE_SOLID_DEASSERT : FSM_CHECK_RXELECIDLE_ASSERTED;
              rxtermination <= rxtermination;
            end
          
          //---------- Wait for RXELECIDELE SOLID DEASSERT and not in mac_in_detect --------------- 
          
          FSM_CHECK_RXELECIDLE_SOLID_DEASSERT:
          
              begin
                ctrl_fsm <= (rxelecidle_int&!mac_in_detect_a) ? FSM_ASSERT_PROG : FSM_CHECK_RXELECIDLE_SOLID_DEASSERT;
                rxtermination <= rxtermination;
              end

          //---------- ASSERT PROG TERMINATION -------------- 
          
          FSM_ASSERT_PROG:
          
              begin 
                ctrl_fsm <= FSM_CTRL_IDLE;
                rxtermination <= 1'b0;
              end
              
          //---------- Default State -------------------------
          default :
          
              begin      
              ctrl_fsm   <= FSM_CTRL_IDLE;
              rxtermination <= 1'b0;
              end
              
          endcase
        end
  end
  
  assign ctrl_fsm_not_in_solid_deassert = (ctrl_fsm != FSM_CHECK_RXELECIDLE_SOLID_DEASSERT);
  assign RXTERM_RXTERMINATION = rxtermination;


endmodule
