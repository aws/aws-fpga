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
// File       : pcie_bridge_rc_pcie4c_ip_gt_rate_wait_cdrhold.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
//  Design :  PHY Wrapper 
//  Module :  RATE WAIT CDRHOLD
//--------------------------------------------------------------------------------------------------

`timescale 1ps / 1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_rc_pcie4c_ip_gt_rate_wait_cdrhold #
(
      parameter SYNC_STAGE       = 3
)
(
  input wire          RATEWAITCDRHOLD_PCLK,
  input wire          RATEWAITCDRHOLD_PCLK_RESET_N,
  input wire          [1:0] RATEWAITCDRHOLD_RXRATE,
  input wire          RATEWAITCDRHOLD_CDRHOLDIN,
  
  output wire [1:0]   RATEWAITCDRHOLD_RATEOUT
);

  wire rxcdrholdin_sync;
  
  reg       rate_change;
  
  reg         [ 1:0]                  rate_r;     
  reg         [ 1:0]                  rate_r2;  
  reg [1:0] new_rate = 2'b00;
  reg [1:0] old_rate = 2'b00;  
  reg [2:0] pclk_fsm = 3'd0; 
  reg [1:0] rateout = 2'b00;

  pcie_bridge_rc_pcie4c_ip_sync #(.WIDTH (1), .STAGE (SYNC_STAGE)) sync_rxcdrholdin     (.CLK (RATEWAITCDRHOLD_PCLK), .D (RATEWAITCDRHOLD_CDRHOLDIN),   .Q (rxcdrholdin_sync));

  //PCLK FSM
  localparam PCLK_FSM_IDLE = 2'd0;
  localparam PCLK_FSM_WAIT_CHECKCDRHOLD = 2'd1;
  localparam PCLK_FSM_OUTPUT_RATE = 2'd2;
  
    always @(posedge RATEWAITCDRHOLD_PCLK)
    begin
      if (!RATEWAITCDRHOLD_PCLK_RESET_N) begin
        rate_r <= 2'd0;
        rate_r2 <= 2'd0;
        rate_change <= 1'b0;
        old_rate <= 2'd0; 
        new_rate <= 2'd0;
      end
      else begin
        rate_r <= RATEWAITCDRHOLD_RXRATE;
        rate_r2 <= rate_r;

        if (rate_r2 != rate_r) begin
          rate_change <= 1'b1;
          old_rate <= rate_r2; 
          new_rate <= rate_r;
        end
        else begin
          rate_change <= 1'b0;
        end
      end  
    end
    
    
    always @(posedge RATEWAITCDRHOLD_PCLK)
    begin 
      if (!RATEWAITCDRHOLD_PCLK_RESET_N) begin 
        pclk_fsm <= PCLK_FSM_IDLE; 
        rateout <= 2'b00; 
      end 
      else begin 
        case (pclk_fsm)
        
        PCLK_FSM_IDLE: 
        begin
          rateout <= rateout;
          if (rate_change)
            pclk_fsm <= PCLK_FSM_WAIT_CHECKCDRHOLD;
          else 
            pclk_fsm <= PCLK_FSM_IDLE;
        end 
        
        PCLK_FSM_WAIT_CHECKCDRHOLD: 
        begin 
          rateout <= rateout;
          if (rxcdrholdin_sync || new_rate == 2'b00) 
            pclk_fsm <= PCLK_FSM_OUTPUT_RATE;
          else
            pclk_fsm <= PCLK_FSM_WAIT_CHECKCDRHOLD;
        end
        
        PCLK_FSM_OUTPUT_RATE: 
        begin 
          rateout <= new_rate; 
          pclk_fsm <= PCLK_FSM_IDLE; 
        end 
        
        endcase
      end 
    end
    

  assign RATEWAITCDRHOLD_RATEOUT = rateout;
  
endmodule 
