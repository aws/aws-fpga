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
// File       : pcie_bridge_ep_pcie4c_ip_gen4_tx_eq_bridge.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
/*****************************************************************************
** Description:
**    Convert Gen4 Equalization I/F between
**       - PCLK2 (500MHz)
**       - PCLK (250MHz)
**    Only work in 1:2 clock ratio
**
******************************************************************************/

`timescale 1ps/1ps

`define PHYREG(clk, reset, q, d, rstval)  \
   always @(posedge clk) begin \
      if (reset) \
         q  <= #(TCQ)   rstval;  \
      else  \
         q  <= #(TCQ)   d; \
   end

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_ep_pcie4c_ip_gen4_tx_eq_bridge #(
   // Parameters
   parameter integer TCQ   = 1
)  (                                                         
   // Clock & Reset Ports
   input  wire                         phy_pclk2,  
   input  wire                         phy_rst2,           

   // Enable Ports
   input  wire                         bridge_enable,

   // 64b TX Data Ports
   input  wire [1:0]                   phy_txeq_ctrl_pclk,            
   input  wire [3:0]                   phy_txeq_preset_pclk,            
   input  wire [5:0]                   phy_txeq_coeff_pclk,          

   // 32b TX Data Ports
   output reg  [1:0]                   phy_txeq_ctrl_pclk2,            
   output reg  [3:0]                   phy_txeq_preset_pclk2,            
   output reg  [5:0]                   phy_txeq_coeff_pclk2
   );

   reg   [1:0]    phy_txeq_ctrl_pclk2_wire;
   reg   [3:0]    phy_txeq_preset_pclk2_wire;
   reg   [5:0]    phy_txeq_coeff_pclk2_wire;
   reg   [5:0]    saved_pre_cursor_wire, saved_pre_cursor_reg;

   //--------------------------------------------------------------------------
   // TX EQ Conversion Logic
   //--------------------------------------------------------------------------
   // RX State Machine
   localparam TXEQ_IDLE   = 0;
   localparam TXEQ_R1CE   = 1;
   localparam TXEQ_S1CE   = 2;
   localparam TXEQ_CNT    = 3;

   reg   [TXEQ_CNT-1:0] tx_state, tx_state_nxt;

   always @(*) begin
      phy_txeq_ctrl_pclk2_wire   = phy_txeq_ctrl_pclk;
      phy_txeq_preset_pclk2_wire = phy_txeq_preset_pclk;
      phy_txeq_coeff_pclk2_wire  = phy_txeq_coeff_pclk;
      saved_pre_cursor_wire      = saved_pre_cursor_reg;
      tx_state_nxt   = 'd0;
      (* parallel_case *)  case (1'b1)
         tx_state[TXEQ_IDLE]: begin
            if (bridge_enable & (phy_txeq_ctrl_pclk == 2'b10) & (phy_txeq_ctrl_pclk2 != 2'b10)) begin
               phy_txeq_ctrl_pclk2_wire   = 'd0;   // Hold off cursors
               tx_state_nxt[TXEQ_R1CE] = 1'b1;
            end else begin
               tx_state_nxt[TXEQ_IDLE] = 1'b1;
            end
         end
         tx_state[TXEQ_R1CE]: begin
            phy_txeq_ctrl_pclk2_wire   = 'd0;   // Hold off cursors
            saved_pre_cursor_wire      = phy_txeq_coeff_pclk;  // Save pre-cursor (1st)
            tx_state_nxt[TXEQ_S1CE] = 1'b1;
         end
         tx_state[TXEQ_S1CE]: begin
            phy_txeq_coeff_pclk2_wire  = saved_pre_cursor_reg; // Send pre-cursor and following cursors
            tx_state_nxt[TXEQ_IDLE] = 1'b1;
         end
      endcase
   end

   `PHYREG(phy_pclk2, phy_rst2, phy_txeq_ctrl_pclk2, phy_txeq_ctrl_pclk2_wire, 'd0)
   `PHYREG(phy_pclk2, phy_rst2, phy_txeq_preset_pclk2, phy_txeq_preset_pclk2_wire, 'd0)
   `PHYREG(phy_pclk2, phy_rst2, phy_txeq_coeff_pclk2, phy_txeq_coeff_pclk2_wire, 'd0)
   `PHYREG(phy_pclk2, phy_rst2, saved_pre_cursor_reg, saved_pre_cursor_wire, 'd0)
   `PHYREG(phy_pclk2, phy_rst2, tx_state, tx_state_nxt, 'd1)

endmodule
