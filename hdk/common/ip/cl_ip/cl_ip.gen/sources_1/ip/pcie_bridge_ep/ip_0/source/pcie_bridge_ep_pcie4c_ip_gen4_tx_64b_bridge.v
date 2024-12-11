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
// File       : pcie_bridge_ep_pcie4c_ip_gen4_tx_64b_bridge.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
/*****************************************************************************
** Description:
**    Covert Gen4 TX Data I/F
**       from 64b at PCLK  (250MHz)
**       to   32b at PCLK2 (500MHz)
**    The conversion logic is bypassed in Gen1/2/3
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
module pcie_bridge_ep_pcie4c_ip_gen4_tx_64b_bridge #(
   // Parameters
   parameter integer TCQ   = 1
)  (                                                         
   // Clock & Reset Ports
   input  wire                         phy_pclk,  
   input  wire                         phy_pclk2,  
   input  wire                         phy_rst2,           

   // Enable Ports
   input  wire                         bridge_enable,

   // 64b TX Data Ports
   input  wire                         phy_txelecidle_64b,
   input  wire [63:0]                  phy_txdata_64b,            
   input  wire [1:0]                   phy_txdatak_64b,            
   input  wire                         phy_txdata_valid_64b,
   input  wire                         phy_txstart_block_64b,      
   input  wire [1:0]                   phy_txsync_header_64b,                    

   // 32b TX Data Ports
   output wire                         phy_txelecidle_32b,
   output wire [31:0]                  phy_txdata_32b,            
   output wire [1:0]                   phy_txdatak_32b,            
   output wire                         phy_txdata_valid_32b,
   output wire                         phy_txstart_block_32b,      
   output wire [1:0]                   phy_txsync_header_32b
   );

   wire  [31:0]   phy_txdata_64b_to_32b;       
   wire           valid_data;
   wire           phy_txdata_valid_muxed;
   wire  [31:0]   phy_txdata_muxed;
   wire           phy_txstart_block_muxed;
   wire  [1:0]    phy_txsync_header_muxed;

   reg   [6:0]    dw_cntr_wire, dw_cntr_reg;
   reg            phy_txdata_valid_32b_wire, phy_txdata_valid_32b_reg;
   reg   [31:0]   phy_txdata_32b_wire, phy_txdata_32b_reg;
   reg   [1:0]    phy_txdatak_32b_reg;
   reg            phy_txstart_block_32b_wire, phy_txstart_block_32b_reg;
   reg   [1:0]    phy_txsync_header_32b_wire, phy_txsync_header_32b_reg;
   reg            phy_txelecidle_32b_reg;
   reg   [31:0]   saved_dw_wire, saved_dw_reg;

   //--------------------------------------------------------------------------
   // Gen4 Bypass Logic
   //--------------------------------------------------------------------------
   assign valid_data             = phy_txdata_valid_64b & bridge_enable & ~phy_txelecidle_64b;
   assign phy_txdata_64b_to_32b  = phy_txdata_64b[31:0];

   assign phy_txdata_muxed          = (bridge_enable)? phy_txdata_32b_wire:         phy_txdata_64b_to_32b;
   assign phy_txdata_valid_muxed    = (bridge_enable)? phy_txdata_valid_32b_wire:   phy_txdata_valid_64b;
   assign phy_txstart_block_muxed   = (bridge_enable)? phy_txstart_block_32b_wire:  phy_txstart_block_64b;
   assign phy_txsync_header_muxed   = (bridge_enable)? phy_txsync_header_32b_wire:  phy_txsync_header_64b;

   //--------------------------------------------------------------------------
   // 64b-to-32b Conversion Logic
   //--------------------------------------------------------------------------

   // 7-bit Counter for data_valid de-assertion
   always @(*) begin
      if (~valid_data) begin
         dw_cntr_wire   = 'd0;
      end else if (phy_txdata_valid_32b_reg) begin
         dw_cntr_wire   = dw_cntr_reg + 1;
      end else begin
         dw_cntr_wire   = dw_cntr_reg;
      end
   end

   `PHYREG(phy_pclk2, phy_rst2, dw_cntr_reg, dw_cntr_wire, 'd0)

   always @(*) begin
      if (valid_data) begin   // Receive new TX data
         if (&dw_cntr_reg[5:0]) begin  // De-assert txdata_valid at dw_cntr 63 or 127 (every 64 DWs)
            phy_txdata_valid_32b_wire  = 1'b0;
         end else begin
            phy_txdata_valid_32b_wire  = 1'b1;
         end
      end else if (dw_cntr_reg[6]) begin  // Send the saved data if dw_cntr >= 64
         phy_txdata_valid_32b_wire  = 1'b1;
      end else begin
         phy_txdata_valid_32b_wire  = 1'b0;
      end
   end

   `PHYREG(phy_pclk2, phy_rst2, phy_txdata_valid_32b_reg, phy_txdata_valid_muxed, 'd0)

   always @(*) begin
      if (valid_data) begin   // Receive new TX data
         if (dw_cntr_reg[6]) begin  // Send the saved data if dw_cntr >= 64
            if (phy_txdata_valid_32b_reg) begin
               phy_txdata_32b_wire  = saved_dw_reg;
            end else begin
               phy_txdata_32b_wire  = phy_txdata_32b_reg;
            end
         end else begin
            if (dw_cntr_reg[0] | ~phy_txdata_valid_32b_reg) begin // Start from the lower DW if lower DW or txdata_valid is de-asserted
               phy_txdata_32b_wire  = phy_txdata_64b[31:0];
            end else begin
               phy_txdata_32b_wire  = phy_txdata_64b[63:32];
            end
         end
      end else if (dw_cntr_reg[6]) begin  // Send the saved data if dw_cntr >= 64
         phy_txdata_32b_wire  = saved_dw_reg;
      end else begin
         phy_txdata_32b_wire  = phy_txdata_32b_reg;
      end
   end

   `PHYREG(phy_pclk2, phy_rst2, phy_txdata_32b_reg, phy_txdata_muxed, 'd0)

   always @(*) begin
      if (valid_data) begin   // Receive new TX data
         if ((&dw_cntr_reg[1:0]) | ~phy_txdata_valid_32b_reg) begin  // Send start_block/sync_header every 4 cycles or when txdata_valid is de-asserted
            phy_txstart_block_32b_wire = 1'b1;
            phy_txsync_header_32b_wire = phy_txsync_header_64b;
         end else begin
            phy_txstart_block_32b_wire = 1'b0;
            phy_txsync_header_32b_wire = 2'b00;
         end
      end else begin
         phy_txstart_block_32b_wire = 1'b0;
         phy_txsync_header_32b_wire = 2'b00;
      end
   end

   `PHYREG(phy_pclk2, phy_rst2, phy_txstart_block_32b_reg, phy_txstart_block_muxed, 'd0)
   `PHYREG(phy_pclk2, phy_rst2, phy_txsync_header_32b_reg, phy_txsync_header_muxed, 'd0)

   always @(*) begin
      if (valid_data) begin   // Receive new TX data
         if (dw_cntr_reg[6]) begin  // Save DWs if dw_cntr >= 64
            if (dw_cntr_reg[0] | ~phy_txdata_valid_32b_reg) begin
               saved_dw_wire  = phy_txdata_64b[63:32];
            end else begin
               saved_dw_wire  = phy_txdata_64b[31:0];
            end
         end else begin
            saved_dw_wire  = saved_dw_reg;
         end
      end else begin
         saved_dw_wire  = saved_dw_reg;
      end
   end

   `PHYREG(phy_pclk2, phy_rst2, saved_dw_reg, saved_dw_wire, 'd0)  
   `PHYREG(phy_pclk2, phy_rst2, phy_txdatak_32b_reg, phy_txdatak_64b, 'd0)
   `PHYREG(phy_pclk2, phy_rst2, phy_txelecidle_32b_reg, phy_txelecidle_64b, 'd0)

   assign phy_txdata_32b         = phy_txdata_32b_reg;
   assign phy_txdatak_32b        = phy_txdatak_32b_reg;
   assign phy_txdata_valid_32b   = phy_txdata_valid_32b_reg;
   assign phy_txstart_block_32b  = phy_txstart_block_32b_reg;
   assign phy_txsync_header_32b  = phy_txsync_header_32b_reg;
   assign phy_txelecidle_32b     = phy_txelecidle_32b_reg;

endmodule
