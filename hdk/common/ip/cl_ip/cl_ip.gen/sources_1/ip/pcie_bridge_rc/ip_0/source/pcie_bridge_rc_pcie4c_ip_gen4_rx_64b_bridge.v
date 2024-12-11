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
// File       : pcie_bridge_rc_pcie4c_ip_gen4_rx_64b_bridge.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
/*****************************************************************************
** Description:
**    Covert Gen4 RX Data I/F
**       from 32b at PCLK2 (500MHz)
**       to   64b at PCLK  (250MHz)
**
******************************************************************************/

`timescale 1ps/1ps

`define PHYREG_EN(clk, reset, q, d, rstval, en) \
   always @(posedge clk) begin \
      if (reset) \
         q  <= #(TCQ)   rstval;  \
      else  \
         q  <= #(TCQ)   en ? d : q; \
   end

`define PHYREG(clk, reset, q, d, rstval)  \
   always @(posedge clk) begin \
      if (reset) \
         q  <= #(TCQ)   rstval;  \
      else  \
         q  <= #(TCQ)   d; \
   end

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_rc_pcie4c_ip_gen4_rx_64b_bridge #(
   // Parameters
   parameter integer TCQ   = 1
)  (                                                         
   // Clock & Reset Ports
   input  wire                         phy_pclk,  
   input  wire                         phy_pclk2,  
   input  wire                         phy_rst,           
   input  wire                         phy_rst2,           

   // Enable Ports
   input  wire                         bridge_enable,
   
   // 32b RX Data Ports
   input  wire [31:0]                  phy_rxdata_32b,            
   input  wire [1:0]                   phy_rxdatak_32b,            
   input  wire                         phy_rxdata_valid_32b,         
   input  wire                         phy_rxstart_block_32b,        
   input  wire [1:0]                   phy_rxsync_header_32b,

   // 64b RX Data Ports
   output wire [63:0]                  phy_rxdata_64b,            
   output wire [1:0]                   phy_rxdatak_64b,            
   output wire                         phy_rxdata_valid_64b,         
   output wire [1:0]                   phy_rxstart_block_64b,        
   output wire [1:0]                   phy_rxsync_header_64b
   );

   wire           valid_data;
   wire  [63:0]   phy_rxdata_32b_to_64b;      
   wire  [1:0]    phy_rxstart_block_32b_to_64b;
   wire           phy_rxdata_valid_64b_muxed;
   wire  [63:0]   phy_rxdata_64b_muxed;
   wire  [1:0]    phy_rxstart_block_64b_muxed;
   wire  [1:0]    phy_rxsync_header_64b_muxed;
   wire           phy_rxdata_valid_odd;

   reg            saved_dw_valid;
   reg   [31:0]   saved_dw, saved_dw_odd;
   reg            saved_start_block, saved_start_block_odd;
   reg   [1:0]    saved_sync_header, saved_sync_header_odd;
   reg            phy_rxdata_valid_64b_wire, phy_rxdata_valid_64b_reg;
   reg   [63:0]   phy_rxdata_64b_wire, phy_rxdata_64b_reg;
   reg   [1:0]    phy_rxdatak_64b_reg;
   reg   [1:0]    phy_rxstart_block_64b_wire, phy_rxstart_block_64b_reg;
   reg   [1:0]    phy_rxsync_header_64b_wire, phy_rxsync_header_64b_reg;

   //--------------------------------------------------------------------------
   // Gen4 Bypass Logic
   //--------------------------------------------------------------------------
   assign valid_data                   = phy_rxdata_valid_32b & bridge_enable;
   assign phy_rxdata_32b_to_64b        = {32'b0, phy_rxdata_32b};
   assign phy_rxstart_block_32b_to_64b = {1'b0, phy_rxstart_block_32b};

   assign phy_rxdata_64b_muxed         = (bridge_enable)? phy_rxdata_64b_wire:         phy_rxdata_32b_to_64b;
   assign phy_rxdata_valid_64b_muxed   = (bridge_enable)? phy_rxdata_valid_64b_wire:   phy_rxdata_valid_32b;                
   assign phy_rxstart_block_64b_muxed  = (bridge_enable)? phy_rxstart_block_64b_wire:  phy_rxstart_block_32b_to_64b;                      
   assign phy_rxsync_header_64b_muxed  = (bridge_enable)? phy_rxsync_header_64b_wire:  phy_rxsync_header_32b;  

   //--------------------------------------------------------------------------
   // 32b-to-64b Conversion Logic
   //--------------------------------------------------------------------------

   // RX State Machine
   localparam RX_IDLE   = 0;
   localparam RX_EVEN   = 1;
   localparam RX_ODD    = 2;
   localparam ST_CNT    = 3;

   reg   [ST_CNT-1:0]   rx_state, rx_state_nxt;

   always @(*) begin
      rx_state_nxt   = 'd0;
      phy_rxdata_valid_64b_wire  = 1'b0;
      phy_rxdata_64b_wire        = 64'd0;
      phy_rxstart_block_64b_wire = 2'b00;
      phy_rxsync_header_64b_wire = 2'b00;

      (* parallel_case *)  case (1'b1)
         rx_state[RX_IDLE]: begin
            if (valid_data) begin
               if (saved_dw_valid) begin  // Start at Even
                  rx_state_nxt[RX_EVEN]      = 1'b1;
                  phy_rxdata_valid_64b_wire  = 1'b1;
                  phy_rxdata_64b_wire        = {phy_rxdata_32b, saved_dw};
                  if (saved_start_block) begin
                     phy_rxstart_block_64b_wire = 2'b01;
                     phy_rxsync_header_64b_wire = saved_sync_header;
                  end else if (phy_rxstart_block_32b) begin // Won't be hit
                     phy_rxstart_block_64b_wire = 2'b10;
                     phy_rxsync_header_64b_wire = phy_rxsync_header_32b;
                  end else begin // Won't be hit
                     phy_rxstart_block_64b_wire = 2'b00;
                     phy_rxsync_header_64b_wire = 2'b00;
                  end
               end else begin             // Start at Odd
                  rx_state_nxt[RX_ODD]       = 1'b1;
               end
            end else begin
               rx_state_nxt[RX_IDLE]      = 1'b1;
            end
         end
         
         rx_state[RX_EVEN]: begin
            if (valid_data) begin
               if (saved_dw_valid) begin  // Continue
                  rx_state_nxt[RX_EVEN]      = 1'b1;
                  phy_rxdata_valid_64b_wire  = 1'b1;
                  phy_rxdata_64b_wire        = {phy_rxdata_32b, saved_dw};
                  if (saved_start_block) begin
                     phy_rxstart_block_64b_wire = 2'b01;
                     phy_rxsync_header_64b_wire = saved_sync_header;
                  end else if (phy_rxstart_block_32b) begin
                     phy_rxstart_block_64b_wire = 2'b10;
                     phy_rxsync_header_64b_wire = phy_rxsync_header_32b;
                  end else begin
                     phy_rxstart_block_64b_wire = 2'b00;
                     phy_rxsync_header_64b_wire = 2'b00;
                  end
               end else begin             // Skip and save
                  rx_state_nxt[RX_ODD]       = 1'b1;
               end
            end else begin
               if (saved_dw_valid) begin  // Skip and save
                  rx_state_nxt[RX_ODD]       = 1'b1;
               end else begin             // End
                  rx_state_nxt[RX_IDLE]      = 1'b1;
               end
            end
         end

         rx_state[RX_ODD]: begin
            if (valid_data) begin
               if (saved_dw_valid) begin  // Continue
                  rx_state_nxt[RX_ODD]       = 1'b1;
                  phy_rxdata_valid_64b_wire  = 1'b1;
                  phy_rxdata_64b_wire        = {saved_dw, saved_dw_odd};
                  if (saved_start_block_odd) begin
                     phy_rxstart_block_64b_wire = 2'b01;
                     phy_rxsync_header_64b_wire = saved_sync_header_odd;
                  end else if (saved_start_block) begin
                     phy_rxstart_block_64b_wire = 2'b10;
                     phy_rxsync_header_64b_wire = saved_sync_header;
                  end else begin
                     phy_rxstart_block_64b_wire = 2'b00;
                     phy_rxsync_header_64b_wire = 2'b00;
                  end                  
               end else begin             // Send saved DWs
                  rx_state_nxt[RX_EVEN]      = 1'b1;
                  phy_rxdata_valid_64b_wire  = 1'b1;
                  phy_rxdata_64b_wire        = {phy_rxdata_32b, saved_dw};
                  if (saved_start_block) begin  // Won't be hit
                     phy_rxstart_block_64b_wire = 2'b01;
                     phy_rxsync_header_64b_wire = saved_sync_header;
                  end else if (phy_rxstart_block_32b) begin
                     phy_rxstart_block_64b_wire = 2'b10;
                     phy_rxsync_header_64b_wire = phy_rxsync_header_32b;
                  end else begin
                     phy_rxstart_block_64b_wire = 2'b00;
                     phy_rxsync_header_64b_wire = 2'b00;
                  end
               end
            end else begin
               if (saved_dw_valid) begin  // Send saved DWs
                  rx_state_nxt[RX_EVEN]      = 1'b1;
                  phy_rxdata_valid_64b_wire  = 1'b1;
                  phy_rxdata_64b_wire        = {saved_dw, saved_dw_odd};
                  if (saved_start_block_odd) begin // Won't be hit
                     phy_rxstart_block_64b_wire = 2'b01;
                     phy_rxsync_header_64b_wire = saved_sync_header_odd;
                  end else if (saved_start_block) begin  // Won't be hit
                     phy_rxstart_block_64b_wire = 2'b10;
                     phy_rxsync_header_64b_wire = saved_sync_header;
                  end else begin
                     phy_rxstart_block_64b_wire = 2'b00;
                     phy_rxsync_header_64b_wire = 2'b00;
                  end                  
               end else begin             // Send saved DWs and end
                  rx_state_nxt[RX_IDLE]      = 1'b1;
                  phy_rxdata_valid_64b_wire  = 1'b1;
                  phy_rxdata_64b_wire        = {32'd0, saved_dw_odd};
                  phy_rxstart_block_64b_wire = 2'b11; // Only lower DW is valid
               end
            end
         end
      endcase
   end

   `PHYREG(phy_pclk, phy_rst, rx_state, rx_state_nxt, 'd1)
   `PHYREG(phy_pclk, phy_rst, phy_rxdata_valid_64b_reg, phy_rxdata_valid_64b_muxed, 'd0)
   `PHYREG(phy_pclk, phy_rst, phy_rxdata_64b_reg, phy_rxdata_64b_muxed, 'd0)
   `PHYREG(phy_pclk, phy_rst, phy_rxdatak_64b_reg, phy_rxdatak_32b, 'd0)
   `PHYREG(phy_pclk, phy_rst, phy_rxstart_block_64b_reg, phy_rxstart_block_64b_muxed, 'd0)
   `PHYREG(phy_pclk, phy_rst, phy_rxsync_header_64b_reg, phy_rxsync_header_64b_muxed, 'd0)

   // Store DW for 64b combining
   `PHYREG(phy_pclk2, phy_rst2, saved_dw_valid, valid_data, 'd0)
   `PHYREG_EN(phy_pclk2, phy_rst2, saved_dw, phy_rxdata_32b, 'd0, valid_data)
   `PHYREG_EN(phy_pclk2, phy_rst2, saved_start_block, phy_rxstart_block_32b, 'd0, valid_data)
   `PHYREG_EN(phy_pclk2, phy_rst2, saved_sync_header, phy_rxsync_header_32b, 'd0, valid_data)

   // Store DW for ODD phase (RX_ODD)
   assign phy_rxdata_valid_odd   = valid_data & rx_state[RX_ODD];
   `PHYREG_EN(phy_pclk2, phy_rst2, saved_dw_odd, saved_dw, 'd0, phy_rxdata_valid_odd)
   `PHYREG_EN(phy_pclk2, phy_rst2, saved_start_block_odd, saved_start_block, 'd0, phy_rxdata_valid_odd)
   `PHYREG_EN(phy_pclk2, phy_rst2, saved_sync_header_odd, saved_sync_header, 'd0, phy_rxdata_valid_odd)   

   assign phy_rxdata_64b         = phy_rxdata_64b_reg;
   assign phy_rxdatak_64b        = phy_rxdatak_64b_reg;
   assign phy_rxdata_valid_64b   = phy_rxdata_valid_64b_reg;
   assign phy_rxstart_block_64b  = phy_rxstart_block_64b_reg;
   assign phy_rxsync_header_64b  = phy_rxsync_header_64b_reg;

endmodule
