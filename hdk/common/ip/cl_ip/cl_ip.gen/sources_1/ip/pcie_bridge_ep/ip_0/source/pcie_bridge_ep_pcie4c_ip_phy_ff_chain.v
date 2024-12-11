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
// File       : pcie_bridge_ep_pcie4c_ip_phy_ff_chain.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
/*****************************************************************************
** Description:
**    Flop Chain
**
******************************************************************************/

`timescale 1ps/1ps

`define AS_PHYREG(clk, reset, q, d, rstval)  \
   always @(posedge clk or posedge reset) begin \
      if (reset) \
         q  <= #(TCQ)   rstval;  \
      else  \
         q  <= #(TCQ)   d; \
   end

`define PHYREG(clk, reset, q, d, rstval)  \
   always @(posedge clk) begin \
      if (reset) \
         q  <= #(TCQ)   rstval;  \
      else  \
         q  <= #(TCQ)   d; \
   end

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_ep_pcie4c_ip_phy_ff_chain #(
   // Parameters
   parameter integer PIPELINE_STAGES   = 0,        // 0 = no pipeline; 1 = 1 stage; 2 = 2 stages; 3 = 3 stages
   parameter         ASYNC             = "FALSE",
   parameter integer FF_WIDTH          = 1,
   parameter integer RST_VAL           = 0,
   parameter integer TCQ               = 1
)  (   
   input  wire                         clock_i,          
   input  wire                         reset_i,           
   input  wire [FF_WIDTH-1:0]          ff_i,            
   output wire [FF_WIDTH-1:0]          ff_o        
   );

   genvar   var_i;

   reg   [FF_WIDTH-1:0]          ff_chain [PIPELINE_STAGES:0];

   always @(*) ff_chain[0] = ff_i;

generate
   if (PIPELINE_STAGES > 0) begin:  with_ff_chain
      for (var_i = 0; var_i < PIPELINE_STAGES; var_i = var_i + 1) begin: ff_chain_gen
         if (ASYNC == "TRUE") begin: async_rst
            `AS_PHYREG(clock_i, reset_i, ff_chain[var_i+1], ff_chain[var_i], RST_VAL)
         end else begin: sync_rst
            `PHYREG(clock_i, reset_i, ff_chain[var_i+1], ff_chain[var_i], RST_VAL)
         end
      end
   end
endgenerate

   assign ff_o = ff_chain[PIPELINE_STAGES];

endmodule
