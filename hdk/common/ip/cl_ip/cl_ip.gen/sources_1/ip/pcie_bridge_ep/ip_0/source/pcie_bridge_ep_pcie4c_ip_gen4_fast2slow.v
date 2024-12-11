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
// File       : pcie_bridge_ep_pcie4c_ip_gen4_fast2slow.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
/*****************************************************************************
** Description:
**    PCIe Gen4 PHY PCLK2(Fast) to PCLK(Slow) conversion
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
module pcie_bridge_ep_pcie4c_ip_gen4_fast2slow #(
   // Parameters
   parameter integer WIDTH = 1,
   parameter         ASYNC = "FALSE",
   parameter integer RST_1 = 0,
   parameter integer TCQ   = 1
)  (                  
   input  wire [WIDTH-1:0]             fast_bits,
   input  wire                         fast_clk_i,
   input  wire                         enable_i,
   input  wire [WIDTH-1:0]             mask_bits,
   input  wire                         mgmt_reset_fast_i,
   input  wire                         mgmt_reset_slow_i,
   input  wire                         slow_clk_i,
  
   output wire [WIDTH-1:0]             slow_bits_ns,  
   output reg  [WIDTH-1:0]             slow_bits_r
   );

   // Retime signals transiting from the fast clock domain (x2) to
   // the slow clock domain (x1).
 
   // Assume there will be only a single assertion of a fast
   // clock signal per slow clock. This only works for active high signals.
 
   // Provide two outputs. A clocked output for simple transits and
   // a pre-clocked output for use by logic.  Depend on optimizer
   // to eliminate logic behind unused outputs.

   // mask_bits AND with the input fast_bits prevent fast bits
   // from being registered during a slow clock.  Useful for request
   // high to pulsed complete handshakes. The pulsed complete
   // is fed into the mask and prevents the request from being
   // registered during the complete handshake.

   wire [WIDTH-1:0]     fast_bits_masked = fast_bits & ~mask_bits;
   wire [WIDTH-1:0]     fast_bits_ns;

   reg  [WIDTH-1:0]     fast_bits_r;

   assign fast_bits_ns  = ((slow_bits_r ^ fast_bits_r) & fast_bits_r) |
                          (~(slow_bits_r ^ fast_bits_r) & fast_bits_masked);

   assign slow_bits_ns  = (enable_i)? fast_bits_r: fast_bits;

generate
   if ((ASYNC == "FALSE") && (RST_1 == 0)) begin: sync_rst_0
      `PHYREG(fast_clk_i, mgmt_reset_fast_i, fast_bits_r, fast_bits_ns, 'h0)
      `PHYREG(slow_clk_i, mgmt_reset_slow_i, slow_bits_r, slow_bits_ns, 'h0)
   end else if ((ASYNC == "TRUE") && (RST_1 == 0)) begin: async_rst_0
      `AS_PHYREG(fast_clk_i, mgmt_reset_fast_i, fast_bits_r, fast_bits_ns, 'h0)
      `AS_PHYREG(slow_clk_i, mgmt_reset_slow_i, slow_bits_r, slow_bits_ns, 'h0)
   end else if ((ASYNC == "FALSE") && (RST_1 == 1)) begin: sync_rst_1
      `PHYREG(fast_clk_i, mgmt_reset_fast_i, fast_bits_r, fast_bits_ns, {WIDTH{1'b1}})
      `PHYREG(slow_clk_i, mgmt_reset_slow_i, slow_bits_r, slow_bits_ns, {WIDTH{1'b1}})
   end else if ((ASYNC == "TRUE") && (RST_1 == 1)) begin: async_rst_1
      `AS_PHYREG(fast_clk_i, mgmt_reset_fast_i, fast_bits_r, fast_bits_ns, {WIDTH{1'b1}})
      `AS_PHYREG(slow_clk_i, mgmt_reset_slow_i, slow_bits_r, slow_bits_ns, {WIDTH{1'b1}})
   end
endgenerate

endmodule
