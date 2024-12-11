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
// File       : gen4_phy_defines.vh
// Version    : 1.0 
//-----------------------------------------------------------------------------
/*****************************************************************************
** Description:
**    PCIe Gen4 PHY defines and macros
**
******************************************************************************/

`define PHYREG(clk, reset, q, d, rstval)  \
   always @(posedge clk) begin \
      if (reset) \
         q  <= #(TCQ)   rstval;  \
      else  \
         q  <= #(TCQ)   d; \
   end

`define AS_PHYREG(clk, reset, q, d, rstval)  \
   always @(posedge clk or posedge reset) begin \
      if (reset) \
         q  <= #(TCQ)   rstval;  \
      else  \
         q  <= #(TCQ)   d; \
   end

`define PHYREG_EN(clk, reset, q, d, rstval, en) \
   always @(posedge clk) begin \
      if (reset) \
         q  <= #(TCQ)   rstval;  \
      else  \
         q  <= #(TCQ)   en ? d : q; \
   end

// Fast2Slow
`define FAST2SLOW(bit_width, rst_val, mod_name, fast_input, fast_clk, enable_input, mask_input, slow_reset, fast_reset, slow_clk, slow_output1, slow_output2)   \
   gen4_fast2slow #(.WIDTH(bit_width), .ASYNC("FALSE"), .RST_1(rst_val), .TCQ(TCQ)) mod_name (.fast_bits(fast_input),  \
                                                                                              .fast_clk_i(fast_clk),   \
                                                                                              .enable_i(enable_input), \
                                                                                              .mask_bits(mask_input),  \
                                                                                              .mgmt_reset_fast_i(fast_reset),  \
                                                                                              .mgmt_reset_slow_i(slow_reset),  \
                                                                                              .slow_clk_i(slow_clk),   \
                                                                                              .slow_bits_ns(slow_output1),   \
                                                                                              .slow_bits_r(slow_output2));

`define AS_FAST2SLOW(bit_width, rst_val, mod_name, fast_input, fast_clk, enable_input, mask_input, slow_reset, fast_reset, slow_clk, slow_output1, slow_output2)   \
   gen4_fast2slow #(.WIDTH(bit_width), .ASYNC("TRUE"), .RST_1(rst_val), .TCQ(TCQ)) mod_name (.fast_bits(fast_input),  \
                                                                                             .fast_clk_i(fast_clk),   \
                                                                                             .enable_i(enable_input), \
                                                                                             .mask_bits(mask_input),  \
                                                                                             .mgmt_reset_fast_i(fast_reset),  \
                                                                                             .mgmt_reset_slow_i(slow_reset),  \
                                                                                             .slow_clk_i(slow_clk),   \
                                                                                             .slow_bits_ns(slow_output1),   \
                                                                                             .slow_bits_r(slow_output2));

// FF Chain
`define FF_CHAIN(chain_length, chain_width, rst_value, mod_name, clk_i, rst_i, ff_out, ff_in)   \
   pcie_4_0_phy_ff_chain #(.PIPELINE_STAGES(chain_length), .ASYNC("FALSE"), .FF_WIDTH(chain_width), .RST_VAL(rst_value), .TCQ(TCQ))   \
      mod_name (.clock_i(clk_i), \
                .reset_i(rst_i),   \
                .ff_i(ff_in), \
                .ff_o(ff_out));

`define AS_FF_CHAIN(chain_length, chain_width, rst_value, mod_name, clk_i, rst_i, ff_out, ff_in)   \
   pcie_4_0_phy_ff_chain #(.PIPELINE_STAGES(chain_length), .ASYNC("TRUE"), .FF_WIDTH(chain_width), .RST_VAL(rst_value), .TCQ(TCQ))   \
      mod_name (.clock_i(clk_i), \
                .reset_i(rst_i),   \
                .ff_i(ff_in), \
                .ff_o(ff_out));
