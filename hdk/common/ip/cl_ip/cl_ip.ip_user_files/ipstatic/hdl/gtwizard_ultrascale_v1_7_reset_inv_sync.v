// (c) Copyright 2013-2015, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////

// ***************************
// * DO NOT MODIFY THIS FILE *
// ***************************

`timescale 1ps/1ps

module gtwizard_ultrascale_v1_7_18_reset_inv_synchronizer # (

  parameter FREQUENCY = 512

)(

  input  wire clk_in,
  input  wire rst_in,
  output wire rst_out

);

  // Use 5 flip-flops as a single synchronizer, and tag each declaration with the appropriate synthesis attribute to
  // enable clustering. Each flip-flop in the synchronizer is asynchronously reset so that the downstream logic is also
  // asynchronously reset but encounters no reset assertion latency. The removal of reset is synchronous, so that the
  // downstream logic is also removed from reset synchronously. This module is designed for active-low reset use.

  (* ASYNC_REG = "TRUE" *) reg rst_in_meta  = 1'b0;
  (* ASYNC_REG = "TRUE" *) reg rst_in_sync1 = 1'b0;
  (* ASYNC_REG = "TRUE" *) reg rst_in_sync2 = 1'b0;
  (* ASYNC_REG = "TRUE" *) reg rst_in_sync3 = 1'b0;
                           reg rst_in_out   = 1'b0;

  always @(posedge clk_in, negedge rst_in) begin
    if (!rst_in) begin
      rst_in_meta  <= 1'b0;
      rst_in_sync1 <= 1'b0;
      rst_in_sync2 <= 1'b0;
      rst_in_sync3 <= 1'b0;
      rst_in_out   <= 1'b0;
    end
    else begin
      rst_in_meta  <= 1'b1;
      rst_in_sync1 <= rst_in_meta;
      rst_in_sync2 <= rst_in_sync1;
      rst_in_sync3 <= rst_in_sync2;
      rst_in_out   <= rst_in_sync3;
    end
  end

  assign rst_out = rst_in_out;


endmodule
