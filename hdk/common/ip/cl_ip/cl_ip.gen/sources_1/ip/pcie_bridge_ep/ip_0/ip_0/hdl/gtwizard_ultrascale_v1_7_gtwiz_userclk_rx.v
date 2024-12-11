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

module gtwizard_ultrascale_v1_7_18_gtwiz_userclk_rx #(

  parameter integer P_CONTENTS                     = 0,
  parameter integer P_FREQ_RATIO_SOURCE_TO_USRCLK  = 1,
  parameter integer P_FREQ_RATIO_USRCLK_TO_USRCLK2 = 1

)(

  input  wire gtwiz_userclk_rx_srcclk_in,
  input  wire gtwiz_userclk_rx_reset_in,
  output wire gtwiz_userclk_rx_usrclk_out,
  output wire gtwiz_userclk_rx_usrclk2_out,
  output wire gtwiz_userclk_rx_active_out

);


  // -------------------------------------------------------------------------------------------------------------------
  // Local parameters
  // -------------------------------------------------------------------------------------------------------------------

  // Convert integer parameters with known, limited legal range to a 3-bit local parameter values
  localparam integer P_USRCLK_INT_DIV  = P_FREQ_RATIO_SOURCE_TO_USRCLK - 1;
  localparam   [2:0] P_USRCLK_DIV      = P_USRCLK_INT_DIV[2:0];
  localparam integer P_USRCLK2_INT_DIV = (P_FREQ_RATIO_SOURCE_TO_USRCLK * P_FREQ_RATIO_USRCLK_TO_USRCLK2) - 1;
  localparam   [2:0] P_USRCLK2_DIV     = P_USRCLK2_INT_DIV[2:0];


  // -------------------------------------------------------------------------------------------------------------------
  // Receiver user clocking network conditional generation, based on parameter values in module instantiation
  // -------------------------------------------------------------------------------------------------------------------
  generate if (1) begin: gen_gtwiz_userclk_rx_main

    // Use BUFG_GT instance(s) to drive RXUSRCLK and RXUSRCLK2, inferred for integral source to RXUSRCLK frequency ratio
    if (P_CONTENTS == 0) begin

      // Drive RXUSRCLK with BUFG_GT-buffered source clock, dividing the input by the integral source clock to RXUSRCLK
      // frequency ratio
      BUFG_GT bufg_gt_usrclk_inst (
        .CE      (1'b1),
        .CEMASK  (1'b0),
        .CLR     (gtwiz_userclk_rx_reset_in),
        .CLRMASK (1'b0),
        .DIV     (P_USRCLK_DIV),
        .I       (gtwiz_userclk_rx_srcclk_in),
        .O       (gtwiz_userclk_rx_usrclk_out)
      );

      // If RXUSRCLK and RXUSRCLK2 frequencies are identical, drive both from the same BUFG_GT. Otherwise, drive
      // RXUSRCLK2 from a second BUFG_GT instance, dividing the source clock down to the RXUSRCLK2 frequency.
      if (P_FREQ_RATIO_USRCLK_TO_USRCLK2 == 1)
        assign gtwiz_userclk_rx_usrclk2_out = gtwiz_userclk_rx_usrclk_out;
      else begin
        BUFG_GT bufg_gt_usrclk2_inst (
          .CE      (1'b1),
          .CEMASK  (1'b0),
          .CLR     (gtwiz_userclk_rx_reset_in),
          .CLRMASK (1'b0),
          .DIV     (P_USRCLK2_DIV),
          .I       (gtwiz_userclk_rx_srcclk_in),
          .O       (gtwiz_userclk_rx_usrclk2_out)
        );
      end

      // Indicate active helper block functionality when the BUFG_GT divider is not held in reset
      (* ASYNC_REG = "TRUE" *) reg gtwiz_userclk_rx_active_meta = 1'b0;
      (* ASYNC_REG = "TRUE" *) reg gtwiz_userclk_rx_active_sync = 1'b0;
      always @(posedge gtwiz_userclk_rx_usrclk2_out, posedge gtwiz_userclk_rx_reset_in) begin
        if (gtwiz_userclk_rx_reset_in) begin
          gtwiz_userclk_rx_active_meta <= 1'b0;
          gtwiz_userclk_rx_active_sync <= 1'b0;
        end
        else begin
          gtwiz_userclk_rx_active_meta <= 1'b1;
          gtwiz_userclk_rx_active_sync <= gtwiz_userclk_rx_active_meta;
        end
      end
      assign gtwiz_userclk_rx_active_out = gtwiz_userclk_rx_active_sync;

    end

  end
  endgenerate


endmodule
