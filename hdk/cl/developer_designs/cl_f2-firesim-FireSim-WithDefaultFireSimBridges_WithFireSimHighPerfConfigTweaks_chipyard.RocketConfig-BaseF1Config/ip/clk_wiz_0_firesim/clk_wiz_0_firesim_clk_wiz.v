
// file: clk_wiz_0_firesim.v
// (c) Copyright 2017-2018, 2023 Advanced Micro Devices, Inc. All rights reserved.
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
//----------------------------------------------------------------------------
// User entered comments
//----------------------------------------------------------------------------
// None
//
//----------------------------------------------------------------------------
//  Output     Output      Phase    Duty Cycle   Pk-to-Pk     Phase
//   Clock     Freq (MHz)  (degrees)    (%)     Jitter (ps)  Error (ps)
//----------------------------------------------------------------------------
// clk_out1__10.00000______0.000______50.0______260.199____221.273
// clk_out2__175.00000______0.000______50.0______161.023____221.273
// clk_out3__153.12500______0.000______50.0______164.075____221.273
// clk_out4__87.50000______0.000______50.0______177.569____221.273
// clk_out5__87.50000______0.000______50.0______177.569____221.273
// clk_out6__76.56250______0.000______50.0______180.962____221.273
//
//----------------------------------------------------------------------------
// Input Clock   Freq (MHz)    Input Jitter (UI)
//----------------------------------------------------------------------------
// __primary_________125.000____________0.010

`timescale 1ps/1ps

module clk_wiz_0_firesim_clk_wiz 

 (// Clock in ports
  // Clock out ports
  output        clk_out1,
  output        clk_out2,
  output        clk_out3,
  output        clk_out4,
  output        clk_out5,
  output        clk_out6,
  // Status and control signals
  input         reset,
  output        locked,
  input         clk_in1
 );
  // Input buffering
  //------------------------------------
wire clk_in1_clk_wiz_0_firesim;
wire clk_in2_clk_wiz_0_firesim;
  IBUF clkin1_ibuf
   (.O (clk_in1_clk_wiz_0_firesim),
    .I (clk_in1));




  // Clocking PRIMITIVE
  //------------------------------------

  // Instantiation of the MMCM PRIMITIVE
  //    * Unused inputs are tied off
  //    * Unused outputs are labeled unused

  wire        clk_out1_clk_wiz_0_firesim;
  wire        clk_out2_clk_wiz_0_firesim;
  wire        clk_out3_clk_wiz_0_firesim;
  wire        clk_out4_clk_wiz_0_firesim;
  wire        clk_out5_clk_wiz_0_firesim;
  wire        clk_out6_clk_wiz_0_firesim;
  wire        clk_out7_clk_wiz_0_firesim;

  wire [15:0] do_unused;
  wire        drdy_unused;
  wire        psdone_unused;
  wire        locked_int;
  wire        clkfbout_clk_wiz_0_firesim;
  wire        clkfbout_buf_clk_wiz_0_firesim;
  wire        clkfboutb_unused;
    wire clkout0b_unused;
   wire clkout1b_unused;
   wire clkout2b_unused;
   wire clkout3b_unused;
  wire        clkout6_unused;
  wire        clkfbstopped_unused;
  wire        clkinstopped_unused;
  wire        reset_high;


  
    MMCME4_ADV

  #(.BANDWIDTH            ("OPTIMIZED"),
    .CLKOUT4_CASCADE      ("FALSE"),
    .COMPENSATION         ("AUTO"),
    .STARTUP_WAIT         ("FALSE"),
    .DIVCLK_DIVIDE        (5),
    .CLKFBOUT_MULT_F      (49.000),
    .CLKFBOUT_PHASE       (0.000),
    .CLKFBOUT_USE_FINE_PS ("FALSE"),
    .CLKOUT0_DIVIDE_F     (122.500),
    .CLKOUT0_PHASE        (0.000),
    .CLKOUT0_DUTY_CYCLE   (0.500),
    .CLKOUT0_USE_FINE_PS  ("FALSE"),
    .CLKOUT1_DIVIDE       (7),
    .CLKOUT1_PHASE        (0.000),
    .CLKOUT1_DUTY_CYCLE   (0.500),
    .CLKOUT1_USE_FINE_PS  ("FALSE"),
    .CLKOUT2_DIVIDE       (8),
    .CLKOUT2_PHASE        (0.000),
    .CLKOUT2_DUTY_CYCLE   (0.500),
    .CLKOUT2_USE_FINE_PS  ("FALSE"),
    .CLKOUT3_DIVIDE       (14),
    .CLKOUT3_PHASE        (0.000),
    .CLKOUT3_DUTY_CYCLE   (0.500),
    .CLKOUT3_USE_FINE_PS  ("FALSE"),
    .CLKOUT4_DIVIDE       (14),
    .CLKOUT4_PHASE        (0.000),
    .CLKOUT4_DUTY_CYCLE   (0.500),
    .CLKOUT4_USE_FINE_PS  ("FALSE"),
    .CLKOUT5_DIVIDE       (16),
    .CLKOUT5_PHASE        (0.000),
    .CLKOUT5_DUTY_CYCLE   (0.500),
    .CLKOUT5_USE_FINE_PS  ("FALSE"),
    .CLKIN1_PERIOD        (8.000))
  
  mmcme4_adv_inst
    // Output clocks
   (
    .CLKFBOUT            (clkfbout_clk_wiz_0_firesim),
    .CLKFBOUTB           (clkfboutb_unused),
    .CLKOUT0             (clk_out1_clk_wiz_0_firesim),
    .CLKOUT0B            (clkout0b_unused),
    .CLKOUT1             (clk_out2_clk_wiz_0_firesim),
    .CLKOUT1B            (clkout1b_unused),
    .CLKOUT2             (clk_out3_clk_wiz_0_firesim),
    .CLKOUT2B            (clkout2b_unused),
    .CLKOUT3             (clk_out4_clk_wiz_0_firesim),
    .CLKOUT3B            (clkout3b_unused),
    .CLKOUT4             (clk_out5_clk_wiz_0_firesim),
    .CLKOUT5             (clk_out6_clk_wiz_0_firesim),
    .CLKOUT6             (clkout6_unused),
     // Input clock control
    .CLKFBIN             (clkfbout_buf_clk_wiz_0_firesim),
    .CLKIN1              (clk_in1_clk_wiz_0_firesim),
    .CLKIN2              (1'b0),
     // Tied to always select the primary input clock
    .CLKINSEL            (1'b1),
    // Ports for dynamic reconfiguration
    .DADDR               (7'h0),
    .DCLK                (1'b0),
    .DEN                 (1'b0),
    .DI                  (16'h0),
    .DO                  (do_unused),
    .DRDY                (drdy_unused),
    .DWE                 (1'b0),
    .CDDCDONE            (),
    .CDDCREQ             (1'b0),
    // Ports for dynamic phase shift
    .PSCLK               (1'b0),
    .PSEN                (1'b0),
    .PSINCDEC            (1'b0),
    .PSDONE              (psdone_unused),
    // Other control and status signals
    .LOCKED              (locked_int),
    .CLKINSTOPPED        (clkinstopped_unused),
    .CLKFBSTOPPED        (clkfbstopped_unused),
    .PWRDWN              (1'b0),
    .RST                 (reset_high));
  assign reset_high = reset; 

  assign locked = locked_int;
// Clock Monitor clock assigning
//--------------------------------------
 // Output buffering
  //-----------------------------------

  BUFG clkf_buf
   (.O (clkfbout_buf_clk_wiz_0_firesim),
    .I (clkfbout_clk_wiz_0_firesim));






  BUFG clkout1_buf
   (.O   (clk_out1),
    .I   (clk_out1_clk_wiz_0_firesim));


  BUFG clkout2_buf
   (.O   (clk_out2),
    .I   (clk_out2_clk_wiz_0_firesim));

  BUFG clkout3_buf
   (.O   (clk_out3),
    .I   (clk_out3_clk_wiz_0_firesim));

  BUFG clkout4_buf
   (.O   (clk_out4),
    .I   (clk_out4_clk_wiz_0_firesim));

  BUFG clkout5_buf
   (.O   (clk_out5),
    .I   (clk_out5_clk_wiz_0_firesim));

  BUFG clkout6_buf
   (.O   (clk_out6),
    .I   (clk_out6_clk_wiz_0_firesim));



endmodule
