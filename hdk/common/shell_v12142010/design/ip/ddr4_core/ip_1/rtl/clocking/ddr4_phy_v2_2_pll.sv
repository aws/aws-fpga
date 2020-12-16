/******************************************************************************
// (c) Copyright 2013 - 2014 Xilinx, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of Xilinx, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// Xilinx, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) Xilinx shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or Xilinx had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// Xilinx products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of Xilinx products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
******************************************************************************/
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor             : Xilinx
// \   \   \/     Version            : 1.1
//  \   \         Application        : MIG
//  /   /         Filename           : ddr4_phy_v2_2_0_pll.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : infrastructure module
// Purpose          : This module has PLL instance to drive the PHY.
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ps/1ps

module ddr4_phy_v2_2_0_pll #
  (
   parameter SYSCLK_TYPE           = "DIFFERENTIAL", // input clock type
   parameter BACKBONE_ROUTE        = "FALSE",// Enable BACKBONE route for MMCM input
   parameter PLL_WIDTH             = 1,   // Number of PLL clocks
   parameter CLKOUTPHY_MODE        = "VCO_2X", // PHY Mode
   parameter CLKIN_PERIOD_PLL      = 3750,// Fabric clock period
   parameter nCK_PER_CLK           = 4,
   parameter C_FAMILY              = "kintexu",
   parameter TCQ                   = 100  // clk->out delay (sim only)
   )
  (
   // Clock inputs
   input                       sys_clk_p,
   input                       sys_clk_n,
   input                       sys_clk_i,
   input                       ub_rst_out,
   input                       mmcm_lock,
   input                       div_clk,
   input                       div_clk_rst,
   input                       pllgate,

   output                      sys_clk_in,
   output [PLL_WIDTH-1:0]      pll_clk,
   output                      pll_lock,
   output                      mmcm_clk_in
   );

  localparam real CLKIN_PERIOD_NS_PLL   = CLKIN_PERIOD_PLL / 1000.0;
  // PLL Multiply and Divide values
  // write PLL VCO multiplier
  localparam CLKFBOUT_MULT_PLL  = (CLKOUTPHY_MODE == "VCO_2X") ?
                                    ((nCK_PER_CLK == 4) ? 4 : 2) : 
                                  (CLKOUTPHY_MODE == "VCO") ? 
                                    ((nCK_PER_CLK == 4) ? 8 : 4)
                                  : ((nCK_PER_CLK == 4) ? 16 : 8);
  // write PLL VCO divisor
  localparam DIVCLK_DIVIDE_PLL  = 1;
  // VCO output divisor for PLL clkout0
  localparam CLKOUT0_DIVIDE_PLL = (CLKOUTPHY_MODE == "VCO_2X") ? 1 : 
                                  (CLKOUTPHY_MODE == "VCO") ? 2 : 4;

  reg                         clkphyout_en;
  wire [PLL_WIDTH-1:0]        pll_fb;
  wire                        pll_fb_clkoutphy;  
  wire                        pll_clk_int;
  wire [PLL_WIDTH-1:0]        pll_lock_i;

  wire 			              rst_pll  = ~mmcm_lock | ub_rst_out;

  generate
    if (SYSCLK_TYPE == "DIFFERENTIAL") begin: diff_input_clk

      //***********************************************************************
      // Differential input clock input buffers
      //***********************************************************************

      IBUFDS #
        (
         .IBUF_LOW_PWR ("FALSE")
         )
        u_ibufg_sys_clk
          (
           .I  (sys_clk_p),
           .IB (sys_clk_n),
           .O  (sys_clk_in)
           );

    end else if (SYSCLK_TYPE == "SINGLE_ENDED") begin: se_input_clk

      //***********************************************************************
      // SINGLE_ENDED input clock input buffers
      //***********************************************************************

      IBUF #
        (
         .IBUF_LOW_PWR ("FALSE")
         )
        u_ibufg_sys_clk
          (
           .I  (sys_clk_i),
           .O  (sys_clk_in)
           );
    end else if (SYSCLK_TYPE == "NO_BUFFER") begin: internal_clk

      //***********************************************************************
      // System clock is driven from FPGA internal clock (clock from fabric)
      //***********************************************************************
      assign sys_clk_in = sys_clk_i;
   end
  endgenerate

  generate
    if (BACKBONE_ROUTE == "TRUE") begin : gen_bufg_backbone
      BUFG u__bufg_backbone
        (
         .O (mmcm_clk_in),
         .I (sys_clk_in)
         );	
    end else begin : wo_bufg
      assign mmcm_clk_in = sys_clk_in;
    end
  endgenerate

  generate
  genvar i;
    for (i = 0; i < PLL_WIDTH; i++) begin : plle_loop
      if (C_FAMILY == "zynquplus" || C_FAMILY == "kintexuplus" || C_FAMILY == "virtexuplus" || C_FAMILY == "virtexuplusHBM" || C_FAMILY == "virtexuplus58g") begin: gen_plle4
      PLLE4_ADV #(
        .COMPENSATION       ("INTERNAL"),
        .CLKFBOUT_MULT      (CLKFBOUT_MULT_PLL),
        .CLKFBOUT_PHASE     (90.000),
        .CLKIN_PERIOD       (CLKIN_PERIOD_NS_PLL),
        .CLKOUT0_DIVIDE     (CLKOUT0_DIVIDE_PLL),
        .CLKOUT0_DUTY_CYCLE (0.500),
        .CLKOUT0_PHASE      (0.000),
        .CLKOUTPHY_MODE     (CLKOUTPHY_MODE),
        .DIVCLK_DIVIDE      (DIVCLK_DIVIDE_PLL)
      ) PLLE4_BASE_INST_OTHER (
        .CLKFBOUT             (pll_fb[i]),
        .CLKOUT0              (),
        .CLKOUT0B             (),
        .CLKOUT1              (),
        .CLKOUT1B             (),
        .CLKOUTPHY            (pll_clk[i]),
        .LOCKED               (pll_lock_i[i]),
        .CLKFBIN              (pll_fb[i]),
        .CLKIN                (div_clk),
        .CLKOUTPHYEN          (clkphyout_en),
        .PWRDWN               (1'b0),
        .RST                  (rst_pll),

        .DO                   (),
        .DRDY                 (),
        .DADDR                (7'b0),
        .DCLK                 (1'b0),
        .DEN                  (1'b0),
        .DI                   (16'b0),
        .DWE                  (1'b0)
      );
      end else begin : gen_plle3
      PLLE3_ADV #(
        .COMPENSATION       ("INTERNAL"),
        .CLKFBOUT_MULT      (CLKFBOUT_MULT_PLL),
        .CLKFBOUT_PHASE     (90.000),
        .CLKIN_PERIOD       (CLKIN_PERIOD_NS_PLL),
        .CLKOUT0_DIVIDE     (CLKOUT0_DIVIDE_PLL),
        .CLKOUT0_DUTY_CYCLE (0.500),
        .CLKOUT0_PHASE      (0.000),
        .CLKOUTPHY_MODE     (CLKOUTPHY_MODE),
        .DIVCLK_DIVIDE      (DIVCLK_DIVIDE_PLL)
      ) PLLE3_BASE_INST_OTHER (
        .CLKFBOUT             (pll_fb[i]),
        .CLKOUT0              (),
        .CLKOUT0B             (),
        .CLKOUT1              (),
        .CLKOUT1B             (),
        .CLKOUTPHY            (pll_clk[i]),
        .LOCKED               (pll_lock_i[i]),
        .CLKFBIN              (pll_fb[i]),
        .CLKIN                (div_clk),
        .CLKOUTPHYEN          (clkphyout_en),
        .PWRDWN               (1'b0),
        .RST                  (rst_pll),

        .DO                   (),
        .DRDY                 (),
        .DADDR                (7'b0),
        .DCLK                 (1'b0),
        .DEN                  (1'b0),
        .DI                   (16'b0),
        .DWE                  (1'b0)
      );
    end
    end
  endgenerate

  assign pll_lock = &pll_lock_i;

  always @(posedge div_clk) begin
    if (div_clk_rst)
      clkphyout_en <= #TCQ 1'b0;
    else if (pllgate)
      clkphyout_en <= #TCQ 1'b1;
  end

endmodule


