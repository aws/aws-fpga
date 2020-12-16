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
//  /   /         Filename           : ddr4_v2_2_10_infrastructure.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
//Device: UltraScale
// Design Name      : infrastructure module
// Purpose          : This module has MMCM instance to generate the fabric and
//                    RIU clocks. Includes the fabric and RIU clock reset logic
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ps/1ps

module ddr4_v2_2_10_infrastructure #
  (
   parameter CLKIN_PERIOD_MMCM     = 3750,// Input clock period
   parameter CLKFBOUT_MULT_MMCM    = 4,   // write MMCM VCO multiplier
   parameter DIVCLK_DIVIDE_MMCM    = 1,   // write MMCM VCO divisor
   parameter CLKOUT0_DIVIDE_MMCM   = 4,   // VCO output divisor for MMCM clkout0
   parameter CLKOUT1_DIVIDE_MMCM   = 4,   // VCO output divisor for MMCM clkout1
   parameter CLKOUT2_DIVIDE_MMCM   = 4,   // VCO output divisor for MMCM clkout2
   parameter CLKOUT3_DIVIDE_MMCM   = 4,   // VCO output divisor for MMCM clkout3
   parameter CLKOUT4_DIVIDE_MMCM   = 4,   // VCO output divisor for MMCM clkout4
   parameter CLKOUT6_DIVIDE_MMCM   = 2*CLKOUT0_DIVIDE_MMCM,   // VCO output divisor for MMCM clkout6
   parameter C_FAMILY              = "kintexu",
   parameter TCQ                   = 100  // clk->out delay (sim only)
   )
  (
   input                       sys_rst,    // core reset from user application
   input                       sys_clk_in,
   input                       mmcm_clk_in,
   input                       pll_lock,
   
   output                      mmcm_lock,
   output                      div_clk,
   output                      riu_clk,
   output wire                 addn_ui_clkout1,
   output wire                 addn_ui_clkout2,
   output wire                 addn_ui_clkout3,
   output wire                 addn_ui_clkout4,
   output wire                 dbg_clk,

   // Reset outputs
   output                      rstdiv0,
   output                      rstdiv1,
   output                      reset_ub,

   output reg                  pllgate
   );

  localparam real CLKIN_PERIOD_NS_MMCM  = CLKIN_PERIOD_MMCM / 1000.0;

  // # of clock cycles to delay deassertion of reset. Needs to be a fairly
  // high number not so much for metastability protection, but to give time
  // for reset (i.e. stable clock cycles) to propagate through all state
  // machines and to all control signals (i.e. not all control signals have
  // resets, instead they rely on base state logic being reset, and the effect
  // of that reset propagating through the logic). Need this because we may not
  // be getting stable clock cycles while reset asserted (i.e. since reset
  // depends on DCM lock status)
  localparam RST_SYNC_NUM = 24;

  // Round up for clk reset delay to ensure that CLKDIV reset deassertion
  // occurs at same time or after CLK reset deassertion
  localparam RST_DIV_SYNC_NUM = RST_SYNC_NUM;          // Counter For Stretching DIV Reset
  localparam RST_RIU_SYNC_NUM = RST_SYNC_NUM/2;       // Counter For Stretching RIU Reset  
  localparam INPUT_RST_STRETCH = 50;                  // Counter For Stretching Input Reset

  // # of clock cycles to wait before we enable the PLL clock
  localparam PLL_GATE_CNT_LIMIT = 20;

  wire                                                   mmcm_clkout0;
  wire                                                   mmcm_clkout1;
  wire                                                   mmcm_clkout2;
  wire                                                   mmcm_clkout3;
  wire                                                   mmcm_clkout4;
  wire                                                   mmcm_clkout5;
  wire                                                   mmcm_clkout6;
  //wire                                                   mmcm_fb;

 (* keep = "TRUE" , ASYNC_REG = "TRUE" *)  reg  [3:0]                   rst_input_sync_r = 0 ;
 (* keep = "TRUE" , ASYNC_REG = "TRUE" *)  reg  [1:0]                   rst_input_async = 0;
 (* keep = "TRUE" , ASYNC_REG = "TRUE" *)  reg    rst_async_riu_div= 0;
 (* keep = "TRUE" , ASYNC_REG = "TRUE" *)  reg                          rst_async_mb = 0;


 (* keep = "TRUE" , ASYNC_REG = "TRUE" *) reg [1:0] rst_riu_sync_r = 0;  // RIU Clock Domain RST Sync
 (* keep = "TRUE" , ASYNC_REG = "TRUE" *) reg [1:0] rst_div_sync_r = 0;  // DIV Clock Domain RST Sync
 (* keep = "TRUE" , ASYNC_REG = "TRUE" *) reg [1:0] rst_mb_sync_r = 0;   // MB RST Sync

  reg [6:0] counter_input_rst = INPUT_RST_STRETCH  ;  // counter for input reset stretch
  reg [6:0] counter_riu_rst   = RST_RIU_SYNC_NUM ;    // counter for riu reset synchronous deassertion 
  reg [6:0] counter_div_rst   = RST_DIV_SYNC_NUM ;     // counter for fabric reset synchronous deassertion
  reg [6:0] counter_mb_rst    = RST_DIV_SYNC_NUM ;     // counter for mb reset synchronous deassertion
  reg       rst_div_logic = 1'b1;     // Fabric reset
  reg       rst_riu_logic = 1'b1;     // RIU Reset
  reg       rst_mb_logic  = 1'b1;      // MB Reset

 (* keep = "TRUE" , ASYNC_REG = "TRUE" *) reg [2:0] rst_div_logic_r = {3{1'b1}} ;  // Reset synchronizer for Fabric Domain
 (* keep = "TRUE" , ASYNC_REG = "TRUE" *) reg [2:0] rst_riu_logic_r = {3{1'b1}};   // Reset synchronizer for RIU Domain
 (* keep = "TRUE" , ASYNC_REG = "TRUE" *) reg [2:0] rst_mb_logic_r  = {3{1'b1}};    // Reset synchronizer for MB

  reg       rst_div_logic_r1 = 1'b1;   // Final Reset going for Fabric
  reg       rst_riu_logic_r1 = 1'b1;   // FInal Reset GOing for RIu
  reg       rst_mb_logic_r1  = 1'b1;   //  Final Reset going for MB

  reg  [4:0]                                             pll_gate_cnt;

                          reg  input_rst_mmcm = 0 ;
(* keep = "TRUE" *)       reg  input_rst_design = 0;
                          wire sys_clk_in_bufg ;

   BUFG  u_bufg_inst (
   .O(sys_clk_in_bufg), // 1-bit output: Clock output
   .I(sys_clk_in)       // 1-bit input: Primary clock
   );

//////////////// Reset Generation Loigc For MMCM And Design  /////////////////////////
  // Reset synchorinizer
  always @(posedge sys_clk_in_bufg or posedge sys_rst) begin
    if (sys_rst) begin
      rst_input_async[0]   <= #TCQ  1;
    end else begin
      rst_input_async[0]   <= #TCQ  0;
    end
  end

  always @(posedge sys_clk_in_bufg or posedge sys_rst ) begin
    if (sys_rst) begin
      rst_input_async[1]   <= #TCQ  1'b1 ;
    end else begin
      rst_input_async[1]   <= #TCQ  rst_input_async[0] ;
    end
  end


  always @(posedge sys_clk_in_bufg) begin
      rst_input_sync_r[0]     <= #TCQ   rst_input_async[1];
      rst_input_sync_r[3:1]   <= #TCQ   rst_input_sync_r[2:0];
  end

 //Counter For Reset Stretching  
  always @(posedge sys_clk_in_bufg) begin
      if (rst_input_sync_r[3])
          counter_input_rst    <= #TCQ   INPUT_RST_STRETCH;
      else if (counter_input_rst != 0) 
          counter_input_rst    <= #TCQ  counter_input_rst - 1'b1 ;
      else 
          counter_input_rst    <= #TCQ  counter_input_rst ;

  end

  always @(posedge sys_clk_in_bufg) begin
      if (counter_input_rst != 0) 
         input_rst_design <= #TCQ  1'b1 ;
      else 
         input_rst_design <= #TCQ  1'b0 ;
  end

  always @(posedge sys_clk_in_bufg) begin
      if ( (counter_input_rst <= 'd10) && (counter_input_rst != 0)  ) 
         input_rst_mmcm <= #TCQ  1'b1 ;
      else 
         input_rst_mmcm <= #TCQ  1'b0 ;
  end
////////////////END of Reset Generation Block for MMCM and Design ////////////////////

  // MMCM instance generates the fabric and the microblaze clock
  // and generates selected additional clocks in GUI
  generate
    if (C_FAMILY == "zynquplus" || C_FAMILY == "kintexuplus" || C_FAMILY == "virtexuplus" || C_FAMILY == "virtexuplusHBM" || C_FAMILY == "virtexuplus58g") begin: gen_mmcme4
      MMCME4_ADV
      #(.BANDWIDTH            ("OPTIMIZED"),
        .CLKOUT4_CASCADE      ("FALSE"),
        .COMPENSATION         ("INTERNAL"),
        .STARTUP_WAIT         ("FALSE"),
        .DIVCLK_DIVIDE        (DIVCLK_DIVIDE_MMCM),
        .CLKFBOUT_MULT_F      (CLKFBOUT_MULT_MMCM),
        .CLKFBOUT_PHASE       (0.000),
        .CLKFBOUT_USE_FINE_PS ("FALSE"),
        .CLKOUT0_DIVIDE_F     (CLKOUT0_DIVIDE_MMCM),
        .CLKOUT0_PHASE        (0.000),
        .CLKOUT0_DUTY_CYCLE   (0.500),
        .CLKOUT0_USE_FINE_PS  ("FALSE"),
        .CLKOUT1_DIVIDE       (CLKOUT1_DIVIDE_MMCM),
        .CLKOUT1_PHASE        (0.000),
        .CLKOUT1_DUTY_CYCLE   (0.500),
        .CLKOUT1_USE_FINE_PS  ("FALSE"),
        .CLKOUT2_DIVIDE       (CLKOUT2_DIVIDE_MMCM),
        .CLKOUT2_PHASE        (0.000),
        .CLKOUT2_DUTY_CYCLE   (0.500),
        .CLKOUT2_USE_FINE_PS  ("FALSE"),
        .CLKOUT3_DIVIDE       (CLKOUT3_DIVIDE_MMCM),
        .CLKOUT3_PHASE        (0.000),
        .CLKOUT3_DUTY_CYCLE   (0.500),
        .CLKOUT3_USE_FINE_PS  ("FALSE"),
        .CLKOUT4_DIVIDE       (CLKOUT4_DIVIDE_MMCM),
        .CLKOUT4_PHASE        (0.000),
        .CLKOUT4_DUTY_CYCLE   (0.500),
        .CLKOUT4_USE_FINE_PS  ("FALSE"),
        .CLKOUT5_DIVIDE       (CLKOUT0_DIVIDE_MMCM*4),
        .CLKOUT5_PHASE        (0.000),
        .CLKOUT5_DUTY_CYCLE   (0.500),
        .CLKOUT5_USE_FINE_PS  ("FALSE"),
        .CLKOUT6_DIVIDE       (CLKOUT6_DIVIDE_MMCM),
        .CLKOUT6_PHASE        (0.000),
        .CLKOUT6_DUTY_CYCLE   (0.500),
        .CLKOUT6_USE_FINE_PS  ("FALSE"),	
        .CLKIN1_PERIOD        (CLKIN_PERIOD_NS_MMCM),
        .REF_JITTER1          (0.010))
      u_mmcme_adv_inst
        // Output clocks
       (
        .CLKFBOUT            (), //mmcm_fb
        .CLKFBOUTB           (),
        .CLKOUT0             (mmcm_clkout0),

        .CLKOUT0B            (),
        .CLKOUT1             (mmcm_clkout1),
        .CLKOUT1B            (),
        .CLKOUT2             (mmcm_clkout2),
        .CLKOUT2B            (),
        .CLKOUT3             (mmcm_clkout3),
        .CLKOUT3B            (),
        .CLKOUT4             (mmcm_clkout4),
        .CLKOUT5             (mmcm_clkout5),
        .CLKOUT6             (mmcm_clkout6),
         // Input clock control
        .CLKFBIN             (), //mmcm_fb
        .CLKIN1              (mmcm_clk_in),
        .CLKIN2              (1'b0),
        // Other control and status signals
        .LOCKED              (mmcm_lock),
        .PWRDWN              (1'b0),
        .RST                 (input_rst_mmcm),
      
        .CDDCDONE            (),
        .CLKFBSTOPPED        (),
        .CLKINSTOPPED        (),
        .DO                  (),
        .DRDY                (),
        .PSDONE              (),
        .CDDCREQ             (1'b0),
        .CLKINSEL            (1'b1),
        .DADDR               (7'b0),
        .DCLK                (1'b0),
        .DEN                 (1'b0),
        .DI                  (16'b0),
        .DWE                 (1'b0),
        .PSCLK               (1'b0),
        .PSEN                (1'b0),
        .PSINCDEC            (1'b0)
      );
    end else begin : gen_mmcme3
      MMCME3_ADV
      #(.BANDWIDTH            ("OPTIMIZED"),
        .CLKOUT4_CASCADE      ("FALSE"),
        .COMPENSATION         ("INTERNAL"),
        .STARTUP_WAIT         ("FALSE"),
        .DIVCLK_DIVIDE        (DIVCLK_DIVIDE_MMCM),
        .CLKFBOUT_MULT_F      (CLKFBOUT_MULT_MMCM),
        .CLKFBOUT_PHASE       (0.000),
        .CLKFBOUT_USE_FINE_PS ("FALSE"),
        .CLKOUT0_DIVIDE_F     (CLKOUT0_DIVIDE_MMCM),
        .CLKOUT0_PHASE        (0.000),
        .CLKOUT0_DUTY_CYCLE   (0.500),
        .CLKOUT0_USE_FINE_PS  ("FALSE"),
        .CLKOUT1_DIVIDE       (CLKOUT1_DIVIDE_MMCM),
        .CLKOUT1_PHASE        (0.000),
        .CLKOUT1_DUTY_CYCLE   (0.500),
        .CLKOUT1_USE_FINE_PS  ("FALSE"),
        .CLKOUT2_DIVIDE       (CLKOUT2_DIVIDE_MMCM),
        .CLKOUT2_PHASE        (0.000),
        .CLKOUT2_DUTY_CYCLE   (0.500),
        .CLKOUT2_USE_FINE_PS  ("FALSE"),
        .CLKOUT3_DIVIDE       (CLKOUT3_DIVIDE_MMCM),
        .CLKOUT3_PHASE        (0.000),
        .CLKOUT3_DUTY_CYCLE   (0.500),
        .CLKOUT3_USE_FINE_PS  ("FALSE"),
        .CLKOUT4_DIVIDE       (CLKOUT4_DIVIDE_MMCM),
        .CLKOUT4_PHASE        (0.000),
        .CLKOUT4_DUTY_CYCLE   (0.500),
        .CLKOUT4_USE_FINE_PS  ("FALSE"),
        .CLKOUT5_DIVIDE       (CLKOUT0_DIVIDE_MMCM*4),
        .CLKOUT5_PHASE        (0.000),
        .CLKOUT5_DUTY_CYCLE   (0.500),
        .CLKOUT5_USE_FINE_PS  ("FALSE"),
        .CLKOUT6_DIVIDE       (CLKOUT6_DIVIDE_MMCM),
        .CLKOUT6_PHASE        (0.000),
        .CLKOUT6_DUTY_CYCLE   (0.500),
        .CLKOUT6_USE_FINE_PS  ("FALSE"),	
        .CLKIN1_PERIOD        (CLKIN_PERIOD_NS_MMCM),
        .REF_JITTER1          (0.010))
      u_mmcme_adv_inst
        // Output clocks
       (
        .CLKFBOUT            (), //mmcm_fb
        .CLKFBOUTB           (),
        .CLKOUT0             (mmcm_clkout0),
        .CLKOUT0B            (),
        .CLKOUT1             (mmcm_clkout1),
        .CLKOUT1B            (),
        .CLKOUT2             (mmcm_clkout2),
        .CLKOUT2B            (),
        .CLKOUT3             (mmcm_clkout3),
        .CLKOUT3B            (),
        .CLKOUT4             (mmcm_clkout4),
        .CLKOUT5             (mmcm_clkout5),
        .CLKOUT6             (mmcm_clkout6),
         // Input clock control
        .CLKFBIN             (), //mmcm_fb
        .CLKIN1              (mmcm_clk_in),
        .CLKIN2              (1'b0),
        // Other control and status signals
        .LOCKED              (mmcm_lock),
        .PWRDWN              (1'b0),
        .RST                 (input_rst_mmcm),
      
        .CDDCDONE            (),
        .CLKFBSTOPPED        (),
        .CLKINSTOPPED        (),
        .DO                  (),
        .DRDY                (),
        .PSDONE              (),
        .CDDCREQ             (1'b0),
        .CLKINSEL            (1'b1),
        .DADDR               (7'b0),
        .DCLK                (1'b0),
        .DEN                 (1'b0),
        .DI                  (16'b0),
        .DWE                 (1'b0),
        .PSCLK               (1'b0),
        .PSEN                (1'b0),
        .PSINCDEC            (1'b0)
      );
    end
  endgenerate

  BUFG u_bufg_addn_ui_clk_1
    (
     .O (addn_ui_clkout1),
     .I (mmcm_clkout1)
     );

  BUFG u_bufg_addn_ui_clk_2
    (
     .O (addn_ui_clkout2),
     .I (mmcm_clkout2)
     );

  BUFG u_bufg_addn_ui_clk_3
    (
     .O (addn_ui_clkout3),
     .I (mmcm_clkout3)
     );

  BUFG u_bufg_addn_ui_clk_4
    (
     .O (addn_ui_clkout4),
     .I (mmcm_clkout4)
     );

  BUFG u_bufg_dbg_clk
    (
     .O (dbg_clk),
     .I (mmcm_clkout5)
     );

  BUFG u_bufg_divClk
    (
     .O (div_clk),
     .I (mmcm_clkout0)
     );
     
  BUFG u_bufg_riuClk
    (
     .O (riu_clk),
     .I (mmcm_clkout6)
     );

  // assign rst_async_riu_div = input_rst_design | ~(&pll_lock) | ~mmcm_lock;
  // assign rst_async_mb      = input_rst_design | ~mmcm_lock;

  always @(posedge sys_clk_in_bufg) begin
       rst_async_riu_div <= #TCQ input_rst_design | ~(&pll_lock) | ~mmcm_lock;
       rst_async_mb      <= #TCQ input_rst_design | ~mmcm_lock;
  end    
//////////////// Reset for RIU Clock Domain /////////////////////////
  // Reset synchorinizer
  always @(posedge riu_clk) begin
      rst_riu_sync_r[0]   <= #TCQ  rst_async_riu_div ;
      rst_riu_sync_r[1]   <= #TCQ  rst_riu_sync_r[0];
  end

 //Counter For Reset Stretching  
  always @(posedge riu_clk) begin
      if (rst_riu_sync_r[1])
          counter_riu_rst    <= #TCQ   RST_RIU_SYNC_NUM;
      else if (counter_riu_rst != 0) 
          counter_riu_rst    <= #TCQ  counter_riu_rst - 1'b1 ;
      else
          counter_riu_rst    <= #TCQ  counter_riu_rst ;

  end

  always @(posedge riu_clk) begin
      if (counter_riu_rst != 0) 
         rst_riu_logic <= #TCQ  1'b1 ;
      else 
         rst_riu_logic <= #TCQ  1'b0 ;
  end
  
  always @(posedge riu_clk) begin
      rst_riu_logic_r[0]   <= #TCQ rst_riu_logic;
      rst_riu_logic_r[2:1] <= #TCQ rst_riu_logic_r[1:0];
      rst_riu_logic_r1     <= #TCQ rst_riu_logic_r[2];
  end
////////////////END of Reset Block for RIU Domain////////////////////



//////////////// Reset for DIV Clock Domain /////////////////////////
  // Reset synchorinizer
  always @(posedge div_clk) begin
      rst_div_sync_r[0]   <= #TCQ  rst_async_riu_div;
      rst_div_sync_r[1]   <= #TCQ  rst_div_sync_r[0];
  end

 //Counter For Reset Stretching  
  always @(posedge div_clk) begin
      if (rst_div_sync_r[1])
          counter_div_rst    <= #TCQ   RST_DIV_SYNC_NUM;
      else if (counter_div_rst != 0) 
          counter_div_rst    <= #TCQ  counter_div_rst - 1'b1 ;
      else 
          counter_div_rst    <= #TCQ  counter_div_rst  ;
  end

  always @(posedge div_clk) begin
      if (counter_div_rst != 0) 
         rst_div_logic <= #TCQ  1'b1 ;
      else 
         rst_div_logic <= #TCQ  1'b0 ;
  end

  always @(posedge div_clk) begin
      rst_div_logic_r[0]   <= #TCQ rst_div_logic;
      rst_div_logic_r[2:1] <= #TCQ rst_div_logic_r[1:0]; 
      rst_div_logic_r1     <= #TCQ rst_div_logic_r[2];
  end


////////////////END of Reset Block for DIV Domain////////////////////

//////////////// Reset for MB /////////////////////////
  // Reset synchorinizer
  always @(posedge riu_clk) begin
      rst_mb_sync_r[0]   <= #TCQ rst_async_mb ;
      rst_mb_sync_r[1]   <= #TCQ rst_mb_sync_r[0];
  end

 //Counter For Reset Stretching  
  always @(posedge riu_clk) begin
      if (rst_mb_sync_r[1])
          counter_mb_rst    <= #TCQ   RST_DIV_SYNC_NUM;
      else if (counter_mb_rst != 0) 
          counter_mb_rst    <= #TCQ  counter_mb_rst - 1'b1 ;
      else 
          counter_mb_rst    <= #TCQ  counter_mb_rst ;
  end

  always @(posedge riu_clk) begin
      if (counter_mb_rst != 0) 
         rst_mb_logic <= #TCQ  1'b1 ;
      else 
         rst_mb_logic <= #TCQ  1'b0 ;
  end
  
  always @(posedge riu_clk) begin
      rst_mb_logic_r[0]   <= #TCQ rst_mb_logic;
      rst_mb_logic_r[2:1] <= #TCQ rst_mb_logic_r[1:0]; 
      rst_mb_logic_r1     <= #TCQ rst_mb_logic_r[2];
  end

////////////////END of Reset Block for MB////////////////////


  assign rstdiv0  = rst_div_logic_r1; // Reset For Fabric Div clk  Domain
  assign rstdiv1  = rst_riu_logic_r1; // Reset For RIU Clock Domain
  assign reset_ub = rst_mb_logic_r1;  // Reset for MicroBlaze 

  always @(posedge div_clk) begin
    if (rst_div_logic_r1)
      pll_gate_cnt <= #TCQ 5'h0;
    else if (pll_gate_cnt < PLL_GATE_CNT_LIMIT)
      pll_gate_cnt <= #TCQ pll_gate_cnt + 5'h1;
  end

  always @ (posedge div_clk)
  begin
    if (rst_div_logic_r1) begin
      pllgate <= #TCQ 1'b0;
    end else if (pll_gate_cnt == PLL_GATE_CNT_LIMIT) begin
      pllgate <= #TCQ 1'b1;
    end
  end

endmodule


