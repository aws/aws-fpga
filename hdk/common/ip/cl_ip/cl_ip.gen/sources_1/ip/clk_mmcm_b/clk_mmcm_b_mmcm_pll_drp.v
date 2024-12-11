
///////////////////////////////////////////////////////////////////////////////
//    
//    Company:          AMD
//    Engineer:         Jim Tatsukawa, Karl Kurbjun and Carl Ribbing
//    Date:             5/30/2013
//    Design Name:      MMCME/PLL DRP
//    Module Name:      mmcm_pll_drp.v
//    Version:          1.04
//    Target Devices:   7/8 Series
//    Tool versions:    2013.3
//    Description:      This calls the DRP register calculation functions and
//                      provides a state machine to perform MMCM/PLL reconfiguration
//                      based on the calulated values stored in a initialized 
//                      ROM.
//
//    Revisions:        1/13/11 Updated ROM[18,41] LOCKED bitmask to 16'HFC00
//                      5/30/13 Adding Fractional support for CLKFBOUT_MULT_F, CLKOUT0_DIVIDE_F
//                      7/29/13 Adding ports for dynamic reconfiguration and updated for MMCM/PLL support
//
// 
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
///////////////////////////////////////////////////////////////////////////////

`timescale 1ps/1ps

module clk_mmcm_b_mmcm_drp
   #(
      //***********************************************************************
      // State 1 Parameters - These are for the first reconfiguration state.
      //***********************************************************************
      
      // These parameters have an effect on the feedback path.  A change on
      // these parameters will effect all of the clock outputs.
      //
      // The paramaters are composed of:
      //    _MULT: This can be from 2 to 64.  It has an effect on the VCO
      //          frequency which consequently, effects all of the clock
      //          outputs.
      //    _PHASE: This is the phase multiplied by 1000. For example if
      //          a phase of 24.567 deg was desired the input value would be
      //          24567.  The range for the phase is from -360000 to 360000. 
      //    _FRAC: This can be from 0 to 875.  This represents the fractional
      //          divide multiplied by 1000. 
      //          M = _MULT + _FRAC / 1000
      //          e.g. M=8.125
      //               _MULT = 8
      //               _FRAC = 125
      //    _FRAC_EN: This indicates fractional divide has been enabled. If 1
      //          then the fractional divide algorithm will be used to calculate
      //          register settings. If 0 then default calculation to be used.
      parameter S1_CLKFBOUT_MULT          = 5,
      parameter S1_CLKFBOUT_PHASE         = 0,
      parameter S1_CLKFBOUT_FRAC          = 125, 
      parameter S1_CLKFBOUT_FRAC_EN       = 1, 
      
      // The bandwidth parameter effects the phase error and the jitter filter
      // capability of the MMCM.  For more information on this parameter see the
      // Device user guide.
      parameter S1_BANDWIDTH              = "LOW",
      
      // The divclk parameter allows th einput clock to be divided before it
      // reaches the phase and frequency comparitor.  This can be set between
      // 1 and 128.
      parameter S1_DIVCLK_DIVIDE          = 1,
      
      // The following parameters describe the configuration that each clock
      // output should have once the reconfiguration for state one has
      // completed.
      //
      // The parameters are composed of:
      //    _DIVIDE: This can be from 1 to 128
      //    _PHASE: This is the phase multiplied by 1000. For example if
      //          a phase of 24.567 deg was desired the input value would be
      //          24567.  The range for the phase is from -360000 to 360000.
      //    _DUTY: This is the duty cycle multiplied by 100,000.  For example if 
      //          a duty cycle of .24567 was desired the input would be
      //          24567.
      
      parameter S1_CLKOUT0_DIVIDE         = 1,
      parameter S1_CLKOUT0_PHASE          = 0,
      parameter S1_CLKOUT0_DUTY           = 50000,
      parameter S1_CLKOUT0_FRAC          = 125, 
      parameter S1_CLKOUT0_FRAC_EN       = 1, 
      
      parameter S1_CLKOUT1_DIVIDE         = 2,
      parameter S1_CLKOUT1_PHASE          = 0,
      parameter S1_CLKOUT1_DUTY           = 50000,
      
      parameter S1_CLKOUT2_DIVIDE         = 4,
      parameter S1_CLKOUT2_PHASE          = 0,
      parameter S1_CLKOUT2_DUTY           = 50000,
      
      parameter S1_CLKOUT3_DIVIDE         = 8,
      parameter S1_CLKOUT3_PHASE          = 0,
      parameter S1_CLKOUT3_DUTY           = 50000,
      
      parameter S1_CLKOUT4_DIVIDE         = 16,
      parameter S1_CLKOUT4_PHASE          = 0,
      parameter S1_CLKOUT4_DUTY           = 50000,
      
      parameter S1_CLKOUT5_DIVIDE         = 8,
      parameter S1_CLKOUT5_PHASE          = 0,
      parameter S1_CLKOUT5_DUTY           = 50000,
      
      parameter S1_CLKOUT6_DIVIDE         = 4,
      parameter S1_CLKOUT6_PHASE          = 0,
      parameter S1_CLKOUT6_DUTY           = 50000
   ) (
      //***********************************************************************
      // State 2 Parameters configured through S2_* ports - These are for the second reconfiguration state.
      //***********************************************************************
      
      // These parameters have an effect on the feedback path.  A change on
      // these parameters will effect all of the clock outputs.
      //
      // The paramaters are composed of:
      //    _MULT: This can be from 2 to 64.  It has an effect on the VCO
      //          frequency which consequently, effects all of the clock
      //          outputs.
      //    _PHASE: This is the phase multiplied by 1000. For example if
      //          a phase of 24.567 deg was desired the input value would be
      //          24567.  The range for the phase is from -360000 to 360000. 
      //    _FRAC: This can be from 0 to 875.  This represents the fractional
      //          divide multiplied by 1000. 
      //          M = _MULT + _FRAC / 1000
      //          e.g. M=8.125
      //               _MULT = 8
      //               _FRAC = 125
      //    _FRAC_EN: This indicates fractional divide has been enabled. If 1
      //          then the fractional divide algorithm will be used to calculate
      //          register settings. If 0 then default calculation to be used.
      
      input [7:0] S2_CLKFBOUT_MULT  ,//        , // 1,
      input [9:0] S2_CLKFBOUT_FRAC  ,//        , // 125, 
      input  S2_CLKFBOUT_FRAC_EN     ,//  , // 1, 
      
      // The bandwidth parameter effects the phase error and the jitter filter
      // capability of the MMCM/PLL.  For more information on this parameter see the
      // Device user guide.
      
      // The divclk parameter allows th einput clock to be divided before it
      // reaches the phase and frequency comparitor.  This can be set between
      // 1 and 128.
      input [7:0] S2_DIVCLK_DIVIDE          , // 1,
      
      // The following parameters describe the configuration that each clock
      // output should have once the reconfiguration for state one has
      // completed.
      //
      // The parameters are composed of:
      //    _DIVIDE: This can be from 1 to 128
      //    _PHASE: This is the phase multiplied by 1000. For example if
      //          a phase of 24.567 deg was desired the input value would be
      //          24567.  The range for the phase is from -360000 to 360000
      //    _DUTY: This is the duty cycle multiplied by 100,000.  For example if 
      //          a duty cycle of .24567 was desired the input would be
      //          24567.
      
      input [7:0] S2_CLKOUT0_DIVIDE         , 
      input [9:0] S2_CLKOUT0_FRAC          , 
      input        S2_CLKOUT0_FRAC_EN       ,
      
      input [7:0] S2_CLKOUT1_DIVIDE         ,
      
      input [7:0] S2_CLKOUT2_DIVIDE         ,
      
      input [7:0] S2_CLKOUT3_DIVIDE         ,
      
      input [7:0] S2_CLKOUT4_DIVIDE         ,
      
      input [7:0] S2_CLKOUT5_DIVIDE         ,
      
      input [7:0] S2_CLKOUT6_DIVIDE         ,
      input             LOAD,
      // These signals are controlled by user logic interface and are covered
      // in more detail within the XAPP.
      input             SADDR,
      input             SEN,
      input             SCLK,
      input             RST,
      output reg        SRDY,
      
      // These signals are to be connected to the MMCM/PLL_ADV by port name.
      // Their use matches the MMCM/PLL port description in the Device User Guide.
      input      [15:0] DO,
      input             DRDY,
      input             LOCKED,
      output reg        DWE,
      output reg        DEN,
      output reg [6:0]  DADDR,
      output reg [15:0] DI,
      output            DCLK,
      output reg        RST_MMCM_PLL
   );

   // 100 ps delay for behavioral simulations
   localparam  TCQ = 100;
   localparam  S2_BANDWIDTH = "LOW";
  
   // Make sure the memory is implemented as distributed
   (* ram_style = "distributed" *)
   reg [38:0]  ram [63:0];  // 39 bit word 64 words deep
   reg [5:0]   ram_addr;
   reg [38:0]  ram_do;
   
   reg         next_srdy;

   reg [5:0]   next_ram_addr;
   reg [6:0]   next_daddr;
   reg         next_dwe;
   reg         next_den;
   reg         next_rst_mmcm_pll;
   reg [15:0]  next_di;
   
   // Integer used to initialize remainder of unused ROM
   integer     ii;
   
   // Pass SCLK to DCLK for the MMCM/PLL
   assign DCLK = SCLK;
   // Include the MMCM/PLLreconfiguration functions.  This contains the constant
   // functions that are used in the calculations below.  This file is 
   // required.
 
   `include "mmcm_pll_drp_func_us_plus_mmcm.vh"
   
   //**************************************************************************
   // State 1 Calculations
   //**************************************************************************
   // Please see header for infor
   localparam [37:0] S1_CLKFBOUT       =
      mmcm_pll_count_calc(S1_CLKFBOUT_MULT, S1_CLKFBOUT_PHASE, 50000);

   localparam [37:0] S1_CLKFBOUT_FRAC_CALC       =
      mmcm_frac_count_calc(S1_CLKFBOUT_MULT, S1_CLKFBOUT_PHASE, 50000, S1_CLKFBOUT_FRAC);

   localparam [9:0]  S1_DIGITAL_FILT   = 
      mmcm_pll_filter_lookup(S1_CLKFBOUT_MULT, S1_BANDWIDTH);

   localparam [39:0] S1_LOCK           =
      mmcm_pll_lock_lookup(S1_CLKFBOUT_MULT);
      
   localparam [37:0] S1_DIVCLK         = 
      mmcm_pll_count_calc(S1_DIVCLK_DIVIDE, 0, 50000); 
      
   localparam [37:0] S1_CLKOUT0        =
      mmcm_pll_count_calc(S1_CLKOUT0_DIVIDE, S1_CLKOUT0_PHASE, S1_CLKOUT0_DUTY); 
         
   localparam [37:0] S1_CLKOUT0_FRAC_CALC        =
      mmcm_frac_count_calc(S1_CLKOUT0_DIVIDE, S1_CLKOUT0_PHASE, 50000, S1_CLKOUT0_FRAC);

   localparam [37:0] S1_CLKOUT1        = 
      mmcm_pll_count_calc(S1_CLKOUT1_DIVIDE, S1_CLKOUT1_PHASE, S1_CLKOUT1_DUTY); 
         
   localparam [37:0] S1_CLKOUT2        = 
      mmcm_pll_count_calc(S1_CLKOUT2_DIVIDE, S1_CLKOUT2_PHASE, S1_CLKOUT2_DUTY); 
         
   localparam [37:0] S1_CLKOUT3        = 
      mmcm_pll_count_calc(S1_CLKOUT3_DIVIDE, S1_CLKOUT3_PHASE, S1_CLKOUT3_DUTY); 
         
   localparam [37:0] S1_CLKOUT4        = 
      mmcm_pll_count_calc(S1_CLKOUT4_DIVIDE, S1_CLKOUT4_PHASE, S1_CLKOUT4_DUTY); 
         
   localparam [37:0] S1_CLKOUT5        = 
      mmcm_pll_count_calc(S1_CLKOUT5_DIVIDE, S1_CLKOUT5_PHASE, S1_CLKOUT5_DUTY); 
         
   localparam [37:0] S1_CLKOUT6        = 
      mmcm_pll_count_calc(S1_CLKOUT6_DIVIDE, S1_CLKOUT6_PHASE, S1_CLKOUT6_DUTY); 
   
   //**************************************************************************
   // State 2 Calculations
   //**************************************************************************
   wire [37:0] S2_CLKFBOUT       = 
      mmcm_pll_count_calc(S2_CLKFBOUT_MULT, S1_CLKFBOUT_PHASE, 50000);
      
   wire [37:0] S2_CLKFBOUT_FRAC_CALC       =
      mmcm_frac_count_calc(S2_CLKFBOUT_MULT, S1_CLKFBOUT_PHASE, 50000, S2_CLKFBOUT_FRAC);

   wire [9:0] S2_DIGITAL_FILT    = 
      mmcm_pll_filter_lookup(S2_CLKFBOUT_MULT, S2_BANDWIDTH);

   wire [39:0] S2_LOCK           = 
      mmcm_pll_lock_lookup(S2_CLKFBOUT_MULT);
   
   wire [37:0] S2_DIVCLK         = 
      mmcm_pll_count_calc(S2_DIVCLK_DIVIDE, 0, 50000); 
   
   wire [37:0] S2_CLKOUT0        = 
      mmcm_pll_count_calc(S2_CLKOUT0_DIVIDE, S1_CLKOUT0_PHASE, S1_CLKOUT0_DUTY);
         
   wire [37:0] S2_CLKOUT0_FRAC_CALC        =
      mmcm_frac_count_calc(S2_CLKOUT0_DIVIDE, S1_CLKOUT0_PHASE, 50000, S2_CLKOUT0_FRAC);
         
   wire [37:0] S2_CLKOUT1        = 
      mmcm_pll_count_calc(S2_CLKOUT1_DIVIDE, S1_CLKOUT1_PHASE, S1_CLKOUT1_DUTY);
         
   wire [37:0] S2_CLKOUT2        = 
      mmcm_pll_count_calc(S2_CLKOUT2_DIVIDE, S1_CLKOUT2_PHASE, S1_CLKOUT2_DUTY);
         
   wire [37:0] S2_CLKOUT3        = 
      mmcm_pll_count_calc(S2_CLKOUT3_DIVIDE, S1_CLKOUT3_PHASE, S1_CLKOUT3_DUTY);
         
   wire [37:0] S2_CLKOUT4        = 
      mmcm_pll_count_calc(S2_CLKOUT4_DIVIDE, S1_CLKOUT4_PHASE, S1_CLKOUT4_DUTY);
         
   wire [37:0] S2_CLKOUT5        = 
      mmcm_pll_count_calc(S2_CLKOUT5_DIVIDE, S1_CLKOUT5_PHASE, S1_CLKOUT5_DUTY);
         
   wire [37:0] S2_CLKOUT6        = 
      mmcm_pll_count_calc(S2_CLKOUT6_DIVIDE, S1_CLKOUT6_PHASE, S1_CLKOUT6_DUTY);
   initial begin
      // ram entries contain (in order) the address, a bitmask, and a bitset
      //***********************************************************************
      // State 1 Initialization
      //***********************************************************************
      
      // Store the power bits
      ram[0] <= {7'h27, 16'h0000, 16'hFFFF};
      
      // Store CLKOUT0 divide and phase
      ram[1]  <= (S1_CLKOUT0_FRAC_EN == 0) ?
						{7'h09, 16'h8000, S1_CLKOUT0[31:16]}:
						{7'h09, 16'h8000, S1_CLKOUT0_FRAC_CALC[31:16]};
      ram[2]  <= (S1_CLKOUT0_FRAC_EN == 0) ?
						{7'h08, 16'h1000, S1_CLKOUT0[15:0]}:
						{7'h08, 16'h1000, S1_CLKOUT0_FRAC_CALC[15:0]};

      // Store CLKOUT1 divide and phase
      ram[3]  <= {7'h0A, 16'h1000, S1_CLKOUT1[15:0]};
      ram[4]  <= {7'h0B, 16'hFC00, S1_CLKOUT1[31:16]};
      
      // Store CLKOUT2 divide and phase
      ram[5]  <= {7'h0C, 16'h1000, S1_CLKOUT2[15:0]};
      ram[6]  <= {7'h0D, 16'hFC00, S1_CLKOUT2[31:16]};
      
      // Store CLKOUT3 divide and phase
      ram[7]  <= {7'h0E, 16'h1000, S1_CLKOUT3[15:0]};
      ram[8]  <= {7'h0F, 16'hFC00, S1_CLKOUT3[31:16]};
      
      // Store CLKOUT4 divide and phase
      ram[9]  <= {7'h10, 16'h1000, S1_CLKOUT4[15:0]};
      ram[10]  <= {7'h11, 16'hFC00, S1_CLKOUT4[31:16]};
      
      // Store CLKOUT5 divide and phase
      ram[11] <= {7'h06, 16'h1000, S1_CLKOUT5[15:0]};
      ram[12] <= (S1_CLKOUT0_FRAC_EN == 0) ?
                {7'h07, 16'h0000, S1_CLKOUT5[31:16]}:
                {7'h07, 16'h0400, S1_CLKOUT0_FRAC_CALC[35:32], 2'b00, S1_CLKOUT5[25:16]}; 
      
      // Store CLKOUT6 divide and phase
      ram[13] <= {7'h12, 16'h1000, S1_CLKOUT6[15:0]};
      ram[14] <= (S1_CLKFBOUT_FRAC_EN == 0) ?
                {7'h13, 16'h0000, S1_CLKOUT6[31:16]}:
                {7'h13, 16'h0400, S1_CLKFBOUT_FRAC_CALC[35:32], 2'b00, S1_CLKOUT6[25:16]};
      
      // Store the input divider
      ram[15] <= {7'h16, 16'hC000, {2'h0, S1_DIVCLK[23:22], S1_DIVCLK[11:0]} };
      
      // Store the feedback divide and phase
      ram[16] <= (S1_CLKFBOUT_FRAC_EN == 0) ?
                {7'h15, 16'h8000, S1_CLKFBOUT[31:16]}:
                {7'h15, 16'h8000, S1_CLKFBOUT_FRAC_CALC[31:16]};
      ram[17] <= (S1_CLKFBOUT_FRAC_EN == 0) ?
                {7'h14, 16'h1000, S1_CLKFBOUT[15:0]}:
                {7'h14, 16'h1000, S1_CLKFBOUT_FRAC_CALC[15:0]};
      

      // Store the lock settings
      ram[18] <= {7'h18, 16'hFC00, {6'h00, S1_LOCK[29:20]} };
      ram[19] <= {7'h19, 16'h8000, {1'b0 , S1_LOCK[34:30], S1_LOCK[9:0]} };
      ram[20] <= {7'h1A, 16'h8000, {1'b0 , S1_LOCK[39:35], S1_LOCK[19:10]} };
      
      // Store the filter settings
      ram[21] <= {7'h4E, 16'h66FF, 
                S1_DIGITAL_FILT[9], 2'h0, S1_DIGITAL_FILT[8:7], 2'h0, 
                S1_DIGITAL_FILT[6], 8'h00 };
      ram[22] <= {7'h4F, 16'h666F, 
                S1_DIGITAL_FILT[5], 2'h0, S1_DIGITAL_FILT[4:3], 2'h0,
                S1_DIGITAL_FILT[2:1], 2'h0, S1_DIGITAL_FILT[0], 4'h0 };

      // Initialize the rest of the ROM
      ram[46] <= {7'h27,32'h0000_0000};
      for(ii = 23; ii < 45; ii = ii +1) begin
         ram[ii] <= 0;
      end
      for(ii = 47; ii < 64; ii = ii +1) begin
         ram[ii] <= 0;
      end
     end
      //***********************************************************************
      // State 2 Initialization
      //***********************************************************************
      
   always @(posedge SCLK) begin
   if (LOAD) begin 
      // Store the power bits
      ram[23] <= {7'h27, 16'h0000, 16'hFFFF};
      // Store CLKOUT0 divide and phase
      ram[24] <= (S2_CLKOUT0_FRAC_EN == 0) ?
                {7'h09, 16'h8000, S2_CLKOUT0[31:16]}:
                {7'h09, 16'h8000, S2_CLKOUT0_FRAC_CALC[31:16]};
      ram[25] <= (S2_CLKOUT0_FRAC_EN == 0) ?
                {7'h08, 16'h1000, S2_CLKOUT0[15:0]}:
                {7'h08, 16'h1000, S2_CLKOUT0_FRAC_CALC[15:0]};
      
      // Store CLKOUT1 divide and phase
      ram[26] <= {7'h0A, 16'h1000, S2_CLKOUT1[15:0]};
      ram[27] <= {7'h0B, 16'hFC00, S2_CLKOUT1[31:16]};
     
      // Store CLKOUT2 divide and phase
      ram[28] <= {7'h0C, 16'h1000, S2_CLKOUT2[15:0]};
      ram[29] <= {7'h0D, 16'hFC00, S2_CLKOUT2[31:16]};
      
      // Store CLKOUT3 divide and phase
      ram[30] <= {7'h0E, 16'h1000, S2_CLKOUT3[15:0]};
      ram[31] <= {7'h0F, 16'hFC00, S2_CLKOUT3[31:16]};
      
      // Store CLKOUT4 divide and phase
      ram[32] <= {7'h10, 16'h1000, S2_CLKOUT4[15:0]};
      ram[33] <= {7'h11, 16'hFC00, S2_CLKOUT4[31:16]};
      
      // Store CLKOUT5 divide and phase
      ram[34] <= {7'h06, 16'h1000, S2_CLKOUT5[15:0]};
      ram[35] <= (S2_CLKOUT0_FRAC_EN == 0) ?
                {7'h07, 16'h0000, S2_CLKOUT5[31:16]}:
                {7'h07, 16'h0400, S2_CLKOUT0_FRAC_CALC[35:32], 2'b00, S2_CLKOUT5[25:16]}; 
      
      // Store CLKOUT6 divide and phase
      ram[36] <= {7'h12, 16'h1000, S2_CLKOUT6[15:0]};
      ram[37] <= (S2_CLKFBOUT_FRAC_EN == 0) ?
                {7'h13, 16'h0000, S2_CLKOUT6[31:16]}:
                {7'h13, 16'h0400, S2_CLKFBOUT_FRAC_CALC[35:32], 2'b00, S2_CLKOUT6[25:16]};
      
      // Store the input divider
      ram[38] <= {7'h16, 16'hC000, {2'h0, S2_DIVCLK[23:22], S2_DIVCLK[11:0]} };
      
      // Store the feedback divide and phase
      ram[39] <= (S2_CLKFBOUT_FRAC_EN == 0) ?
                {7'h15, 16'h8000, S2_CLKFBOUT[31:16]}:
                {7'h15, 16'h8000, S2_CLKFBOUT_FRAC_CALC[31:16]};
      ram[40] <= (S2_CLKFBOUT_FRAC_EN == 0) ?
                {7'h14, 16'h1000, S2_CLKFBOUT[15:0]}:
                {7'h14, 16'h1000, S2_CLKFBOUT_FRAC_CALC[15:0]};
 

      // Store the lock settings
      ram[41] <= {7'h18, 16'hFC00, {6'h00, S2_LOCK[29:20]} };
      ram[42] <= {7'h19, 16'h8000, {1'b0 , S2_LOCK[34:30], S2_LOCK[9:0]} };
      ram[43] <= {7'h1A, 16'h8000, {1'b0 , S2_LOCK[39:35], S2_LOCK[19:10]} };
      
      // Store the filter settings
      ram[44] <= {7'h4E, 16'h66FF, 
                S2_DIGITAL_FILT[9], 2'h0, S2_DIGITAL_FILT[8:7], 2'h0, 
                S2_DIGITAL_FILT[6], 8'h00 };
      ram[45] <= {7'h4F, 16'h666F, 
                S2_DIGITAL_FILT[5], 2'h0, S2_DIGITAL_FILT[4:3], 2'h0,
                S2_DIGITAL_FILT[2:1], 2'h0, S2_DIGITAL_FILT[0], 4'h0 };
      ram[46] <= {7'h27,32'h0000_0000};
      for(ii = 47; ii < 64; ii = ii +1) begin

         ram[ii] <= 0;
   end
  end
   end

   // Output the initialized ram value based on ram_addr each clock cycle
   always @(posedge SCLK) begin
      ram_do<= #TCQ ram[ram_addr];
   end
   
   //**************************************************************************
   // Everything below is associated whith the state machine that is used to
   // Read/Modify/Write to the MMCM/PLL.
   //**************************************************************************
   
   // State Definitions
   localparam RESTART      = 4'h1;
   localparam WAIT_LOCK    = 4'h2;
   localparam WAIT_SEN     = 4'h3;
   localparam ADDRESS      = 4'h4;
   localparam WAIT_A_DRDY  = 4'h5;
   localparam BITMASK      = 4'h6;
   localparam BITSET       = 4'h7;
   localparam WRITE        = 4'h8;
   localparam WAIT_DRDY    = 4'h9;
   
   // State sync
(* dont_touch = "true" *)

   reg [3:0]  current_state   = RESTART;
   reg [3:0]  next_state      = RESTART;
   
   // These variables are used to keep track of the number of iterations that 
   //    each state takes to reconfigure.
   // STATE_COUNT_CONST is used to reset the counters and should match the
   //    number of registers necessary to reconfigure each state.
   localparam STATE_COUNT_CONST  = 23;
   reg [4:0] state_count         = STATE_COUNT_CONST; 
   reg [4:0] next_state_count    = STATE_COUNT_CONST;
   
   // This block assigns the next register value from the state machine below
   always @(posedge SCLK) begin
      DADDR       <= #TCQ next_daddr;
      DWE         <= #TCQ next_dwe;
      DEN         <= #TCQ next_den;
      RST_MMCM_PLL    <= #TCQ next_rst_mmcm_pll;
      DI          <= #TCQ next_di;
      
      SRDY        <= #TCQ next_srdy;
      
      ram_addr    <= #TCQ next_ram_addr;
      state_count <= #TCQ next_state_count;
   end
   
   // This block assigns the next state, reset is syncronous.
   always @(posedge SCLK) begin
      if(RST) begin
         current_state <= #TCQ RESTART;
      end else begin
         current_state <= #TCQ next_state;
      end
   end
   
   always @* begin
      // Setup the default values
      next_srdy         = 1'b0;
      next_daddr        = DADDR;
      next_dwe          = 1'b0;
      next_den          = 1'b0;
      next_rst_mmcm_pll     = RST_MMCM_PLL;
      next_di           = DI;
      next_ram_addr     = ram_addr;
      next_state_count  = state_count;
   
      case (current_state)
         // If RST is asserted reset the machine
         RESTART: begin
            next_daddr     = 7'h00;
            next_di        = 16'h0000;
            next_ram_addr  = 6'h00;
            next_rst_mmcm_pll  = 1'b1;
            next_state     = WAIT_LOCK;
         end
         
         // Waits for the MMCM/PLL to assert LOCKED - once it does asserts SRDY
         WAIT_LOCK: begin
            // Make sure reset is de-asserted
            next_rst_mmcm_pll   = 1'b0;
            // Reset the number of registers left to write for the next 
            // reconfiguration event.
            next_state_count = STATE_COUNT_CONST ;
            
            if(LOCKED) begin
               // MMCM/PLL is locked, go on to wait for the SEN signal
               next_state  = WAIT_SEN;
               // Assert SRDY to indicate that the reconfiguration module is
               // ready
               next_srdy   = 1'b1;
            end else begin
               // Keep waiting, locked has not asserted yet
               next_state  = WAIT_LOCK;
            end
         end
         
         // Wait for the next SEN pulse and set the ROM addr appropriately 
         //    based on SADDR
         WAIT_SEN: begin
            if (SEN) begin
               // SEN was asserted
               if (!SADDR) begin
                  // Reconfigure with the first (0) state
                  next_ram_addr = 8'h00;
               end else begin
                  // Reconfigure with the second (1) state
                  next_ram_addr = STATE_COUNT_CONST;
               end
               // Go on to address the MMCM/PLL
               next_state = ADDRESS;
            end else begin
               // Keep waiting for SEN to be asserted
               next_state = WAIT_SEN;
            end
         end
         
         // Set the address on the MMCM/PLL and assert DEN to read the value
         ADDRESS: begin
            // Reset the DCM through the reconfiguration
            next_rst_mmcm_pll  = 1'b1;
            // Enable a read from the MMCM/PLL and set the MMCM/PLL address
            next_den       = 1'b1;
            next_daddr     = ram_do[38:32];
            
            // Wait for the data to be ready
            next_state     = WAIT_A_DRDY;
         end
         
         // Wait for DRDY to assert after addressing the MMCM/PLL
         WAIT_A_DRDY: begin
            if (DRDY) begin
               // Data is ready, mask out the bits to save
               next_state = BITMASK;
            end else begin
               // Keep waiting till data is ready
               next_state = WAIT_A_DRDY;
            end
         end
         
         // Zero out the bits that are not set in the mask stored in ram
         BITMASK: begin
            // Do the mask
            next_di     = ram_do[31:16] & DO;
            // Go on to set the bits
            next_state  = BITSET;
         end
         
         // After the input is masked, OR the bits with calculated value in ram
         BITSET: begin
            // Set the bits that need to be assigned
            next_di           = ram_do[15:0] | DI;
            // Set the next address to read from ROM
            next_ram_addr     = ram_addr + 1'b1;
            // Go on to write the data to the MMCM/PLL
            next_state        = WRITE;
         end
         
         // DI is setup so assert DWE, DEN, and RST_MMCM_PLL.  Subtract one from the
         //    state count and go to wait for DRDY.
         WRITE: begin
            // Set WE and EN on MMCM/PLL
            next_dwe          = 1'b1;
            next_den          = 1'b1;
            
            // Decrement the number of registers left to write
            next_state_count  = state_count - 1'b1;
            // Wait for the write to complete
            next_state        = WAIT_DRDY;
         end
         
         // Wait for DRDY to assert from the MMCM/PLL.  If the state count is not 0
         //    jump to ADDRESS (continue reconfiguration).  If state count is
         //    0 wait for lock.
         WAIT_DRDY: begin
            if(DRDY) begin
               // Write is complete
               if(state_count > 0) begin
                  // If there are more registers to write keep going
                  next_state  = ADDRESS;
               end else begin
                  // There are no more registers to write so wait for the MMCM/PLL
                  // to lock
                  next_state  = WAIT_LOCK;
               end
            end else begin
               // Keep waiting for write to complete
               next_state     = WAIT_DRDY;
            end
         end
         
         // If in an unknown state reset the machine
         default: begin
            next_state = RESTART;
         end
      endcase
   end
endmodule
