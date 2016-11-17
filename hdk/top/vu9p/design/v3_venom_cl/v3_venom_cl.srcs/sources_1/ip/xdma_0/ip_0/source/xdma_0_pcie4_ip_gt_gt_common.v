//-----------------------------------------------------------------------------
//
// (c) Copyright 2012-2012 Xilinx, Inc. All rights reserved.
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
//
//-----------------------------------------------------------------------------
//
// Project    : UltraScale+ FPGA PCI Express v4.0 Integrated Block
// File       : xdma_0_pcie4_ip_gt_gt_common.v
// Version    : 1.1 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
//  Design :  PHY Wrapper
//  Module :  GT Common
//--------------------------------------------------------------------------------------------------

`timescale 1ps / 1ps

//--------------------------------------------------------------------------------------------------
//  GT Common Module
//--------------------------------------------------------------------------------------------------
(* DowngradeIPIdentifiedWarnings = "yes" *)
module xdma_0_pcie4_ip_gt_gt_common #
(
    parameter         PHY_SIM_EN      = "FALSE",
    parameter         PHY_GT_XCVR     = "GTY",
    parameter integer PHY_MAX_SPEED   = 4,
    parameter integer PHY_REFCLK_FREQ = 0    
)
(    
    //----------------------------------------------------------------------------------------------
    //  Clock Ports
    //----------------------------------------------------------------------------------------------
    input                               GTCOM_REFCLK,
    
    output                              GTCOM_QPLL0OUTCLK,
    output                              GTCOM_QPLL0OUTREFCLK,
    output                              GTCOM_QPLL0LOCK,
    
    output                              GTCOM_QPLL1OUTCLK,
    output                              GTCOM_QPLL1OUTREFCLK,
    output                              GTCOM_QPLL1LOCK,
    
    //----------------------------------------------------------------------------------------------
    //  Reset Ports
    //----------------------------------------------------------------------------------------------
    input                               GTCOM_QPLL0PD,
    input                               GTCOM_QPLL0RESET, 
 
    input                               GTCOM_QPLL1PD,
    input                               GTCOM_QPLL1RESET,
            
    //----------------------------------------------------------------------------------------------
    //  PCIe Ports
    //----------------------------------------------------------------------------------------------
    input       [ 2:0]                  GTCOM_QPLLRATE,
    
    //----------------------------------------------------------------------------------------------
    //  DRP Ports
    //----------------------------------------------------------------------------------------------
    input                               GTCOM_DRPCLK,                                        
    input       [15:0]                  GTCOM_DRPADDR,                                       
    input                               GTCOM_DRPEN,                                             
    input                               GTCOM_DRPWE,     
    input       [15:0]                  GTCOM_DRPDI,                                      
                                                                
    output                              GTCOM_DRPRDY,    
    output      [15:0]                  GTCOM_DRPDO
);                                                      
    
    //----------------------------------------------------------------------------------------------
    //  QPLL[0/1]_FBDIV - QPLL Feedback (N) Divider (Gen1/Gen2)
    //----------------------------------------------------------------------------------------------
    localparam [ 7:0] QPLL_FBDIV = (PHY_REFCLK_FREQ == 2) ? 8'd40 : 
                                   (PHY_REFCLK_FREQ == 1) ? 8'd80 : 8'd100;
    
    
    
    //----------------------------------------------------------------------------------------------
    //  QPLL[1/0]_FBDIV_G34 - QPLL Feedback (N) Divider (Gen3/Gen4)
    //----------------------------------------------------------------------------------------------    
    localparam [ 7:0] QPLL_FBDIV_G3 = (PHY_REFCLK_FREQ == 2) ? 8'd32  : 
                                      (PHY_REFCLK_FREQ == 1) ? 8'd64  : 8'd80;
    
    localparam [ 7:0] QPLL_FBDIV_G4 = (PHY_REFCLK_FREQ == 2) ? 8'd64  : 
                                      (PHY_REFCLK_FREQ == 1) ? 8'd128 : 8'd160;
    
    localparam [ 7:0] QPLL_FBDIV_G34 = (PHY_MAX_SPEED == 4) ? QPLL_FBDIV_G4 : QPLL_FBDIV_G3;



    //----------------------------------------------------------------------------------------------
    //  QPLL[1/0]_CFG2_G3 - QPLL Configuration (Gen3 and Gen4)
    //    [6] : 1'b0 = Select upper band VCO
    //        : 1'b1 = Select lower band VCO
    //----------------------------------------------------------------------------------------------  
    localparam [15:0] QPLL_CFG2_G3 = (PHY_MAX_SPEED == 4) ? 16'h0000 : 16'h0040;



//--------------------------------------------------------------------------------------------------
//  GTY Common
//--------------------------------------------------------------------------------------------------    

generate
  if (PHY_GT_XCVR == "GTY" || PHY_GT_XCVR == "GTY64") begin: GTY_CHANNEL
//--------------------------------------------------------------------------------------------------
//  GTY Common
//--------------------------------------------------------------------------------------------------
GTYE4_COMMON #
(   
    //---------------------------------------------------------------------------------------------- 
    //  Simulation Attributes
    //----------------------------------------------------------------------------------------------      
    .SIM_MODE                           ("FAST"),                                                                                                                                                                                      
    .SIM_RESET_SPEEDUP                  ("TRUE"),                                                                                              
    .SIM_VERSION                        (1),                                                                          

    //----------------------------------------------------------------------------------------------               
    //  Clock Attributes
    //----------------------------------------------------------------------------------------------    
    .RXRECCLKOUT0_SEL                   ( 2'b00),
    .RXRECCLKOUT1_SEL                   ( 2'b00),                    

    //----------------------------------------------------------------------------------------------
    //  QPLL0 Attributes 
    //----------------------------------------------------------------------------------------------    
    .AEN_QPLL0_FBDIV                    (1'b1),                                 
    .QPLL0CLKOUT_RATE                   ("HALF"),                              
    .QPLL0_CFG0                         (16'h001D),                             
    .QPLL0_CFG1                         (16'h0000),                             
    .QPLL0_CFG1_G3                      (16'h0000),                             
    .QPLL0_CFG2                         (16'h0040),                             
    .QPLL0_CFG2_G3                      (QPLL_CFG2_G3),                        
    .QPLL0_CFG3                         (16'h0120),                  
    .QPLL0_CFG4                         (16'h0000),
    .QPLL0_CP                           (10'b0000011111),                       // Optimized for PCIe PLL compliance
    .QPLL0_CP_G3                        (10'b0000011111),                       // Optimized for PCIe PLL compliance
    .QPLL0_FBDIV                        (QPLL_FBDIV),
    .QPLL0_FBDIV_G3                     (QPLL_FBDIV_G34),
    .QPLL0_INIT_CFG0                    (16'b0000000000000000),
    .QPLL0_INIT_CFG1                    ( 8'b00000000),
    .QPLL0_LOCK_CFG                     (16'h05FC),                             // [10] : 1'b1 = Auto VCO
    .QPLL0_LOCK_CFG_G3                  (16'h05FC),                             // [10] : 1'b1 = Auto VCO
    .QPLL0_LPF                          (10'b0000010101),                       // Optimized for PCIe PLL compliance
    .QPLL0_LPF_G3                       (10'b0000010101),                       // Optimized for PCIe PLL compliance
    .QPLL0_PCI_EN                       ( 1'b1),                                
    .QPLL0_RATE_SW_USE_DRP              ( 1'b0),                                // Advance PCIe feature
    .QPLL0_REFCLK_DIV                   (1),
    .QPLL0_SDM_CFG0                     (16'b0000000011000000),                
    .QPLL0_SDM_CFG1                     (16'b0000000000000000),
    .QPLL0_SDM_CFG2                     (16'b0000000000000000),
                     
    //---------------------------------------------------------------------------------------------- 
    //  QPLL1 Attributes               
    //----------------------------------------------------------------------------------------------    
    .AEN_QPLL1_FBDIV                    (1'b1),                                 
    .QPLL1CLKOUT_RATE                   ("HALF"),                              
    .QPLL1_CFG0                         (16'h001D),                             
    .QPLL1_CFG1                         (16'h0000),                             
    .QPLL1_CFG1_G3                      (16'h0000),                             
    .QPLL1_CFG2                         (16'h0040),                             
    .QPLL1_CFG2_G3                      (QPLL_CFG2_G3),                         
    .QPLL1_CFG3                         (16'h0120),                  
    .QPLL1_CFG4                         (16'h0000),
    .QPLL1_CP                           (10'b0000011111),                       // Optimized for PCIe PLL compliance
    .QPLL1_CP_G3                        (10'b0000011111),                       // Optimized for PCIe PLL compliance
    .QPLL1_FBDIV                        (QPLL_FBDIV),
    .QPLL1_FBDIV_G3                     (QPLL_FBDIV_G34),
    .QPLL1_INIT_CFG0                    (16'b0000000000000000),
    .QPLL1_INIT_CFG1                    ( 8'b00000000),
    .QPLL1_LOCK_CFG                     (16'h05FC),                             // [10] : 1'b1 = Auto VCO
    .QPLL1_LOCK_CFG_G3                  (16'h05FC),                             // [10] : 1'b1 = Auto VCO
    .QPLL1_LPF                          (10'b0000010101),                       // Optimized for PCIe PLL compliance
    .QPLL1_LPF_G3                       (10'b0000010101),                       // Optimized for PCIe PLL compliance
    .QPLL1_PCI_EN                       ( 1'b1),                               
    .QPLL1_RATE_SW_USE_DRP              ( 1'b0),                                // Advance PCIe feature
    .QPLL1_REFCLK_DIV                   (1),
    .QPLL1_SDM_CFG0                     (16'b0000000011000000),                 
    .QPLL1_SDM_CFG1                     (16'b0000000000000000),
    .QPLL1_SDM_CFG2                     (16'b0000000000000000),
 
    //----------------------------------------------------------------------------------------------
    //  PPF Attributes                                                         
    //----------------------------------------------------------------------------------------------      
    .PPF0_CFG                           (16'h0FFF),                            
    .PPF1_CFG                           (16'h0FFF),                           
    
    //----------------------------------------------------------------------------------------------
    //  Bias Attributes                                                          
    //----------------------------------------------------------------------------------------------
    .BIAS_CFG0                          (16'b0000000000000000),
    .BIAS_CFG1                          (16'b0000000000000000),
    .BIAS_CFG2                          (16'b0011000000000000),                 // Optimized for PCIe PLL compliance
    .BIAS_CFG3                          (16'b0000000001000000),                 
    .BIAS_CFG4                          (16'b0000000000000000),    
    .BIAS_CFG_RSVD                      (10'b0000000000),  
       
    //---------------------------------------------------------------------------------------------- 
    //  SDM0 Attributes                                                          
    //----------------------------------------------------------------------------------------------
    .A_SDM0TOGGLE                       ( 1'b0),
    .AEN_SDM0TOGGLE                     ( 1'b0),
    .SDM0INITSEED0_0                    (16'b0000000000000000),
    .SDM0INITSEED0_1                    ( 9'b000000000),
    
    //---------------------------------------------------------------------------------------------- 
    //  SDM1 Attributes                                                          
    //----------------------------------------------------------------------------------------------     
    .A_SDM1DATA_HIGH                    ( 9'b000000000),
    .A_SDM1DATA_LOW                     (16'b0000000000000000),
    .A_SDM1TOGGLE                       ( 1'b0),
    .AEN_SDM1TOGGLE                     ( 1'b0),
    .SDM1INITSEED0_0                    (16'b0000000000000000),
    .SDM1INITSEED0_1                    ( 9'b000000000),     
          
    //----------------------------------------------------------------------------------------------
    //  Reserved & MISC Attributes                                                         
    //----------------------------------------------------------------------------------------------            
    .COMMON_CFG0                        (16'b0000000000000000),
    .COMMON_CFG1                        (16'b0000000000000000),
    .POR_CFG                            (16'b0000000000001011),                 // CHECK      
    .RSVD_ATTR0                         (16'b0000000000000001),                 // CHECK
    .RSVD_ATTR1                         (16'b0000000000000000),    
    .RSVD_ATTR2                         (16'b0000000000000001),                 // CHECK                
    .RSVD_ATTR3                         (16'b0000000000000000),
    .SARC_ENB                           ( 1'b0),
    .SARC_SEL                           ( 1'b0),

    //----------------------------------------------------------------------------------------------
    //  MicroBlaze Attributes                                                         
    //----------------------------------------------------------------------------------------------
    .UB_CFG0                            (16'h0),
    .UB_CFG1                            (16'h0),
    .UB_CFG2                            (16'h0),
    .UB_CFG3                            (16'h0),
    .UB_CFG4                            (16'h0),
    .UB_CFG5                            (16'h0),
    .UB_CFG6                            (16'h0)
)
gtye4_common_i 
(       
    //----------------------------------------------------------------------------------------------
    //  QPLL0 Clock Ports
    //----------------------------------------------------------------------------------------------
    .GTGREFCLK0                         ( 1'd0), 
    .GTREFCLK00                         (GTCOM_REFCLK),                         
    .GTREFCLK10                         ( 1'd0),
    .GTNORTHREFCLK00                    ( 1'd0),
    .GTNORTHREFCLK10                    ( 1'd0),
    .GTSOUTHREFCLK00                    ( 1'd0),
    .GTSOUTHREFCLK10                    ( 1'd0),
   
    .REFCLKOUTMONITOR0                  (),
    .RXRECCLK0SEL                       (),
    
    //----------------------------------------------------------------------------------------------
    //  QPLL1 Clock Ports
    //----------------------------------------------------------------------------------------------
    .GTGREFCLK1                         ( 1'd0),
    .GTREFCLK01                         (GTCOM_REFCLK),
    .GTREFCLK11                         ( 1'd0),
    .GTNORTHREFCLK01                    ( 1'd0),    
    .GTNORTHREFCLK11                    ( 1'd0),
    .GTSOUTHREFCLK01                    ( 1'd0),
    .GTSOUTHREFCLK11                    ( 1'd0),        
        
    .REFCLKOUTMONITOR1                  (),  
    .RXRECCLK1SEL	                      (), 
        
    //----------------------------------------------------------------------------------------------
    //  QPLL0 Ports
    //----------------------------------------------------------------------------------------------
    .QPLL0CLKRSVD0                      ( 1'd0),
    .QPLL0CLKRSVD1                      ( 1'd0),                              
    .QPLL0FBDIV                         ( 8'd0),                                // CHECK
    .QPLL0LOCKDETCLK                    ( 1'd0),
    .QPLL0LOCKEN                        ( 1'd1),
    .QPLL0PD                            (GTCOM_QPLL0PD),                        
    .QPLL0REFCLKSEL                     ( 3'd1),                                                          
    .QPLL0RESET                         (GTCOM_QPLL0RESET),                     
       
    .QPLL0FBCLKLOST                     (),
    .QPLL0LOCK                          (GTCOM_QPLL0LOCK),
    .QPLL0OUTCLK                        (GTCOM_QPLL0OUTCLK),
    .QPLL0OUTREFCLK                     (GTCOM_QPLL0OUTREFCLK),
    .QPLL0REFCLKLOST                    (),     
    .QPLLDMONITOR0                      (),                                                                      
                                               
    //----------------------------------------------------------------------------------------------
    //  QPLL1 Ports
    //----------------------------------------------------------------------------------------------
    .QPLL1CLKRSVD0                      ( 1'd0),
    .QPLL1CLKRSVD1                      ( 1'd0),                                
    .QPLL1FBDIV                         ( 8'd0),                                // CHECK
    .QPLL1LOCKDETCLK                    ( 1'd0),
    .QPLL1LOCKEN                        ( 1'd1),
    .QPLL1PD                            (GTCOM_QPLL1PD),
    .QPLL1REFCLKSEL                     ( 3'd1),                        
    .QPLL1RESET                         (GTCOM_QPLL1RESET),      
     
    .QPLL1FBCLKLOST                     (),  
    .QPLL1LOCK                          (GTCOM_QPLL1LOCK),       
    .QPLL1OUTCLK                        (GTCOM_QPLL1OUTCLK),     
    .QPLL1OUTREFCLK                     (GTCOM_QPLL1OUTREFCLK),                       
    .QPLL1REFCLKLOST                    (),  
    .QPLLDMONITOR1                      (),            
         
    //----------------------------------------------------------------------------------------------
    //  PCIe Ports
    //----------------------------------------------------------------------------------------------
    .PCIERATEQPLL0                      (GTCOM_QPLLRATE),           
    .PCIERATEQPLL1                      (GTCOM_QPLLRATE),       
                                                                                                       
    //----------------------------------------------------------------------------------------------
    //  DRP Ports
    //----------------------------------------------------------------------------------------------
    .DRPCLK                             (GTCOM_DRPCLK),                                        
    .DRPADDR                            (GTCOM_DRPADDR),                                       
    .DRPEN                              (GTCOM_DRPEN),                                             
    .DRPWE                              (GTCOM_DRPWE),     
    .DRPDI                              (GTCOM_DRPDI),                                      
                                                                         
    .DRPRDY                             (GTCOM_DRPRDY),    
    .DRPDO                              (GTCOM_DRPDO),                                      
        
    //----------------------------------------------------------------------------------------------
    //  rCal Ports
    //----------------------------------------------------------------------------------------------        
    .RCALENB                            ( 1'd1),          
                                                                                                        
    //----------------------------------------------------------------------------------------------
    //  Band Gap Ports
    //----------------------------------------------------------------------------------------------
    .BGBYPASSB                          ( 1'b1),                                
    .BGMONITORENB                       ( 1'b1),                                
    .BGPDB                              ( 1'b1),  
    .BGRCALOVRD                         ( 5'b11111),                                 
    .BGRCALOVRDENB                      ( 1'b1),                                                            
        
    //----------------------------------------------------------------------------------------------
    //  SDM0 Ports
    //----------------------------------------------------------------------------------------------
    .SDM0DATA                           (25'd0),
    .SDM0RESET                          ( 1'd0),
    .SDM0TOGGLE                         ( 1'd0), 
    .SDM0WIDTH                          ( 2'd0),
    
    .SDM0FINALOUT                       (),
    .SDM0TESTDATA                       (),

    //----------------------------------------------------------------------------------------------
    //  SDM1 Ports
    //----------------------------------------------------------------------------------------------
    .SDM1DATA                           (25'd0),
    .SDM1RESET                          ( 1'd0),
    .SDM1TOGGLE                         ( 1'd0), 
    .SDM1WIDTH                          ( 2'd0),
    
    .SDM1FINALOUT                       (),
    .SDM1TESTDATA                       (),

    //----------------------------------------------------------------------------------------------
    //  TCON Ports
    //----------------------------------------------------------------------------------------------
    //.TCONGPI                            (10'd0),
    //.TCONPOWERUP                        ( 1'd0),
    //.TCONRESET                          ( 2'd0),
    //.TCONRSVDIN1                        ( 2'd0),
    
    //.TCONGPO                            (),
    //.TCONRSVDOUT0                       (),

    //----------------------------------------------------------------------------------------------
    //  Reserved & MISC Ports
    //----------------------------------------------------------------------------------------------
    .PMARSVD0                           ( 8'd0),            
    .PMARSVD1                           ( 8'd0),  
    .QPLLRSVD1                          ( 8'd0),
    .QPLLRSVD2                          ( 5'd0),               
    .QPLLRSVD3                          ( 5'd0),          
    .QPLLRSVD4                          ( 8'd0),                   

    .PMARSVDOUT0                        (),
    .PMARSVDOUT1                        (),

    //----------------------------------------------------------------------------------------------
    //  MicroBlaze Ports
    //----------------------------------------------------------------------------------------------
    .UBCFGSTREAMEN                      ( 1'b0),
    .UBDO                               ( 16'h0),
    .UBDRDY                             ( 1'b0),
    .UBENABLE                           ( 1'b0),
    .UBGPI                              ( 2'b0),
    .UBINTR                             ( 2'b0),
    .UBIOLMBRST                         ( 1'b0),
    .UBMBRST                            ( 1'b0),
    .UBMDMCAPTURE                       ( 1'b0),
    .UBMDMDBGRST                        ( 1'b0),
    .UBMDMDBGUPDATE                     ( 1'b0),
    .UBMDMREGEN                         ( 4'b0),
    .UBMDMSHIFT                         ( 1'b0),
    .UBMDMSYSRST                        ( 1'b0),
    .UBMDMTCK                           ( 1'b0),
    .UBMDMTDI                           ( 1'b0),

    .UBDADDR                            (),
    .UBDEN                              (),
    .UBDI                               (),
    .UBDWE                              (),
    .UBMDMTDO                           (),
    .UBRSVDOUT                          (),
    .UBTXUART                           ()

);

end else begin: GTH_COMMON
GTHE4_COMMON #
(   
    //---------------------------------------------------------------------------------------------- 
    //  Simulation Attributes
    //----------------------------------------------------------------------------------------------      
    .SIM_MODE                           ("FAST"),                                                                                                                                                                                      
    .SIM_RESET_SPEEDUP                  ("TRUE"),                                                                                              
    .SIM_VERSION                        (1),                                                                          

    //----------------------------------------------------------------------------------------------               
    //  Clock Attributes
    //----------------------------------------------------------------------------------------------    
    .RXRECCLKOUT0_SEL                   ( 2'b00),
    .RXRECCLKOUT1_SEL                   ( 2'b00),                    

    //----------------------------------------------------------------------------------------------
    //  QPLL0 Attributes 
    //----------------------------------------------------------------------------------------------    
    .AEN_QPLL0_FBDIV                    (1'b1),                                 
    .QPLL0CLKOUT_RATE                   ("HALF"),                              
    .QPLL0_CFG0                         (16'b0011001100011100),                            
    .QPLL0_CFG1                         (16'b1101000000111000),                             
    .QPLL0_CFG1_G3                      (16'b1101000000111000),                             
    .QPLL0_CFG2                         (16'b0000111111000000),                             
    .QPLL0_CFG2_G3                      (16'b0000111111000000),                        
    .QPLL0_CFG3                         (16'b0000000100100000),                  
    .QPLL0_CFG4                         (16'b0000000011100111),
    .QPLL0_CP                           (10'b1111111111),                       // Optimized for PCIe PLL compliance
    .QPLL0_CP_G3                        (10'b0000011111),                       // Optimized for PCIe PLL compliance
    .QPLL0_FBDIV                        (QPLL_FBDIV),
    .QPLL0_FBDIV_G3                     (QPLL_FBDIV_G34),
    .QPLL0_INIT_CFG0                    (16'h02B2),
    .QPLL0_INIT_CFG1                    ( 8'b00000000),
    .QPLL0_LOCK_CFG                     (16'b0010010111101000),                             // [10] : 1'b1 = Auto VCO
    .QPLL0_LOCK_CFG_G3                  (16'b0010010111101000),                             // [10] : 1'b1 = Auto VCO
    .QPLL0_LPF                          (10'b0100110101),                       // Optimized for PCIe PLL compliance
    .QPLL0_LPF_G3                       (10'b1111111111),                       // Optimized for PCIe PLL compliance
    .QPLL0_PCI_EN                       ( 1'b1),                                
    .QPLL0_RATE_SW_USE_DRP              ( 1'b0),                                // Advance PCIe feature
    .QPLL0_REFCLK_DIV                   (1),
    .QPLL0_SDM_CFG0                     (16'b0000000011000000),                
    .QPLL0_SDM_CFG1                     (16'b0000000000000000),
    .QPLL0_SDM_CFG2                     (16'b0000000000000000),
                     
    //---------------------------------------------------------------------------------------------- 
    //  QPLL1 Attributes               
    //----------------------------------------------------------------------------------------------    
    .AEN_QPLL1_FBDIV                    (1'b1),                                 
    .QPLL1CLKOUT_RATE                   ("HALF"),                              
    .QPLL1_CFG0                         (16'b0011001100011100),                             
    .QPLL1_CFG1                         (16'b0001000000101000),                             
    .QPLL1_CFG1_G3                      (16'b0001000000101000),                             
    .QPLL1_CFG2                         (16'b0000111111000011),                             
    .QPLL1_CFG2_G3                      (16'b0000000100100000),                         
    .QPLL1_CFG3                         (16'b0000000100100000),                  
    .QPLL1_CFG4                         (16'b0000000001100011),
    .QPLL1_CP                           (10'b0100010101),                       // Optimized for PCIe PLL compliance
    .QPLL1_CP_G3                        (10'b0100010101),                       // Optimized for PCIe PLL compliance
    .QPLL1_FBDIV                        (QPLL_FBDIV),
    .QPLL1_FBDIV_G3                     (QPLL_FBDIV_G34),
    .QPLL1_INIT_CFG0                    (16'h02B2),
    .QPLL1_INIT_CFG1                    ( 8'b00000000),
    .QPLL1_LOCK_CFG                     (16'b0010010111101000),                             // [10] : 1'b1 = Auto VCO
    .QPLL1_LOCK_CFG_G3                  (16'b0010010111101000),                             // [10] : 1'b1 = Auto VCO
    .QPLL1_LPF                          (10'b0000010101),                       // Optimized for PCIe PLL compliance
    .QPLL1_LPF_G3                       (10'b0000010101),                       // Optimized for PCIe PLL compliance
    .QPLL1_PCI_EN                       ( 1'b1),                               
    .QPLL1_RATE_SW_USE_DRP              ( 1'b0),                                // Advance PCIe feature
    .QPLL1_REFCLK_DIV                   (1),
    .QPLL1_SDM_CFG0                     (16'b0000000011000000),                 
    .QPLL1_SDM_CFG1                     (16'b0000000000000000),
    .QPLL1_SDM_CFG2                     (16'b0000000000000000),
 
    //----------------------------------------------------------------------------------------------
    //  PPF Attributes                                                         
    //----------------------------------------------------------------------------------------------      
    .PPF0_CFG                           (16'h0FFF),                            
    .PPF1_CFG                           (16'h0FFF),                           
    
    //----------------------------------------------------------------------------------------------
    //  Bias Attributes                                                          
    //----------------------------------------------------------------------------------------------
    .BIAS_CFG0                          (16'b0000000000000000),
    .BIAS_CFG1                          (16'b0000000000000000),
    .BIAS_CFG2                          (16'b0000000100100100),                 // Optimized for PCIe PLL compliance
    .BIAS_CFG3                          (16'b0000000001000001),                 
    .BIAS_CFG4                          (16'b0000000000010000),    
    .BIAS_CFG_RSVD                      (10'b0000000000),  
       
    //---------------------------------------------------------------------------------------------- 
    //  SDM0 Attributes                                                          
    //----------------------------------------------------------------------------------------------
    .A_SDM0TOGGLE                       ( 1'b0),
    .AEN_SDM0TOGGLE                     ( 1'b0),
    .SDM0INITSEED0_0                    (16'b0000000000000000),
    .SDM0INITSEED0_1                    ( 9'b000000000),
    
    //---------------------------------------------------------------------------------------------- 
    //  SDM1 Attributes                                                          
    //----------------------------------------------------------------------------------------------     
    .A_SDM1DATA_HIGH                    ( 9'b000000000),
    .A_SDM1DATA_LOW                     (16'b0000000000000000),
    .A_SDM1TOGGLE                       ( 1'b0),
    .AEN_SDM1TOGGLE                     ( 1'b0),
    .SDM1INITSEED0_0                    (16'b0000000000000000),
    .SDM1INITSEED0_1                    ( 9'b000000000),     
          
    //----------------------------------------------------------------------------------------------
    //  Reserved & MISC Attributes                                                         
    //----------------------------------------------------------------------------------------------            
    .COMMON_CFG0                        (16'b0000000000000000),
    .COMMON_CFG1                        (16'b0000000000000000),
    .POR_CFG                            (16'b0000000000000000),                 // CHECK      
    .RSVD_ATTR0                         (16'b0000000000000000),                 // CHECK
    .RSVD_ATTR1                         (16'b0000000000000000),    
    .RSVD_ATTR2                         (16'b0000000000000000),                 // CHECK                
    .RSVD_ATTR3                         (16'b0000000000000000),
    .SARC_ENB                           ( 1'b0),
    .SARC_SEL                           ( 1'b0)
)
gthe4_common_i 
(       
    //----------------------------------------------------------------------------------------------
    //  QPLL0 Clock Ports
    //----------------------------------------------------------------------------------------------
    .GTGREFCLK0                         ( 1'd0), 
    .GTREFCLK00                         (GTCOM_REFCLK),                         
    .GTREFCLK10                         ( 1'd0),
    .GTNORTHREFCLK00                    ( 1'd0),
    .GTNORTHREFCLK10                    ( 1'd0),
    .GTSOUTHREFCLK00                    ( 1'd0),
    .GTSOUTHREFCLK10                    ( 1'd0),
   
    .REFCLKOUTMONITOR0                  (),
    .RXRECCLK0SEL                       (),
    
    //----------------------------------------------------------------------------------------------
    //  QPLL1 Clock Ports
    //----------------------------------------------------------------------------------------------
    .GTGREFCLK1                         ( 1'd0),
    .GTREFCLK01                         (GTCOM_REFCLK),
    .GTREFCLK11                         ( 1'd0),
    .GTNORTHREFCLK01                    ( 1'd0),    
    .GTNORTHREFCLK11                    ( 1'd0),
    .GTSOUTHREFCLK01                    ( 1'd0),
    .GTSOUTHREFCLK11                    ( 1'd0),        
        
    .REFCLKOUTMONITOR1                  (),  
    .RXRECCLK1SEL	                      (), 
        
    //----------------------------------------------------------------------------------------------
    //  QPLL0 Ports
    //----------------------------------------------------------------------------------------------
    .QPLL0CLKRSVD0                      ( 1'd0),
    .QPLL0CLKRSVD1                      ( 1'd0),                              
    .QPLL0FBDIV                         ( 8'd0),                                // CHECK
    .QPLL0LOCKDETCLK                    ( 1'd0),
    .QPLL0LOCKEN                        ( 1'd1),
    .QPLL0PD                            (GTCOM_QPLL0PD),                        
    .QPLL0REFCLKSEL                     ( 3'd1),                                                          
    .QPLL0RESET                         (GTCOM_QPLL0RESET),                     
       
    .QPLL0FBCLKLOST                     (),
    .QPLL0LOCK                          (GTCOM_QPLL0LOCK),
    .QPLL0OUTCLK                        (GTCOM_QPLL0OUTCLK),
    .QPLL0OUTREFCLK                     (GTCOM_QPLL0OUTREFCLK),
    .QPLL0REFCLKLOST                    (),     
    .QPLLDMONITOR0                      (),                                                                      
                                               
    //----------------------------------------------------------------------------------------------
    //  QPLL1 Ports
    //----------------------------------------------------------------------------------------------
    .QPLL1CLKRSVD0                      ( 1'd0),
    .QPLL1CLKRSVD1                      ( 1'd0),                                
    .QPLL1FBDIV                         ( 8'd0),                                // CHECK
    .QPLL1LOCKDETCLK                    ( 1'd0),
    .QPLL1LOCKEN                        ( 1'd1),
    .QPLL1PD                            (GTCOM_QPLL1PD),
    .QPLL1REFCLKSEL                     ( 3'd1),                        
    .QPLL1RESET                         (GTCOM_QPLL1RESET),      
     
    .QPLL1FBCLKLOST                     (),  
    .QPLL1LOCK                          (GTCOM_QPLL1LOCK),       
    .QPLL1OUTCLK                        (GTCOM_QPLL1OUTCLK),     
    .QPLL1OUTREFCLK                     (GTCOM_QPLL1OUTREFCLK),                       
    .QPLL1REFCLKLOST                    (),  
    .QPLLDMONITOR1                      (),            
         
    //----------------------------------------------------------------------------------------------
    //  PCIe Ports
    //----------------------------------------------------------------------------------------------
    .PCIERATEQPLL0                      (GTCOM_QPLLRATE),           
    .PCIERATEQPLL1                      (GTCOM_QPLLRATE),       
                                                                                                       
    //----------------------------------------------------------------------------------------------
    //  DRP Ports
    //----------------------------------------------------------------------------------------------
    .DRPCLK                             (GTCOM_DRPCLK),                                        
    .DRPADDR                            (GTCOM_DRPADDR),                                       
    .DRPEN                              (GTCOM_DRPEN),                                             
    .DRPWE                              (GTCOM_DRPWE),     
    .DRPDI                              (GTCOM_DRPDI),                                      
                                                                         
    .DRPRDY                             (GTCOM_DRPRDY),    
    .DRPDO                              (GTCOM_DRPDO),                                      
        
    //----------------------------------------------------------------------------------------------
    //  rCal Ports
    //----------------------------------------------------------------------------------------------        
    .RCALENB                            ( 1'd1),          
                                                                                                        
    //----------------------------------------------------------------------------------------------
    //  Band Gap Ports
    //----------------------------------------------------------------------------------------------
    .BGBYPASSB                          ( 1'b1),                                
    .BGMONITORENB                       ( 1'b1),                                
    .BGPDB                              ( 1'b1),  
    .BGRCALOVRD                         ( 5'b11111),                                 
    .BGRCALOVRDENB                      ( 1'b1),                                                            
        
    //----------------------------------------------------------------------------------------------
    //  SDM0 Ports
    //----------------------------------------------------------------------------------------------
    .SDM0DATA                           (25'd0),
    .SDM0RESET                          ( 1'd0),
    .SDM0TOGGLE                         ( 1'd0), 
    .SDM0WIDTH                          ( 2'd0),
    
    .SDM0FINALOUT                       (),
    .SDM0TESTDATA                       (),

    //----------------------------------------------------------------------------------------------
    //  SDM1 Ports
    //----------------------------------------------------------------------------------------------
    .SDM1DATA                           (25'd0),
    .SDM1RESET                          ( 1'd0),
    .SDM1TOGGLE                         ( 1'd0), 
    .SDM1WIDTH                          ( 2'd0),
    
    .SDM1FINALOUT                       (),
    .SDM1TESTDATA                       (),

    //----------------------------------------------------------------------------------------------
    //  TCON Ports
    //----------------------------------------------------------------------------------------------
    .TCONGPI                            (10'd0),
    .TCONPOWERUP                        ( 1'd0),
    .TCONRESET                          ( 2'd0),
    .TCONRSVDIN1                        ( 2'd0),
    
    .TCONGPO                            (),
    .TCONRSVDOUT0                       (),

    //----------------------------------------------------------------------------------------------
    //  Reserved & MISC Ports
    //----------------------------------------------------------------------------------------------
    .PMARSVD0                           ( 8'd0),            
    .PMARSVD1                           ( 8'd0),  
    .QPLLRSVD1                          ( 8'd0),
    .QPLLRSVD2                          ( 5'd0),               
    .QPLLRSVD3                          ( 5'd0),          
    .QPLLRSVD4                          ( 8'd0),                   

    .PMARSVDOUT0                        (),
    .PMARSVDOUT1                        ()
);
end
endgenerate

endmodule
