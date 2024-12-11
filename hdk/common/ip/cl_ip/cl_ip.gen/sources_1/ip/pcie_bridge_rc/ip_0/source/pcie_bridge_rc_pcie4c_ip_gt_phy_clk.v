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
// File       : pcie_bridge_rc_pcie4c_ip_gt_phy_clk.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
//  Design :  PHY Wrapper 
//  Module :  PHY Clock
//--------------------------------------------------------------------------------------------------

`timescale 1ps / 1ps

//--------------------------------------------------------------------------------------------------
//  PHY Clock Module
//--------------------------------------------------------------------------------------------------
(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_rc_pcie4c_ip_gt_phy_clk #
(
    parameter integer PHY_MAX_SPEED     = 4, 
    parameter         PHY_GEN4_64BIT_EN = "FALSE",
    parameter integer PHY_CORECLK_FREQ  = 2,  
    parameter integer PHY_USERCLK_FREQ  = 4, 
    parameter integer PHY_MCAPCLK_FREQ  = 4          
)
(
    //--------------------------------------------------------------------------
    //  CLK Port
    //--------------------------------------------------------------------------
    input                               CLK_TXOUTCLK,
    output                              CLK_PCLK2_GT,

    //--------------------------------------------------------------------------
    //  int_clk Ports
    //--------------------------------------------------------------------------
    input                               CLK_INTCLK_CE,
    input                               CLK_INTCLK_CEMASK,
    input                               CLK_INTCLK_CLR,
    input                               CLK_INTCLK_CLRMASK,
    input       [ 2:0]                  CLK_INTCLK_DIV,
    output                              CLK_INTCLK,
    
    //--------------------------------------------------------------------------
    //  PCLK Ports
    //--------------------------------------------------------------------------
    input                               CLK_PCLK_CE,
    input                               CLK_PCLK_CEMASK,
    input                               CLK_PCLK_CLR,
    input                               CLK_PCLK_CLRMASK,
    input       [ 2:0]                  CLK_PCLK_DIV,
    output                              CLK_PCLK,
    
    //--------------------------------------------------------------------------
    //  PCLK2 Ports
    //--------------------------------------------------------------------------
    input                               CLK_PCLK2_CE,
    input                               CLK_PCLK2_CEMASK,
    input                               CLK_PCLK2_CLR,
    input                               CLK_PCLK2_CLRMASK,
    input       [ 2:0]                  CLK_PCLK2_DIV,
    output                              CLK_PCLK2,
    
    //--------------------------------------------------------------------------
    //  CORECLK Ports
    //--------------------------------------------------------------------------
    input                               CLK_CORECLK_CE,
    input                               CLK_CORECLK_CEMASK,
    input                               CLK_CORECLK_CLR,
    input                               CLK_CORECLK_CLRMASK,
    output                              CLK_CORECLK,      
    
    //--------------------------------------------------------------------------
    //  USERCLK Ports
    //--------------------------------------------------------------------------
    input                               CLK_USERCLK_CE,
    input                               CLK_USERCLK_CEMASK,
    input                               CLK_USERCLK_CLR,
    input                               CLK_USERCLK_CLRMASK,
    output                              CLK_USERCLK,    
    
    output                              GT_DRP_CLK_125M,
    //--------------------------------------------------------------------------
    //  MCAPCLK Ports
    //--------------------------------------------------------------------------
    input                               CLK_MCAPCLK_CE,
    input                               CLK_MCAPCLK_CEMASK,
    input                               CLK_MCAPCLK_CLR,
    input                               CLK_MCAPCLK_CLRMASK,
    output                              CLK_MCAPCLK    
);
    //--------------------------------------------------------------------------
    //  Internal Signals
    //--------------------------------------------------------------------------                                     
    (*keep*) wire                       pclk;                                                                 
    (*keep*) wire                       pclk2;



    //----------------------------------------------------------------------------------------------
    //  Divider for CORECLK
    //----------------------------------------------------------------------------------------------     
    localparam [ 2:0] CORECLK_DIV_250MHZ = 3'd0;                                                    // 250.0 MHz
    localparam [ 2:0] CORECLK_DIV_500MHZ = (PHY_CORECLK_FREQ == 1) ? 3'd1 : 3'd0;                   // 250.0 MHZ : Default = 500.0 MHz                                
    
    localparam [ 2:0] CORECLK_DIV        = (PHY_MAX_SPEED     < 3) ? CORECLK_DIV_250MHZ : 
                                           (PHY_MAX_SPEED    == 4) ? CORECLK_DIV_500MHZ : 
                                           (PHY_CORECLK_FREQ == 1) ? CORECLK_DIV_250MHZ : CORECLK_DIV_500MHZ;



    //----------------------------------------------------------------------------------------------
    //  Divider for USERCLK
    //---------------------------------------------------------------------------------------------- 
    localparam [ 2:0] USERCLK_DIV_250MHZ = (PHY_USERCLK_FREQ == 3) ? 3'd0 :                         // 250.0 MHz
                                           (PHY_USERCLK_FREQ == 2) ? 3'd1 :                         // 125.0 MHz
                                           (PHY_USERCLK_FREQ == 1) ? 3'd3 : 3'd0;                   //  62.5 MHz : Default = 250.0 MHz
   
    localparam [ 2:0] USERCLK_DIV_500MHZ = (PHY_USERCLK_FREQ == 4) ? 3'd0 :                         // 500.0 MHz
                                           (PHY_USERCLK_FREQ == 3) ? 3'd1 :                         // 250.0 MHz
                                           (PHY_USERCLK_FREQ == 2) ? 3'd3 :                         // 125.0 MHz
                                           (PHY_USERCLK_FREQ == 1) ? 3'd7 : 3'd0;                   //  62.5 MHz : Default = 500.0 MHz
    
    localparam [ 2:0] USERCLK_DIV        = (PHY_MAX_SPEED     < 3) ? USERCLK_DIV_250MHZ :
                                           (PHY_MAX_SPEED    == 4) ? USERCLK_DIV_500MHZ : 
                                           (PHY_CORECLK_FREQ == 1) ? USERCLK_DIV_250MHZ : USERCLK_DIV_500MHZ;


                                           
    //----------------------------------------------------------------------------------------------
    //  Divider for MCAPCLK
    //---------------------------------------------------------------------------------------------- 
    localparam [ 2:0] MCAPCLK_DIV_250MHZ = (PHY_MCAPCLK_FREQ == 3) ? 3'd0 :                         // 250.0 MHz
                                           (PHY_MCAPCLK_FREQ == 2) ? 3'd1 :                         // 125.0 MHz
                                           (PHY_MCAPCLK_FREQ == 1) ? 3'd3 : 3'd0;                   //  62.5 MHz : Default = 250.0 MHz
   
    localparam [ 2:0] MCAPCLK_DIV_500MHZ = (PHY_MCAPCLK_FREQ == 4) ? 3'd0 :                         // 500.0 MHz
                                           (PHY_MCAPCLK_FREQ == 3) ? 3'd1 :                         // 250.0 MHz
                                           (PHY_MCAPCLK_FREQ == 2) ? 3'd3 :                         // 125.0 MHz
                                           (PHY_MCAPCLK_FREQ == 1) ? 3'd7 : 3'd0;                   //  62.5 MHz : Default = 500.0 MHz
    
    localparam [ 2:0] MCAPCLK_DIV        = (PHY_MAX_SPEED     < 3) ? MCAPCLK_DIV_250MHZ :
                                           (PHY_MAX_SPEED    == 4) ? MCAPCLK_DIV_500MHZ : 
                                           (PHY_CORECLK_FREQ == 1) ? MCAPCLK_DIV_250MHZ : MCAPCLK_DIV_500MHZ;

//--------------------------------------------------------------------------------------------------
//  BUFG_GT for intclk
//--------------------------------------------------------------------------------------------------
                                           
BUFG_GT bufg_gt_intclk
(
     //-------------------------------------------------------------------------
     //  Input Ports
     //-------------------------------------------------------------------------
    .CE                                 (CLK_INTCLK_CE),
    .CEMASK                             (CLK_INTCLK_CEMASK),
    .CLR                                (CLK_INTCLK_CLR),
    .CLRMASK                            (CLK_INTCLK_CLRMASK),
    .DIV                                (CLK_INTCLK_DIV),
    .I                                  (CLK_TXOUTCLK),

     //-------------------------------------------------------------------------
     //  Output Ports
     //-------------------------------------------------------------------------
    .O                                  (CLK_INTCLK)
);    


//--------------------------------------------------------------------------------------------------
//  BUFG_GT for PCLK
//--------------------------------------------------------------------------------------------------
BUFG_GT bufg_gt_pclk 
(
     //-------------------------------------------------------------------------
     //  Input Ports
     //-------------------------------------------------------------------------
    .CE                                 (CLK_PCLK_CE),
    .CEMASK                             (CLK_PCLK_CEMASK),
    .CLR                                (CLK_PCLK_CLR),
    .CLRMASK                            (CLK_PCLK_CLRMASK),
    .DIV                                (CLK_PCLK_DIV),
    .I                                  (CLK_TXOUTCLK),
    
     //-------------------------------------------------------------------------
     //  Output Ports
     //-------------------------------------------------------------------------
    .O                                  (pclk)
);



//--------------------------------------------------------------------------------------------------
//  BUFG_GT for PCLK2
//--------------------------------------------------------------------------------------------------
BUFG_GT bufg_gt_pclk2 
(
     //-------------------------------------------------------------------------
     //  Input Ports
     //-------------------------------------------------------------------------
    .CE                                 (CLK_PCLK2_CE),
    .CEMASK                             (CLK_PCLK2_CEMASK),
    .CLR                                (CLK_PCLK2_CLR),
    .CLRMASK                            (CLK_PCLK2_CLRMASK),
    .DIV                                (CLK_PCLK2_DIV),
    .I                                  (CLK_TXOUTCLK),
    
     //-------------------------------------------------------------------------
     //  Output Ports
     //-------------------------------------------------------------------------
    .O                                  (pclk2)
);



//--------------------------------------------------------------------------------------------------
//  BUFG_GT for CORECLK
//--------------------------------------------------------------------------------------------------
BUFG_GT bufg_gt_coreclk 
(
     //-------------------------------------------------------------------------
     //  Input Ports
     //-------------------------------------------------------------------------
    .CE                                 (CLK_CORECLK_CE),
    .CEMASK                             (CLK_CORECLK_CEMASK),
    .CLR                                (CLK_CORECLK_CLR),
    .CLRMASK                            (CLK_CORECLK_CLRMASK),
    .DIV                                (    CORECLK_DIV),
    .I                                  (CLK_TXOUTCLK),

     //-------------------------------------------------------------------------
     //  Output Ports
     //-------------------------------------------------------------------------
    .O                                  (CLK_CORECLK)
);



//--------------------------------------------------------------------------------------------------
//  BUFG_GT for USERCLK
//--------------------------------------------------------------------------------------------------
BUFG_GT bufg_gt_userclk 
(
     //-------------------------------------------------------------------------
     //  Input Ports
     //-------------------------------------------------------------------------
    .CE                                 (CLK_USERCLK_CE),
    .CEMASK                             (CLK_USERCLK_CEMASK),
    .CLR                                (CLK_USERCLK_CLR),
    .CLRMASK                            (CLK_USERCLK_CLRMASK),
    .DIV                                (    USERCLK_DIV),
    .I                                  (CLK_TXOUTCLK),
    
     //-------------------------------------------------------------------------
     //  Output Ports
     //-------------------------------------------------------------------------
    .O                                  (CLK_USERCLK)
);


  assign GT_DRP_CLK_125M = 1'b0;


//--------------------------------------------------------------------------------------------------
//  BUFG_GT for MCAPCLK
//--------------------------------------------------------------------------------------------------
BUFG_GT bufg_gt_mcapclk
(
     //-------------------------------------------------------------------------
     //  Input Ports
     //-------------------------------------------------------------------------
    .CE                                 (CLK_MCAPCLK_CE),
    .CEMASK                             (CLK_MCAPCLK_CEMASK),
    .CLR                                (CLK_MCAPCLK_CLR),
    .CLRMASK                            (CLK_MCAPCLK_CLRMASK),
    .DIV                                (    MCAPCLK_DIV),
    .I                                  (CLK_TXOUTCLK),

     //-------------------------------------------------------------------------
     //  Output Ports
     //-------------------------------------------------------------------------
    .O                                  (CLK_MCAPCLK)
);


//--------------------------------------------------------------------------------------------------
//  PHY Clock Output
//--------------------------------------------------------------------------------------------------
assign CLK_PCLK     = pclk;
assign CLK_PCLK2    = pclk2;
assign CLK_PCLK2_GT = (PHY_GEN4_64BIT_EN == "TRUE") ? pclk2 : pclk;



endmodule
