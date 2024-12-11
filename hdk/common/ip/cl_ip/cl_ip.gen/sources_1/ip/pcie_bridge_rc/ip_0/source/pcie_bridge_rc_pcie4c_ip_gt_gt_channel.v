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
// File       : pcie_bridge_rc_pcie4c_ip_gt_gt_channel.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
//  Design :  PHY Wrapper 
//  Module :  GT Channel
//--------------------------------------------------------------------------------------------------

`timescale 1ps / 1ps

//--------------------------------------------------------------------------------------------------
//  GT Channel Module
//--------------------------------------------------------------------------------------------------
(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_rc_pcie4c_ip_gt_gt_channel #
(
    parameter         PHY_SIM_EN                 = "FALSE", 
    parameter         PHY_GT_XCVR                = "GTY",
    parameter integer PHY_MODE                   = 0,
    parameter integer PHY_REFCLK_MODE            = 0,
    parameter integer PHY_LANE                   = 1,
    parameter integer PHY_MAX_SPEED              = 3,
    parameter         PHY_GEN4_64BIT_EN          = "FALSE",
    parameter         PHY_GEN12_CDR_CTRL_ON_EIDLE = "FALSE",   
    parameter         PHY_GEN34_CDR_CTRL_ON_EIDLE = "FALSE", 
    parameter integer PHY_REFCLK_FREQ            = 0,                
    parameter integer PHY_CORECLK_FREQ           = 2,
    parameter         GT_LANE_NUM                = 0,
    parameter         PHY_GEN4_EIEOS             = 1
)
(    
    //--------------------------------------------------------------------------
    //  Clock Ports
    //--------------------------------------------------------------------------
    input                               GT_GTREFCLK0,
    input                               GT_TXUSRCLK,
    input                               GT_RXUSRCLK,
    input                               GT_TXUSRCLK2,
    input                               GT_RXUSRCLK2,    

    output                              GT_TXOUTCLK, 
    output                              GT_RXOUTCLK,
    output                              GT_TXOUTCLKFABRIC,                                                        
    output                              GT_RXOUTCLKFABRIC,                                                        
    output                              GT_TXOUTCLKPCS,                                                        
    output                              GT_RXOUTCLKPCS,  
    output                              GT_RXRECCLKOUT,

    input       [ 2:0]                  GT_TXOUTCLKSEL,
    
    //--------------------------------------------------------------------------   
    //  BUFG_GT Controller Ports                                                                        
    //--------------------------------------------------------------------------                   
    output                              GT_BUFGTCE,       
    output      [ 2:0]                  GT_BUFGTCEMASK, 
    output                              GT_BUFGTRESET,
    output      [ 2:0]                  GT_BUFGTRSTMASK,
    output      [ 8:0]                  GT_BUFGTDIV,   
                
    //--------------------------------------------------------------------------
    //  Reset Ports
    //--------------------------------------------------------------------------
    input                               GT_CPLLPD,
    input                               GT_CPLLRESET,
    input                               GT_TXPROGDIVRESET,
    input                               GT_GTTXRESET,
    input                               GT_GTRXRESET,
    input                               GT_TXUSERRDY,
    input                               GT_RXUSERRDY,
    
    input                               GT_TXPMARESET,                                            
    input                               GT_RXPMARESET,                                            
    input                               GT_TXPCSRESET,   
    input                               GT_RXPCSRESET,  
    input                               GT_RXBUFRESET,
    input                               GT_RXCDRRESET,
    input                               GT_RXDFELPMRESET,
    input                               GT_RXCDRFREQRESET,
    
    input                               GT_RESETOVRD,
                                        
    output                              GT_GTPOWERGOOD,
    output                              GT_TXPROGDIVRESETDONE,  
    output                              GT_TXPMARESETDONE,
    output                              GT_RXPMARESETDONE,
    output                              GT_TXRESETDONE,
    output                              GT_RXRESETDONE,                 
    
    //--------------------------------------------------------------------------
    //  QPLL Ports
    //--------------------------------------------------------------------------
    input                               GT_QPLL0CLK,
    input                               GT_QPLL0REFCLK,
    input                               GT_QPLL0LOCK,
    input                               GT_QPLL1CLK,
    input                               GT_QPLL1REFCLK,
    input                               GT_QPLL1LOCK,
    
    output      [ 2:0]                  GT_QPLLRATE,
    
    //--------------------------------------------------------------------------
    //  Serial Line Ports
    //--------------------------------------------------------------------------
    input                               GT_RXN,
    input                               GT_RXP,
    
    output                              GT_TXP,
    output                              GT_TXN,
    
    //--------------------------------------------------------------------------
    //  TX Data Ports 
    //--------------------------------------------------------------------------
    input       [63:0]                  GT_TXDATA,
    input       [ 1:0]                  GT_TXDATAK,   
    input                               GT_TXDATA_VALID,
    input                               GT_TXSTART_BLOCK,      
    input       [ 1:0]                  GT_TXSYNC_HEADER,  
    
    //--------------------------------------------------------------------------
    //  RX Data Ports 
    //--------------------------------------------------------------------------
    output      [63:0]                  GT_RXDATA,
    output      [ 1:0]                  GT_RXDATAK,
    output                              GT_RXDATA_VALID,
    output      [ 1:0]                  GT_RXSTART_BLOCK,      
    output      [ 1:0]                  GT_RXSYNC_HEADER,     
    
    //--------------------------------------------------------------------------
    //  PHY Command Ports
    //--------------------------------------------------------------------------
    input                               GT_TXDETECTRX,
    input                               GT_TXELECIDLE,
    input                               GT_TXCOMPLIANCE,
    input                               GT_RXPOLARITY,
    input       [ 1:0]                  GT_POWERDOWN,
    input       [ 1:0]                  GT_RATE,
    input                               GT_RXCDRHOLD,
      
    //--------------------------------------------------------------------------
    //  PHY Status Ports
    //--------------------------------------------------------------------------
    output                              GT_RXVALID,
    output                              GT_PHYSTATUS,
    output                              GT_RXELECIDLE,
    output      [ 2:0]                  GT_RXSTATUS,
      
    //--------------------------------------------------------------------------
    //  TX Equalization Ports 
    //--------------------------------------------------------------------------
    input       [ 2:0]                  GT_TXMARGIN,
    input                               GT_TXSWING,
    input       [ 1:0]                  GT_TXDEEMPH,
    
    //--------------------------------------------------------------------------
    //  TX Equalization Ports (Gen3)
    //--------------------------------------------------------------------------
    input       [ 4:0]                  GT_TXPRECURSOR,
    input       [ 6:0]                  GT_TXMAINCURSOR,
    input       [ 4:0]                  GT_TXPOSTCURSOR,      
    
    //--------------------------------------------------------------------------
    //  PCIe Ports
    //--------------------------------------------------------------------------
    input                               GT_PCIERSTIDLE,        
    input                               GT_PCIERSTTXSYNCSTART, 
    input                               GT_PCIEEQRXEQADAPTDONE,
    input                               GT_PCIEUSERRATEDONE,
             
    output                              GT_PCIEUSERPHYSTATUSRST,    
    output      [ 1:0]                  GT_PCIERATEQPLLPD,                  
    output      [ 1:0]                  GT_PCIERATEQPLLRESET,                
    output                              GT_PCIERATEIDLE,            
    output                              GT_PCIESYNCTXSYNCDONE,                      
    output                              GT_PCIERATEGEN3,    
    output                              GT_PCIEUSERGEN3RDY, 
    output                              GT_PCIEUSERRATESTART,  
                
    //--------------------------------------------------------------------------
    //  USB Ports
    //--------------------------------------------------------------------------
    input                               GT_TXONESZEROS,                        
    input                               GT_RXEQTRAINING,                       
    input                               GT_RXTERMINATION,                        
    
    output                              GT_POWERPRESENT,                                 
                                                          
    //--------------------------------------------------------------------------
    //  TX Sync Alignment Ports
    //--------------------------------------------------------------------------                                                      
    input                               GT_TXSYNCALLIN,
    input                               GT_TXSYNCIN,                                        
                
    output                              GT_TXPHALIGNDONE,            
    output                              GT_TXSYNCOUT,
   
    //--------------------------------------------------------------------------
    //  Loopback & PRBS Ports
    //--------------------------------------------------------------------------     
    input       [ 2:0]                  GT_LOOPBACK,                                              
    input       [ 3:0]                  GT_PRBSSEL,
    input                               GT_TXPRBSFORCEERR, 
    input                               GT_RXPRBSCNTRESET,                                                                                                      

    output                              GT_RXPRBSERR,                                              
    output                              GT_RXPRBSLOCKED,  
      
    //--------------------------------------------------------------------------
    //  GT Status Ports
    //--------------------------------------------------------------------------   
    input                               GT_MASTER_CPLLLOCK,
                                                                                                                      
    output                              GT_CPLLLOCK,
    output                              GT_RXCDRLOCK,
    output                              GT_GEN34_EIOS_DET,
    output                              GT_RXRATEDONE,

    //--------------------------------------------------------------------------
    //  DRP Ports
    //--------------------------------------------------------------------------
    input                               GT_DRPCLK,
    input      [9:0]                    GT_DRPADDR,
    input                               GT_DRPEN,
    input                               GT_DRPWE,
    input      [15:0]                   GT_DRPDI,
    
    output                              GT_DRPRDY,
    output     [15:0]                   GT_DRPDO    
);

//-------------------------------------------------------------------------------------------------
//  Internal Signals
//-------------------------------------------------------------------------------------------------- 
    wire        [127:0]                 txdata;
    wire        [ 15:0]                 txctrl0;
    wire        [ 15:0]                 txctrl1;
    wire        [  7:0]                 txctrl2;
    
    wire        [127:0]                 rxdata;
    wire        [ 15:0]                 rxctrl0;
    
    wire                                pcierategen3;
    wire        [ 15:0]                 pcsrsvdout;
    
    wire                                rxelecidle_int;
    wire                                phy_rxcdrreset;
    wire                                rxcdrreset_int;
 
 
 
    //----------------------------------------------------------------------------------------------
    //  Single vs. Mulit-lane Selection
    //----------------------------------------------------------------------------------------------
    localparam [ 0:0] MULTI_LANE     = (PHY_LANE    == 1) ? 1'b0 : 1'b1;
    localparam [ 0:0] MASTER_LANE    = (GT_LANE_NUM == 0) ? 1'b1 : 1'b0;
    localparam [ 0:0] LOCAL_MASTER   = 1'b1;                                                        // Default for GTH                                      



    //----------------------------------------------------------------------------------------------
    //  PHY Mode
    //----------------------------------------------------------------------------------------------
    localparam        PCS_PCIE_EN = (PHY_MODE == 1) ? "FALSE" : "TRUE";
    localparam [ 0:0] USB_MODE    = (PHY_MODE == 1) ? 1'b1    : 1'b0;



    //----------------------------------------------------------------------------------------------
    //  CPLL_FBDIV - CPLL Feedback (N1) Divider
    //----------------------------------------------------------------------------------------------
    localparam CPLL_FBDIV_45 = (PHY_MAX_SPEED < 3) ? 5 : 4;
    
    
    
    //----------------------------------------------------------------------------------------------
    //  CPLL_FBDIV - CPLL Feedback (N2) Divider
    //----------------------------------------------------------------------------------------------
    localparam CPLL_FBDIV = (PHY_REFCLK_FREQ == 2) ?  2 : 
                            (PHY_REFCLK_FREQ == 1) ?  4 : 5;            
    
    
    
    //----------------------------------------------------------------------------------------------
    // [TX/RX]OUT_DIV - Output Clock Divider
    //----------------------------------------------------------------------------------------------
    localparam OUT_DIV = (PHY_MODE      == 1) ? 1 :
                         (PHY_MAX_SPEED  < 3) ? 2 : 4;  
    
    
    
    //----------------------------------------------------------------------------------------------
    //  [TX/RX]_CLK25_DIV - Clock (25 MHz) Divider
    //----------------------------------------------------------------------------------------------
    localparam CLK25_DIV = (PHY_REFCLK_FREQ == 2) ? 10 : 
                           (PHY_REFCLK_FREQ == 1) ?  5 : 4;
                   
                   
                       
    //----------------------------------------------------------------------------------------------
    //  [TX/RX]_PROGDIV_CFG - Programmable Divider Configuration
    //
    //    Gen1/Gen2 : 250 MHz
    //    Gen3      : 250 or 500 MHz
    //    Gen4      : 500 MHz
    //----------------------------------------------------------------------------------------------
    localparam PROGDIV_CFG = (PHY_MAX_SPEED     < 3) ? 10.0 :                                          
                             (PHY_MAX_SPEED    == 4) ?  4.0 :                                       
                             (PHY_CORECLK_FREQ == 1) ?  8.0 : 4.0;                                 
                       
                       
    
    //----------------------------------------------------------------------------------------------
    //  [TX/RX]PLLCLKSEL - PLL Clock Select   
    //                                                    
    //    2'b00 = CPLL                                                                          
    //    2'b01 = Reserved                                                                          
    //    2'b11 = QPLL0                                                                         
    //    2'b10 = QPLL1                                                                           
    //----------------------------------------------------------------------------------------------
    localparam [ 1:0] PLLCLKSEL = (PHY_MAX_SPEED  < 3) ? 2'b00 : 
                                  (PHY_MAX_SPEED == 3) ? 2'b10 : 2'b11;                                                             
              
                                    
              
    //----------------------------------------------------------------------------------------------
    //  [TX/RX]SYSCLKSEL - System Clock Select   
    //                                                    
    //    2'b00 = CPLL                                                                          
    //    2'b01 = Reserved                                                                          
    //    2'b10 = QPLL0                                                                         
    //    2'b11 = QPLL1                                                                           
    //----------------------------------------------------------------------------------------------                 
    localparam [ 1:0] SYSCLKSEL = (PHY_MAX_SPEED  < 3) ? 2'b00 : 
                                  (PHY_MAX_SPEED == 3) ? 2'b11 : 2'b10;                          
                                  
                                           
                          
     //----------------------------------------------------------------------------------------------
    //  OOBDIVCTL - OOB Divider Control   
    //                                                    
    //    2'd0 = div1                                                                        
    //    2'd1 = div2                                                                        
    //    2'd2 = div4                                                                        
    //    2'd3 = div8                                                                         
    //----------------------------------------------------------------------------------------------                 
    localparam [ 1:0] OOBDIVCTL = (PHY_REFCLK_FREQ == 2) ? 2'd2 : 2'd1; 
                                          
                          
                                                                                                    
    //----------------------------------------------------------------------------------------------
    //  PCIE_PLL_SEL_MODE_GENx - PLL Select Mode for PCIe
    //
    //    2'b00 = CPLL
    //    2'b10 = QPLL0
    //    2'b11 = QPLL1
    //----------------------------------------------------------------------------------------------
    localparam [ 1:0] PCIE_PLL_SEL_MODE_GEN12 = (PHY_MAX_SPEED  < 3) ? 2'b00 : 
                                                (PHY_MAX_SPEED == 3) ? 2'b11 : 2'b10;                 
   
    localparam [ 1:0] PCIE_PLL_SEL_MODE_GEN3  = (PHY_MAX_SPEED  < 3) ? 2'b00 :
                                                (PHY_MAX_SPEED == 3) ? 2'b11 : 2'b10;  
      
    localparam [ 1:0] PCIE_PLL_SEL_MODE_GEN4  = (PHY_MAX_SPEED  < 3) ? 2'b00 :         
                                                (PHY_MAX_SPEED == 3) ? 2'b11 : 2'b10;  
                            
                            
                            
    //----------------------------------------------------------------------------------------------
    //  PCIE_[TX/RX]PMA_CFG - PCIe PMA Configuration    
    //                                         
    //    [   15] : Reserved                                                        
    //    [14:13] : [TX/RX]_INT_DATAWIDTH_G4                                                                    
    //    [12: 9] : [TX/RX]_DATA_WIDTH_G4                                                     
    //    [ 8: 6] : [TX/RX]OUTCLK_DIV_G2                                                        
    //    [ 5: 3] : [TX/RX]OUTCLK_DIV_G3                                                        
    //    [ 2: 0] : [TX/RX]OUTCLK_DIV_G4                                                          
    //----------------------------------------------------------------------------------------------                                                      
    localparam [ 1:0] INT_DATAWIDTH_G4 = 2'd1;
    localparam [ 3:0] DATA_WIDTH_G4    = 4'd4;
    localparam [ 2:0] OUT_DIV_G2       = (PHY_MAX_SPEED  < 3) ? 3'd0 : 3'd1;                                                                                                                                                     
    localparam [ 2:0] OUT_DIV_G3       = (PHY_MAX_SPEED == 4) ? 3'd1 : 3'd0;                                                                                                                                                                    
    localparam [ 2:0] OUT_DIV_G4       = 3'd0;                                                              

    localparam [15:0] PCIE_PMA_CFG = {1'd0,      
                                     INT_DATAWIDTH_G4,                                    
                                     DATA_WIDTH_G4,                                                             
                                     OUT_DIV_G2,                                                 
                                     OUT_DIV_G3,                                                                                              
                                     OUT_DIV_G4};         
    
    
    
    //----------------------------------------------------------------------------------------------
    //  PCIE_BUFG_DIV_CTRL - PCIe BUFG_GT Divider Control
    //
    //    [   15] : BUFG_GT_FSM_CLK
    //    [14:12] : PCLK_DIV_G1
    //    [11:10] : PCLK_DIV_G2  
    //    [ 9: 8] : PCLK_DIV_G3 
    //    [ 7: 6] : PCLK_DIV_G4
    //    [ 5: 0] : Reserved
    //----------------------------------------------------------------------------------------------  
    localparam [ 0:0] BUFG_GT_FSM_CLK    = 1'd0;                                                    // 1'b0 = REFCLK : 1'b1 = PROGDIVCLK
                                                              
    localparam [ 2:0] PCLK_DIV_G1        = (PHY_MODE         == 1) ? 3'd0 :                         // 250 MHz (USB3)
                                           (PHY_MAX_SPEED     < 3) ? 3'd1 :  
                                           (PHY_MAX_SPEED    == 4) ? 3'd3 :                              
                                           (PHY_CORECLK_FREQ == 1) ? 3'd1 : 3'd3;                   // 125 MHz (PCIe)
    
    localparam [ 1:0] PCLK_DIV_G2        = (PHY_MAX_SPEED     < 3) ? 2'd0 : 
                                           (PHY_MAX_SPEED    == 4) ? 2'd1 : 
                                           (PHY_CORECLK_FREQ == 1) ? 2'd0 : 2'd1;                   // 250 MHz
    
    localparam [ 1:0] PCLK_DIV_G3        = PCLK_DIV_G2;                                             // 250 MHz
    
    localparam [ 1:0] PCLK_DIV_G4        = 2'd0;                                                    // 500 MHz
            
    localparam [15:0] PCIE_BUFG_DIV_CTRL = {BUFG_GT_FSM_CLK,                    
                                            PCLK_DIV_G1, 
                                            PCLK_DIV_G2,  
                                            PCLK_DIV_G3,                                                            
                                            PCLK_DIV_G4,
                                            6'd0};
                    
                    
                    
    //----------------------------------------------------------------------------------------------
    //  PCIE_TXPCS_CFG_GEN3 - PCIe TX PCS Configuration
    //                                             
    //    [15:14] : Reserved                                                        
    //    [13:12] : TX_DRIVE_MODE_G3                                                                    
    //    [   11] : ASYNC_EN   
    //    [   10] : TX_XCLK_SEL_G3                                                   
    //    [    9] : TXBUF_EN_G3                                                          
    //    [ 8: 7] : TX_INT_DATAWIDTH_G3
    //    [ 6: 3] : TX_DATA_WIDTH_G3
    //    [    2] : TX_SYNC_MODE
    //    [    1] : DRP_EXT_CTRL                                                         
    //    [    0] : Reserved                                                         
    //----------------------------------------------------------------------------------------------                                                      
    localparam [ 1:0] TX_DRIVE_MODE_G3    = 2'd2;                                      // "PIPEGEN3"
    localparam [ 0:0] ASYNC_EN            = (PHY_REFCLK_MODE != 0) ? 1'd1 : 1'd0;      // 1'b0 = Async : 1'b1 = Sync
    localparam [ 0:0] TX_XCLK_SEL_G3      = 1'd1;                                      // "TXUSER" when bypassing TX buffer                                                                                                                                                     
    localparam [ 0:0] TXBUF_EN_G3         = 1'd0;                                      // "FALSE"                                                                                                                                        
    localparam [ 1:0] TX_INT_DATAWIDTH_G3 = 2'd1;                                      //  4-byte
    localparam [ 3:0] TX_DATA_WIDTH_G3    = 4'd4;                                      // 32-bit 
    localparam [ 0:0] TX_SYNC_MODE        = 1'd1;                                      // Auto 
    localparam [ 0:0] DRP_EXT_CTRL        = 1'd0;                                      // Disable (Advance feature) 
    
    localparam [15:0] PCIE_TXPCS_CFG_GEN3 = {2'd0,
                                             TX_DRIVE_MODE_G3,
                                             ASYNC_EN,
                                             TX_XCLK_SEL_G3,
                                             TXBUF_EN_G3,
                                             TX_INT_DATAWIDTH_G3,
                                             TX_DATA_WIDTH_G3,
                                             TX_SYNC_MODE,
                                             DRP_EXT_CTRL,
                                             1'd0};
    
    
    
    //----------------------------------------------------------------------------------------------
    //  PCIE_RXPCS_CFG_GEN3 - PCIe RX PCS Configuration  
    //                                                                                                  
    //    [   15] : RX_DFE_LPM_HOLD_DURING_EIDLE_G3                                                                 
    //    [   14] : RXCDR_PH_RESET_ON_EIDLE_G3  
    //    [   13] : RXCDR_FR_RESET_ON_EIDLE_G3                                             
    //    [   12] : RXCDR_HOLD_DURING_EIDLE_G3                                                      
    //    [   11] : CLK_CORRECT_USE_G3
    //    [   10] : RX_XCLK_SEL_G3
    //    [    9] : RXBUF_EN_G3
    //    [ 8: 7] : RX_INT_DATA_WIDTH_G3
    //    [ 6: 3] : RX_DATA_WIDTH_G3
    //    [    2] : RX_SYNC_MODE                                                        
    //    [    1] : RATE_FSM_CLK  
    //    [    0] : RXVALID_GATE_G3                                                
    //----------------------------------------------------------------------------------------------                                                      
    localparam [ 0:0] RX_DFE_LPM_HOLD_DURING_EIDLE_G3 = 1'd0;                          // 
    localparam [ 0:0] RXCDR_PH_RESET_ON_EIDLE_G3      = 1'd0;                          // 
    localparam [ 0:0] RXCDR_FR_RESET_ON_EIDLE_G3      = 1'd0;                          //                                                                                                                                          
    localparam [ 0:0] RXCDR_HOLD_DURING_EIDLE_G3      = 1'd0;                          //             
    localparam [ 0:0] CLK_CORRECT_USE_G3              = 1'd1;                          // "TRUE"       
    localparam [ 0:0] RX_XCLK_SEL_G3                  = 1'd0;                          // "RXDES" when using RX buffer                                                                              
    localparam [ 0:0] RXBUF_EN_G3                     = 1'd1;                          // "TRUE"
    localparam [ 1:0] RX_INT_DATA_WIDTH_G3            = 2'd1;                          //  4-byte  
    localparam [ 3:0] RX_DATA_WIDTH_G3                = 4'd4;                          // 32-bit  
    localparam [ 0:0] RX_SYNC_MODE                    = 1'd1;                          // Auto
    localparam [ 0:0] RATE_FSM_CLK                    = 1'd0;                          // 1'b0 = REFCLK : 1'b1 = PCLK
    localparam [ 0:0] RXVALID_GATE_G3                 = 1'd1;
    
    localparam [15:0] PCIE_RXPCS_CFG_GEN3 = {RX_DFE_LPM_HOLD_DURING_EIDLE_G3,
                                             RXCDR_PH_RESET_ON_EIDLE_G3,
                                             RXCDR_FR_RESET_ON_EIDLE_G3,
                                             RXCDR_HOLD_DURING_EIDLE_G3,
                                             CLK_CORRECT_USE_G3,
                                             RX_XCLK_SEL_G3,
                                             RXBUF_EN_G3,
                                             RX_INT_DATA_WIDTH_G3,
                                             RX_DATA_WIDTH_G3,
                                             RX_SYNC_MODE,
                                             RATE_FSM_CLK,
                                             RXVALID_GATE_G3};
    
    //----------------------------------------------------------------------------------------------
    //  PCIe CDR for Gen1/Gen2
    //  USB CDR for Gen1 (5G) uses same setting
    //----------------------------------------------------------------------------------------------   
    localparam [15:0] RXCDR_CFG0      = 16'b0000_0000_0000_0010;
    localparam [15:0] RXCDR_CFG1      = 16'b0000_0000_0000_0000;
    localparam [15:0] RXCDR_CFG2      = (PHY_REFCLK_MODE == 2) ? 16'b0000_0001_1110_0100 : 16'b0000001001011001;
    localparam [15:0] RXCDR_CFG3      = 16'b0000_0000_0001_0010; 
    localparam [15:0] RXCDR_CFG4      = 16'b0101_1100_1111_0110;
    localparam [15:0] RXCDR_CFG5      = 16'b1011_0100_0110_1011;
    
    //----------------------------------------------------------------------------------------------
    //  PCIe CDR for Gen3
    //---------------------------------------------------------------------------------------------- 
    localparam [15:0] RXCDR_CFG0_GEN3 = RXCDR_CFG0;
    localparam [15:0] RXCDR_CFG1_GEN3 = RXCDR_CFG1;
    localparam [15:0] RXCDR_CFG2_GEN3 = (PHY_REFCLK_MODE == 2) ? 16'b0000_0000_0011_0110 : 16'b0000_0000_0011_0100;
    localparam [15:0] RXCDR_CFG3_GEN3 = RXCDR_CFG3; 
    localparam [15:0] RXCDR_CFG4_GEN3 = RXCDR_CFG4;
    localparam [15:0] RXCDR_CFG5_GEN3 = 16'b0001_0100_0110_1011;
    
    //----------------------------------------------------------------------------------------------
    //  PCIe CDR for Gen4
    //---------------------------------------------------------------------------------------------- 
    localparam [15:0] RXCDR_CFG2_GEN4 = (PHY_REFCLK_MODE == 2) ? 16'b0000_0000_0100_0110 : 16'b0000_0000_0011_0100;          
    localparam [15:0] RXCDR_CFG3_GEN4 = RXCDR_CFG4_GEN3;

    //----------------------------------------------------------------------------------------------
    //  PCIe RX Buffer for Gen1/Gen2
    //----------------------------------------------------------------------------------------------  
    localparam [5:0] PCIE_CLK_COR_MAX_LAT     = (PHY_REFCLK_MODE == 2) ? 6'd28 : (PHY_REFCLK_MODE == 1) ? 6'd20 : 6'd20;
    localparam [5:0] PCIE_CLK_COR_MIN_LAT     = (PHY_REFCLK_MODE == 2) ? 6'd22 : (PHY_REFCLK_MODE == 1) ? 6'd17 : 6'd4;
    localparam [5:0] PCIE_RXBUF_THRESH_OVFLW  = (PHY_REFCLK_MODE == 2) ? 6'd63 : (PHY_REFCLK_MODE == 1) ? 6'd31 : 6'd31;
    localparam [5:0] PCIE_RXBUF_THRESH_UNDFLW = (PHY_REFCLK_MODE == 2) ? 6'd8  : (PHY_REFCLK_MODE == 1) ? 6'd8  : 6'd1;
    
    //----------------------------------------------------------------------------------------------
    //  PCIe RX Buffer for Gen3/Gen4
    //----------------------------------------------------------------------------------------------  
    localparam [4:0] PCIE3_CLK_COR_EMPTY_THRSH = 5'd0;
    localparam [5:0] PCIE3_CLK_COR_FULL_THRSH  = (PHY_REFCLK_MODE == 2) ? 6'd32 : (PHY_REFCLK_MODE == 1) ? 6'd16 : 6'd16;
    localparam [4:0] PCIE3_CLK_COR_MAX_LAT     = (PHY_REFCLK_MODE == 2) ? 5'd16 : (PHY_REFCLK_MODE == 1) ? 5'd8  : 5'd4;
    localparam [4:0] PCIE3_CLK_COR_MIN_LAT     = (PHY_REFCLK_MODE == 2) ? 5'd12 : (PHY_REFCLK_MODE == 1) ? 5'd4  : 5'd0;
    localparam [5:0] PCIE3_CLK_COR_THRSH_TIMER = (PHY_REFCLK_MODE == 2) ? 6'd4  : (PHY_REFCLK_MODE == 1) ? 6'd8  : 6'd8;
    
    //----------------------------------------------------------------------------------------------
    //  TX Electrical Idle Attributes for USB3 and PCIe
    //---------------------------------------------------------------------------------------------- 
    localparam [ 2:0]  TX_EIDLE_ASSERT_DELAY   = (PHY_MODE == 1) ? 3'd0 : 3'd4;
    localparam [ 2:0]  TX_EIDLE_DEASSERT_DELAY = (PHY_MODE == 1) ? 3'd1 : 3'd3;
    
    //----------------------------------------------------------------------------------------------
    //  Comma Align and Detect Attributres for USB3 and PCIe                                                                  
    //----------------------------------------------------------------------------------------------     
    localparam         ALIGN_COMMA_DOUBLE  = (PHY_MODE == 1) ? "TRUE" : "FALSE";                      
    localparam         SHOW_REALIGN_COMMA  = (PHY_MODE == 1) ? "TRUE" : "FALSE";  
    
    //----------------------------------------------------------------------------------------------
    //  Clock Correction Attributes for USB3 and PCIe
    //----------------------------------------------------------------------------------------------
    localparam [ 5:0]  CLK_COR_MAX_LAT      = (PHY_MODE == 1) ?  6'd16        : PCIE_CLK_COR_MAX_LAT;
    localparam [ 5:0]  CLK_COR_MIN_LAT      = (PHY_MODE == 1) ?  6'd13        : PCIE_CLK_COR_MIN_LAT;
    localparam         CLK_COR_KEEP_IDLE    = (PHY_MODE == 1) ? "FALSE"       : "TRUE";
    localparam [ 9:0]  CLK_COR_SEQ_1_1      = (PHY_MODE == 1) ? 10'b100111100 : 10'b0100011100;
    localparam [ 9:0]  CLK_COR_SEQ_1_2      = (PHY_MODE == 1) ? 10'b100111100 : 10'b0000000000;
    localparam [ 3:0]  CLK_COR_SEQ_2_ENABLE = (PHY_MODE == 1) ?  4'b0000      :  4'b1111;
    localparam [ 1:0]  CLK_COR_SEQ_LEN      = (PHY_MODE == 1) ? 2             : 1;

    //----------------------------------------------------------------------------------------------
    //  RX Buffer Attributes for USB3 and PCIe                                                                  
    //----------------------------------------------------------------------------------------------
    localparam [ 5:0]  RXBUF_THRESH_OVFLW  = (PHY_MODE == 1) ? 32 : PCIE_RXBUF_THRESH_OVFLW;                                                            
    localparam [ 5:0]  RXBUF_THRESH_UNDFLW = (PHY_MODE == 1) ?  6 : PCIE_RXBUF_THRESH_UNDFLW;                                    
    
    //----------------------------------------------------------------------------------------------
    //  RX Common Mode Select for USB3 and PCIe        
    //
    //    0 = AVTT
    //    1 = GND
    //    2 = Floating
    //    3 = Programmable                                                         
    //----------------------------------------------------------------------------------------------
    localparam integer RX_CM_SEL = (PHY_MODE == 1) ?  1 : 3;   
   
    //----------------------------------------------------------------------------------------------
    //  GT Attributes for USB3 and PCIe                                                                  
    //----------------------------------------------------------------------------------------------  
    localparam         SIM_TX_EIDLE_DRIVE_LEVEL = (PHY_MODE == 1) ? "Z"   : "LOW";    
    localparam         RXSLIDE_MODE             = (PHY_MODE == 1) ? "OFF" : "PMA";   

    //----------------------------------------------------------------------------------------------
    //  Reserved Attributes for USB3 and PCIe                                                                  
    //----------------------------------------------------------------------------------------------      
    localparam [ 8:0]  USB_LFPS_DET      = (PHY_REFCLK_FREQ == 0) ? 9'b011001001 : 9'b011001010; 
    localparam         RXTERMINATION_DRP = 1'd1;
    localparam [ 1:0]  RX_CM_SEL_USB     = 2'd3;
    
    localparam [15:0]  PCS_RSVD0         = {USB_LFPS_DET, 2'b11, (PHY_GEN4_EIEOS==1) ? 1'b1:1'b0, 1'b0, RXTERMINATION_DRP, RX_CM_SEL_USB};
        
    //----------------------------------------------------------------------------------------------
    //  Other Attributes based on latest 2015.3 rules                                                                 
    //----------------------------------------------------------------------------------------------   
    localparam [3:0]   RX_SUM_VCMTUNE    = (PHY_MODE         == 1) ? 4'b0110 : 
                                           (PHY_MAX_SPEED     < 3) ? 4'b0110 : 4'b1010; 
                                           
    localparam [3:0]   RX_SUM_IREF_TUNE  = (PHY_MODE         == 1) ? 4'b0100 : 
                                           (PHY_MAX_SPEED     < 3) ? 4'b0100 : 4'b1001; 
                                           
    localparam         RXDFE_PWR_SAVING  = (PHY_MODE         == 1) ? 1'b0 :
                                           (PHY_MAX_SPEED    == 4) ? 1'b1 : 1'b0;
                                           
    localparam         TX_PI_BIASSET     = (PHY_MODE         == 1) ? 0 :
                                           (PHY_MAX_SPEED     < 3) ? 0 :
                                           (PHY_MAX_SPEED    == 3) ? 1 : 3;
    
    localparam  [15:0] RXPI_CFG0         = (PHY_MODE         == 1) ? 16'h1200 :
                                           (PHY_MAX_SPEED     < 3) ? 16'h1200 :
                                           (PHY_MAX_SPEED    == 3) ? 16'h2202 : 16'b0000000100000100;
//--------------------------------------------------------------------------------------------------
//  GT Channel
//--------------------------------------------------------------------------------------------------
generate
  if (PHY_GT_XCVR == "GTY" || PHY_GT_XCVR == "GTY64") begin: GTY_CHANNEL
//--------------------------------------------------------------------------------------------------
//  GTY Channel
//--------------------------------------------------------------------------------------------------
GTYE4_CHANNEL #
(  
    //----------------------------------------------------------------------------------------------
    //  Simulation Attributes
    //----------------------------------------------------------------------------------------------
    .SIM_MODE                           ("FAST"),                                    
    .SIM_RECEIVER_DETECT_PASS           ("TRUE"),
    .SIM_RESET_SPEEDUP                  ("TRUE"),
    .SIM_TX_EIDLE_DRIVE_LEVEL           (SIM_TX_EIDLE_DRIVE_LEVEL),
    .SIM_DEVICE                         ("ULTRASCALE_PLUS"),                             
   
    //----------------------------------------------------------------------------------------------     
    //  Clock Attributes
    //----------------------------------------------------------------------------------------------                       
    .TXREFCLKDIV2_SEL                   ( 1'b0),                              
    .RXREFCLKDIV2_SEL                   ( 1'b0),                                
    .TX_CLK25_DIV                       (CLK25_DIV),                                                    
    .RX_CLK25_DIV                       (CLK25_DIV),                                                    
    .TX_CLKMUX_EN                       ( 1'b1),                                                
    .RX_CLKMUX_EN                       ( 1'b1),                                                
    .TX_XCLK_SEL                        ("TXUSR"),                                              
    .RX_XCLK_SEL                        ("RXDES"),   
    .TXOUT_DIV                          (OUT_DIV), 
    .RXOUT_DIV                          (OUT_DIV), 
    .LOCAL_MASTER                       (LOCAL_MASTER),   
    .RX_CLK_SLIP_OVRD                   ( 5'b00000),  
    .RXPMACLK_SEL                       ("DATA"),                                                                                                                           
    .USE_PCS_CLK_PHASE_SEL              ( 1'b0),           
   
    //----------------------------------------------------------------------------------------------     
    //  Programmable Divider Attributes
    //----------------------------------------------------------------------------------------------                                                                                                                       
    .TX_PROGCLK_SEL                     ("CPLL"),                               
    .TX_PROGDIV_CFG                     (PROGDIV_CFG),                      
    .RX_PROGDIV_CFG                     (PROGDIV_CFG),   
    .TX_PROGDIV_RATE                    (16'h0001),                          
    .RX_PROGDIV_RATE                    (16'h0001),                                   
               
    //----------------------------------------------------------------------------------------------
    //  CPLL Attributes
    //----------------------------------------------------------------------------------------------                 
    .CPLL_CFG0                          (16'h0000), //(16'h20FA),                             // Optimize for PCIe PLL compliance   [Changed for extracted model]
    .CPLL_CFG1                          (16'h81E4), //(16'h24AA),               [Changed for extracted model]
    .CPLL_CFG2                          (16'hF007),                             
    .CPLL_CFG3                          ( 6'h00),  
    .CPLL_FBDIV                         (CPLL_FBDIV),  
    .CPLL_FBDIV_45                      (CPLL_FBDIV_45),    
    .CPLL_INIT_CFG0                     (16'h001E),                
    .CPLL_LOCK_CFG                      (16'h01EC), //(16'h01E8),                             // Bit[0] must be LOW   [Changed for extracted model]
    .CPLL_REFCLK_DIV                    ( 1),     
             
    //----------------------------------------------------------------------------------------------
    //  Reset Attributes
    //----------------------------------------------------------------------------------------------                
    //.RESET_POWERSAVE_DISABLE            ( 1'b0),   
                                                                              
    //----------------------------------------------------------------------------------------------
    //  Reset Time Attributes
    //----------------------------------------------------------------------------------------------    
    .TX_DIVRESET_TIME                   ( 5'b00001),
    .TXPCSRESET_TIME	                ( 5'b00001),
    .TXPMARESET_TIME	                ( 5'b00001),
    .RX_DIVRESET_TIME                   ( 5'b00001),
    .RXBUFRESET_TIME                    ( 5'b00001),
    .RXCDRFREQRESET_TIME                ( 5'b10000), //( 5'b00001),  [Changed for extracted model]
    .RXCDRPHRESET_TIME                  ( 5'b00001),    
    .RXDFELPMRESET_TIME                 ( 7'b0001111),    
    .RXISCANRESET_TIME	                ( 5'b00001), 
    .RXOSCALRESET_TIME	                ( 5'b00011), 
    .RXPCSRESET_TIME	                  ( 5'b00001),   
    .RXPMARESET_TIME	                  ( 5'b00001),   
               
    //----------------------------------------------------------------------------------------------
    //  PCIe Attributes
    //----------------------------------------------------------------------------------------------
    .PCIE_GEN4_64BIT_INT_EN             (PHY_GEN4_64BIT_EN),  // THIS ATTRIBUTE IS NEW AND MAY NOT BE AVAILABLE IN EARLY GT MODELS
    .PCIE_BUFG_DIV_CTRL                 (PCIE_BUFG_DIV_CTRL),                  
    .PCIE_RXPCS_CFG_GEN3                (PCIE_RXPCS_CFG_GEN3),                 
    .PCIE_RXPMA_CFG                     (PCIE_PMA_CFG),                        
    .PCIE_TXPCS_CFG_GEN3                (PCIE_TXPCS_CFG_GEN3),                 
    .PCIE_TXPMA_CFG                     (PCIE_PMA_CFG),                        
    .PCS_PCIE_EN                        (PCS_PCIE_EN),  
    .PCIE_PLL_SEL_MODE_GEN12            (PCIE_PLL_SEL_MODE_GEN12),                  
    .PCIE_PLL_SEL_MODE_GEN3             (PCIE_PLL_SEL_MODE_GEN3),  
    .PCIE_PLL_SEL_MODE_GEN4             (PCIE_PLL_SEL_MODE_GEN4),

    //---------------------------------------------------------------------------------------------- 
    //  Data Width Attributes
    //----------------------------------------------------------------------------------------------                          
    .TX_DATA_WIDTH                      (20),                                                                                                                                         
    .RX_DATA_WIDTH                      (20),  
    .TX_INT_DATAWIDTH                   ( 0),                                                                
    .RX_INT_DATAWIDTH                   ( 0),   
    .TX_FABINT_USRCLK_FLOP              ( 1'b0), 
    .RX_FABINT_USRCLK_FLOP              ( 1'b0),                                                    
              
    //----------------------------------------------------------------------------------------------
    //  Analog Front End Attributes
    //----------------------------------------------------------------------------------------------
    .LPBK_BIAS_CTRL	                    ( 3'b000),                           
    .LPBK_EN_RCAL_B	                    ( 1'b0),                             
    .LPBK_EXT_RCAL	                    ( 4'b0000),                          
    .LPBK_RG_CTRL	                      ( 4'b0000),                             
    .RX_AFE_CM_EN                       ( 1'b0),
    .RX_BIAS_CFG0                       (16'h1534),
    .RX_CM_BUF_CFG                      ( 4'b1010),
    .RX_CM_BUF_PD                       ( 1'b0),                                           
    .RX_CM_SEL                          (RX_CM_SEL),                                                        
    .RX_CM_TRIM                         (10),    
    .RX_TUNE_AFE_OS                     ( 2'b00),
    .TERM_RCAL_CFG                      (15'b100001000010000),                                     
    .TERM_RCAL_OVRD                     ( 3'b000),             
                                                                                                    
    //----------------------------------------------------------------------------------------------  
    //  Receiver Detection Attributes
    //----------------------------------------------------------------------------------------------                                      
    .TX_RXDETECT_CFG                    (14'h0032),                                                      
    .TX_RXDETECT_REF                    (3),                                  
    
    //----------------------------------------------------------------------------------------------  
    //  TX Electrical Idle Attributes
    //----------------------------------------------------------------------------------------------   
    .TX_EIDLE_ASSERT_DELAY              (TX_EIDLE_ASSERT_DELAY),                            
    .TX_EIDLE_DEASSERT_DELAY            (TX_EIDLE_DEASSERT_DELAY),             
    .TX_IDLE_DATA_ZERO                  ( 1'b0),                                // Optimized for PCIe      
 
    //----------------------------------------------------------------------------------------------  
    //  RX OOB Attributes
    //----------------------------------------------------------------------------------------------   
    .OOB_PWRUP                          ( 1'b1),                                
    .OOBDIVCTL                          (OOBDIVCTL),                                            
    .RX_SIG_VALID_DLY                   ( 4),                                   // Optimized for PCIe
    .RXOOB_CFG                          ( 9'b000000110),                          
    .RXOOB_CLK_CFG                      ("PMA"),      
    
    //----------------------------------------------------------------------------------------------  
    //  RX Electrical Idle Attributes
    //----------------------------------------------------------------------------------------------                                                   
    .RX_DFE_LPM_HOLD_DURING_EIDLE       ( 1'b0),                                
    .RXBUF_EIDLE_HI_CNT                 ( 4'b0100),                             // Optimized for PCIe
    .RXBUF_EIDLE_LO_CNT                 ( 4'b0000),
    .RXBUF_RESET_ON_EIDLE               ("TRUE"),
    .RXCDR_FR_RESET_ON_EIDLE            ( 1'b0),
    .RXCDR_PH_RESET_ON_EIDLE            ( 1'b0),
    .RXCDR_HOLD_DURING_EIDLE            ( 1'b0),                                // Optimized for PCIe
    .RXELECIDLE_CFG                     ("SIGCFG_1"),                           // Optimized for PCIe
 
    //----------------------------------------------------------------------------------------------  
    //  Power Down Attributes
    //----------------------------------------------------------------------------------------------   
    .PD_TRANS_TIME_FROM_P2              (12'h03C),                                                     
    .PD_TRANS_TIME_NONE_P2              ( 8'h19),                                                      
    .PD_TRANS_TIME_TO_P2                ( 8'h64),   
    .TX_PMA_POWER_SAVE                  ( 1'b0),   
    .RX_PMA_POWER_SAVE                  ( 1'b0),                               
  
    //----------------------------------------------------------------------------------------------  
    //  Rate Change Attributes
    //---------------------------------------------------------------------------------------------- 
    .RATE_SW_USE_DRP                    ( 1'b0),                                // Advance PCIe feature
    .TRANS_TIME_RATE                    ( 8'h0E),             
    .TXBUF_RESET_ON_RATE_CHANGE         ("TRUE"),                              
    .RXBUF_RESET_ON_RATE_CHANGE         ("TRUE"),                              

    //----------------------------------------------------------------------------------------------
    //  TX Driver Attributes
    //----------------------------------------------------------------------------------------------                                   
    .TX_DEEMPH0                         ( 6'b010100),                           // -6.0 dB 
    .TX_DEEMPH1                         ( 6'b001101),                           // -3.5 dB
    .TX_DEEMPH2                         ( 6'b000000),                           //  0.0 dB 
    .TX_DEEMPH3                         ( 6'b000000),                           //  0.0 dB  
    .TX_DRIVE_MODE                      ("PIPE"),                                
    .TX_LOOPBACK_DRIVE_HIZ              ("FALSE"),                   
    .TX_MAINCURSOR_SEL                  ( 1'b0),   
    .TX_MARGIN_FULL_0                   ( 7'b1001111),                          // 1200 mV
    .TX_MARGIN_FULL_1                   ( 7'b1001110),                          // 1100 mV
    .TX_MARGIN_FULL_2                   ( 7'b1001100),                          // 1000 mV 
    .TX_MARGIN_FULL_3                   ( 7'b1001010),                          //  900 mV
    .TX_MARGIN_FULL_4                   ( 7'b1001000),                          //  800 mV
    .TX_MARGIN_LOW_0                    ( 7'b1000110),                          //  700 mV            
    .TX_MARGIN_LOW_1                    ( 7'b1000101),                          //  600 mV           
    .TX_MARGIN_LOW_2                    ( 7'b1000011),                          //  500 mV          
    .TX_MARGIN_LOW_3                    ( 7'b1000010),                          //  400 mV           
    .TX_MARGIN_LOW_4                    ( 7'b1000000),                          //  300 mV                               
   
    //----------------------------------------------------------------------------------------------    
    //  Comma Align & Detect Attributes
    //----------------------------------------------------------------------------------------------       
    .ALIGN_COMMA_DOUBLE                 (ALIGN_COMMA_DOUBLE),                                                  
    .ALIGN_COMMA_ENABLE                 (10'b1111111111),                                           
    .ALIGN_COMMA_WORD                   ( 1),                                                       
    .ALIGN_MCOMMA_DET                   ("TRUE"),                                                   
    .ALIGN_MCOMMA_VALUE                 (10'b1010000011),                                           
    .ALIGN_PCOMMA_DET                   ("TRUE"),                                                   
    .ALIGN_PCOMMA_VALUE                 (10'b0101111100),                                           
    .DEC_MCOMMA_DETECT                  ("TRUE"),                                                      
    .DEC_PCOMMA_DETECT                  ("TRUE"),                                                      
    .DEC_VALID_COMMA_ONLY               ("FALSE"),                                                     
    .SHOW_REALIGN_COMMA                 (SHOW_REALIGN_COMMA),       
   
    //----------------------------------------------------------------------------------------------   
    //  8B/10B Attributes                                                                             
    //----------------------------------------------------------------------------------------------                   
    .RX_DISPERR_SEQ_MATCH               ("TRUE"),        
   
    //----------------------------------------------------------------------------------------------  
    //  TX Buffer Attributes
    //----------------------------------------------------------------------------------------------                      
    .TX_FIFO_BYP_EN                     ( 1'b1),                                
    .TXBUF_EN                           ("FALSE"),        
    .TXFIFO_ADDR_CFG                    ("LOW"),                                                                                      
 
    //----------------------------------------------------------------------------------------------
    //  RX Buffer Attributes                                                                        
    //----------------------------------------------------------------------------------------------     
    .RXBUF_ADDR_MODE                    ("FULL"),                               
    .RXBUF_EN                           ("TRUE"),
    .RXBUF_RESET_ON_CB_CHANGE           ("TRUE"),
    .RXBUF_RESET_ON_COMMAALIGN          ("FALSE"),
    .RXBUF_THRESH_OVFLW                 (RXBUF_THRESH_OVFLW),                                                      
    .RXBUF_THRESH_OVRD                  ("TRUE"),                             
    .RXBUF_THRESH_UNDFLW                (RXBUF_THRESH_UNDFLW),                                    
    .RX_BUFFER_CFG                      ( 6'b000000),
    .RX_DEFER_RESET_BUF_EN              ("TRUE"), 
   
    //----------------------------------------------------------------------------------------------   
    //  PCIe Gen3 RX Buffer Attributes                                                                                   
    //----------------------------------------------------------------------------------------------   
    .PCI3_AUTO_REALIGN                  ("OVR_1K_BLK"),                           
    .PCI3_PIPE_RX_ELECIDLE              ( 1'b0),                                
    .PCI3_RX_ASYNC_EBUF_BYPASS          ( 2'b00),                               
    .PCI3_RX_ELECIDLE_EI2_ENABLE        ( 1'b0),                                
    .PCI3_RX_ELECIDLE_H2L_COUNT         ( 6'b000000),                           
    .PCI3_RX_ELECIDLE_H2L_DISABLE       ( 3'b000),                              
    .PCI3_RX_ELECIDLE_HI_COUNT          ( 6'b000000),                           
    .PCI3_RX_ELECIDLE_LP4_DISABLE       ( 1'b0),                                
    .PCI3_RX_FIFO_DISABLE               ( 1'b0),                                
       
    //----------------------------------------------------------------------------------------------   
    //  PCIe Gen3 Clock Correction Attributes                                                                                   
    //----------------------------------------------------------------------------------------------          
    .PCIE3_CLK_COR_EMPTY_THRSH             (PCIE3_CLK_COR_EMPTY_THRSH),                           
    .PCIE3_CLK_COR_FULL_THRSH              (PCIE3_CLK_COR_FULL_THRSH),                          
    .PCIE3_CLK_COR_MAX_LAT                 (PCIE3_CLK_COR_MAX_LAT),                          
    .PCIE3_CLK_COR_MIN_LAT                 (PCIE3_CLK_COR_MIN_LAT),                          
    .PCIE3_CLK_COR_THRSH_TIMER             (PCIE3_CLK_COR_THRSH_TIMER),                      
       
    //---------------------------------------------------------------------------------------------- 
    //  Clock Correction Attributes
    //----------------------------------------------------------------------------------------------             
    .CBCC_DATA_SOURCE_SEL               ("DECODED"),  
    .CLK_COR_KEEP_IDLE                  (CLK_COR_KEEP_IDLE),
    .CLK_COR_MAX_LAT                    (CLK_COR_MAX_LAT),                                   
    .CLK_COR_MIN_LAT                    (CLK_COR_MIN_LAT),                                  
    .CLK_COR_PRECEDENCE                 ("TRUE"),
    .CLK_COR_REPEAT_WAIT                (0),
    .CLK_COR_SEQ_1_1                    (CLK_COR_SEQ_1_1),
    .CLK_COR_SEQ_1_2                    (CLK_COR_SEQ_1_2),
    .CLK_COR_SEQ_1_3                    (10'b0000000000),
    .CLK_COR_SEQ_1_4                    (10'b0000000000),
    .CLK_COR_SEQ_1_ENABLE               (4'b1111),
    .CLK_COR_SEQ_2_1                    (10'b0000000000),
    .CLK_COR_SEQ_2_2                    (10'b0000000000),
    .CLK_COR_SEQ_2_3                    (10'b0000000000),
    .CLK_COR_SEQ_2_4                    (10'b0000000000),
    .CLK_COR_SEQ_2_ENABLE               (CLK_COR_SEQ_2_ENABLE),
    .CLK_COR_SEQ_2_USE                  ("FALSE"),
    .CLK_COR_SEQ_LEN                    (CLK_COR_SEQ_LEN),
    .CLK_CORRECT_USE                    ("TRUE"),                
       
    //---------------------------------------------------------------------------------------------- 
    //  FTS Deskew Attributes                                                                            
    //----------------------------------------------------------------------------------------------                                         
    .FTS_DESKEW_SEQ_ENABLE              ( 4'b1111),                                        
    .FTS_LANE_DESKEW_CFG                ( 4'b1111),                                          
    .FTS_LANE_DESKEW_EN                 ("FALSE"),           
       
    //---------------------------------------------------------------------------------------------- 
    //  Channel Bonding Attributes (Disabled)
    //----------------------------------------------------------------------------------------------          
    .CHAN_BOND_KEEP_ALIGN               ("FALSE"),
    .CHAN_BOND_MAX_SKEW                 ( 1),
    .CHAN_BOND_SEQ_1_1                  (10'b0000000000),
    .CHAN_BOND_SEQ_1_2                  (10'b0000000000),
    .CHAN_BOND_SEQ_1_3                  (10'b0000000000),
    .CHAN_BOND_SEQ_1_4                  (10'b0000000000),
    .CHAN_BOND_SEQ_1_ENABLE             ( 4'b1111),
    .CHAN_BOND_SEQ_2_1                  (10'b0000000000),
    .CHAN_BOND_SEQ_2_2                  (10'b0000000000),
    .CHAN_BOND_SEQ_2_3                  (10'b0000000000),
    .CHAN_BOND_SEQ_2_4                  (10'b0000000000),  
    .CHAN_BOND_SEQ_2_ENABLE             ( 4'b1111),
    .CHAN_BOND_SEQ_2_USE                ("FALSE"), 
    .CHAN_BOND_SEQ_LEN                  ( 1),                                                           
  
    //----------------------------------------------------------------------------------------------            
    //  TX Sync Alignment Attributes                                                                              
    //----------------------------------------------------------------------------------------------     
    .TXDLY_CFG                          (16'b0000000000011111),    
    .TXDLY_LCFG                         (16'b0000000001010000),                
    .TXPH_CFG                           (16'b0000000100000011),
    .TXPH_CFG2                          (16'b0000000000000000),                 
    .TXPH_MONITOR_SEL                   ( 5'b00000),
    .TXPHDLY_CFG0                       (16'b0110000000100000),                 
    .TXPHDLY_CFG1                       (16'b0000000000000010),              
                                                                                    
    //----------------------------------------------------------------------------------------------            
    //  TX Auto Sync Alignment Attributes                                                                               
    //----------------------------------------------------------------------------------------------                
    .TXSYNC_MULTILANE                   (MULTI_LANE),                                                                                                              
    .TXSYNC_OVRD                        (1'b0),                                 // Select auto TXSYNC mode                                                                                 
    .TXSYNC_SKIP_DA                     (1'b0),                     
                                                                                                    
    //----------------------------------------------------------------------------------------------            
    //  RX Sync Alignment Attributes (Not used)                                                                             
    //----------------------------------------------------------------------------------------------    
  //.RXDLY_CFG                          (16'h001F),   
  //.RXDLY_LCFG                         (16'h0030),   
  //.RXPH_MONITOR_SEL                   (5'b00000),
  //.RXPHBEACON_CFG                     (16'h0000),
  //.RXPHDLY_CFG                        (16'h2020),
  //.RXPHSAMP_CFG                       (16'h2100),
  //.RXPHSLIP_CFG                       (16'h9933),                             
     
    //----------------------------------------------------------------------------------------------            
    //  RX Auto Sync Alignment Attributes (Not used)                                                                                
    //----------------------------------------------------------------------------------------------                
  //.RXSYNC_MULTILANE                   (1'b0),                                                                                                              
  //.RXSYNC_OVRD                        (1'b0),                                                                                         
  //.RXSYNC_SKIP_DA                     (1'b0),                   
  
    //----------------------------------------------------------------------------------------------  
    //  Gearbox Attributes (Not used)                                                                
    //---------------------------------------------------------------------------------------------- 
  //.GEARBOX_MODE                       ( 5'b00000), 
  //.TX_SAMPLE_PERIOD                   ( 3'b101),
  //.RX_SAMPLE_PERIOD                   ( 3'b101),
  //.TXGEARBOX_EN                       ("FALSE"),
  //.RXGEARBOX_EN                       ("FALSE"),    
  //.TXGBOX_FIFO_INIT_RD_ADDR           ( 4),
  //.RXGBOX_FIFO_INIT_RD_ADDR           ( 4),
  //.RXSLIDE_AUTO_WAIT                  ( 7),                                                         
    .RXSLIDE_MODE                       (RXSLIDE_MODE),                          

    //----------------------------------------------------------------------------------------------
    //  PCS Reserved Attributes
    //----------------------------------------------------------------------------------------------
    .PCS_RSVD0                          (PCS_RSVD0),
  
    //----------------------------------------------------------------------------------------------  
    //  PMA Reserved Attributes
    //----------------------------------------------------------------------------------------------      
    .TX_PMA_RSV0                        (16'h000A),                             
    .RX_PMA_RSV0                        (16'h00E0),                                        
      
    //----------------------------------------------------------------------------------------------
    //  CFOK Attributes                                                                 
    //----------------------------------------------------------------------------------------------              
    .RXCFOK_CFG0                        (16'b0011_1110_0000_0000),
    .RXCFOK_CFG1                        (16'b0000_0000_0100_0010),
    .RXCFOK_CFG2                        (16'b0000_0000_0010_1101),

    //----------------------------------------------------------------------------------------------
    //  RX CTLE
    //----------------------------------------------------------------------------------------------  
    .CTLE3_OCAP_EXT_CTRL	              ( 3'b000),                           
    .CTLE3_OCAP_EXT_EN	                ( 1'b0),                                
    .RX_EN_CTLE_RCAL_B                  ( 1'b0),                              

    //----------------------------------------------------------------------------------------------    
    //  RX LPM Attributes
    //----------------------------------------------------------------------------------------------        
    .RXLPM_CFG                          (16'b0000_0000_0000_0000),    
    .RXLPM_GC_CFG                       (16'b0000_0010_0000_0000),
    .RXLPM_KH_CFG0                      (16'b0000_0000_0000_0000),
    .RXLPM_KH_CFG1                      (16'b0000_0000_0000_0010),
    .RXLPM_OS_CFG0                      (16'b0000_0100_0000_0000),
    .RXLPM_OS_CFG1                      (16'b0000_0000_0000_0000),
 
    //----------------------------------------------------------------------------------------------    
    //  RX DFE Attributes
    //----------------------------------------------------------------------------------------------       
    .RXDFE_CFG0                         (16'b0100_1100_0000_0000), //(16'b0000110000000000),    [Changed for extracted model]
    .RXDFE_CFG1                         (16'b0000_0000_0000_0000),
    .RXDFE_GC_CFG0                      (16'b0001_1110_0000_0000), 
    .RXDFE_GC_CFG1                      (16'b0001_1001_0000_0000),  // different from GTH 
    .RXDFE_GC_CFG2                      (16'b0000_0000_0000_0000),  // different from GTH
    .RXDFE_H2_CFG0                      (16'b0000_0000_0000_0000),
    .RXDFE_H2_CFG1                      (16'b0000_0000_0000_0010),
    .RXDFE_H3_CFG0                      (16'b0000_0000_0000_0000),
    .RXDFE_H3_CFG1                      (16'b0000_0000_0000_0010),
    .RXDFE_H4_CFG0                      (16'b0000_0000_0000_0000),
    .RXDFE_H4_CFG1                      (16'b0000_0000_0000_0011),
    .RXDFE_H5_CFG0                      (16'b0000_0000_0000_0000),
    .RXDFE_H5_CFG1                      (16'b0000_0000_0000_0010),
    .RXDFE_H6_CFG0                      (16'b0000_0000_0000_0000),
    .RXDFE_H6_CFG1                      (16'b0000_0000_0000_0010),
    .RXDFE_H7_CFG0                      (16'b0000_0000_0000_0000),
    .RXDFE_H7_CFG1                      (16'b0000_0000_0000_0010), 
    .RXDFE_H8_CFG0                      (16'b0000_0000_0000_0000),
    .RXDFE_H8_CFG1                      (16'b0000_0000_0000_0010),
    .RXDFE_H9_CFG0                      (16'b0000_0000_0000_0000),
    .RXDFE_H9_CFG1                      (16'b0000_0000_0000_0010), 
    .RXDFE_HA_CFG0                      (16'b0000_0000_0000_0000),
    .RXDFE_HA_CFG1                      (16'b0000_0000_0000_0010),
    .RXDFE_HB_CFG0                      (16'b0000_0000_0000_0000), //(16'b0010000000000000),    [Changed for extracted model]
    .RXDFE_HB_CFG1                      (16'b0000_0000_0000_0010),
    .RXDFE_HC_CFG0                      (16'b0000_0000_0000_0000),
    .RXDFE_HC_CFG1                      (16'b0000_0000_0000_0010),
    .RXDFE_HD_CFG0                      (16'b0000_0000_0000_0000),
    .RXDFE_HD_CFG1                      (16'b0000_0000_0000_0010),
    .RXDFE_HE_CFG0                      (16'b0000_0000_0000_0000),
    .RXDFE_HE_CFG1                      (16'b0000_0000_0000_0010),
    .RXDFE_HF_CFG0                      (16'b0000_0000_0000_0000),
    .RXDFE_HF_CFG1                      (16'b0000_0000_0000_0010),
    .RXDFE_OS_CFG0                      (16'b0000_0000_0000_0000),
    .RXDFE_OS_CFG1                      (16'b0000_0000_0000_0010), //(16'b0000001000000000),    [Changed for extracted model]
    //.RXDFE_PWR_SAVING                   (16'b0),
    .RXDFE_UT_CFG0                      (16'b0000_0000_0000_0000),
    .RXDFE_UT_CFG1                      (16'b0000_0000_0000_0010),
    .RXDFE_VP_CFG0                      (16'b0000_0000_0000_0000),
    .RXDFE_VP_CFG1                      (16'b0000_0000_0010_0010),
    .RXDFELPM_KL_CFG0                   (16'h0000),                  
    .RXDFELPM_KL_CFG1                   (16'h0022),             
    .RXDFELPM_KL_CFG2                   (16'h0100),                        
    //.RX_DFE_AGC_CFG0                    ( 2'b00),                               
    .RX_DFE_AGC_CFG1                    ( 2),  
    .RX_DFE_KL_LPM_KH_CFG0              ( 1),
    .RX_DFE_KL_LPM_KH_CFG1              ( 2),
    .RX_DFE_KL_LPM_KL_CFG0              ( 2'b01),
    .RX_DFE_KL_LPM_KL_CFG1              ( 3'b010),   
    .RX_DFELPM_CFG0                     ( 0),                                                            
    .RX_DFELPM_CFG1                     ( 1'b1),                                                               
    .RX_DFELPM_KLKH_AGC_STUP_EN         ( 1'b1),   
          
    //----------------------------------------------------------------------------------------------  
    //  TX PI attributes
    //----------------------------------------------------------------------------------------------
    .TX_PHICAL_CFG0	                    (16'h0000),                           
    .TX_PHICAL_CFG1	                    (16'h7e00),
    //.TX_PHICAL_CFG2	                    (16'h0000),
    .TX_PI_BIASSET	                    ( 0),                                  
    .TXPI_CFG0                          ( 2'b00),
    .TXPI_CFG1                          ( 2'b00),
    //.TXPI_CFG2                          ( 2'b00),
    //.TXPI_CFG3                          ( 1'b0),
    //.TXPI_CFG4                          ( 1'b1),
    //.TXPI_CFG5                          ( 3'b000),
    .TXPI_GRAY_SEL                      ( 1'b0),
    .TXPI_INVSTROBE_SEL                 ( 1'b0),
    //.TXPI_LPM                           ( 1'b0),
    .TXPI_PPM_CFG                       ( 8'b00000000),
    //.TXPI_PPMCLK_SEL                    ("TXUSRCLK2"),
    .TXPI_SYNFREQ_PPM                   ( 3'b000),
    //.TXPI_VREFSEL                       ( 1'b0),    
    
    //----------------------------------------------------------------------------------------------  
    //  RX PI Attributes
    //----------------------------------------------------------------------------------------------    
    //.RXPI_AUTO_BW_SEL_BYPASS            ( 1'b0),
    .RXPI_CFG0                          (16'h0100),
    .RXPI_CFG1                          (16'h0100),
    //.RXPI_LPM                           ( 1'b0),
    //.RXPI_SEL_LC                        ( 2'b00),
    //.RXPI_STARTCODE                     ( 2'b00),
    //.RXPI_VREFSEL                       ( 1'b0),              

    //----------------------------------------------------------------------------------------------
    //  RX CDR Attributes
    //----------------------------------------------------------------------------------------------    
    .CDR_SWAP_MODE_EN                   ( 1'b0),                 
    .RX_WIDEMODE_CDR                    ( 2'b01),                                      
    .RXCDR_CFG0                         (RXCDR_CFG0), 
    .RXCDR_CFG0_GEN3                    (RXCDR_CFG0_GEN3), 
    .RXCDR_CFG1                         (RXCDR_CFG1), 
    .RXCDR_CFG1_GEN3                    (RXCDR_CFG1_GEN3), 
    .RXCDR_CFG2                         (RXCDR_CFG2), 
    .RXCDR_CFG2_GEN3                    (RXCDR_CFG2_GEN3), 
    .RXCDR_CFG2_GEN4                    (RXCDR_CFG2_GEN4), 
    .RXCDR_CFG3                         (RXCDR_CFG3), 
    .RXCDR_CFG3_GEN3                    (RXCDR_CFG3_GEN3), 
    .RXCDR_CFG3_GEN4                    (RXCDR_CFG3_GEN4),
    .RXCDR_CFG4                         (RXCDR_CFG4), 
    .RXCDR_CFG4_GEN3                    (RXCDR_CFG4_GEN3), 
    .RXCDR_CFG5                         (RXCDR_CFG5), 
    .RXCDR_CFG5_GEN3                    (RXCDR_CFG5_GEN3), 
    .RXCDR_LOCK_CFG0                    (16'b1001_0000_1000_0001), 
    .RXCDR_LOCK_CFG1                    (16'b1001_0111_1110_0000), 
    .RXCDR_LOCK_CFG2                    (16'b0110_0100_0100_0001), 
    .RXCDR_LOCK_CFG3                    (16'b0000_0111_1110_0000), 

    //---------------------------------------------------------------------------------------------- 
    //  Eye Scan Attributes
    //----------------------------------------------------------------------------------------------
    .ES_CLK_PHASE_SEL                   ( 1'b0),                           
    .ES_CONTROL                         ( 6'b000000),                      
    .ES_ERRDET_EN                       ("FALSE"),                        
    .ES_EYE_SCAN_EN                     ("FALSE"),                        
    .ES_HORZ_OFFSET                     (12'b000000000000),                       
    .ES_PRESCALE                        ( 5'b00000),                                
    .ES_QUAL_MASK0                      (16'b0000000000000000),           
    .ES_QUAL_MASK1                      (16'b0000000000000000),           
    .ES_QUAL_MASK2                      (16'b0000000000000000),           
    .ES_QUAL_MASK3                      (16'b0000000000000000),           
    .ES_QUAL_MASK4                      (16'b0000000000000000),       
    .ES_QUAL_MASK5                      (16'b0000000000000000),           
    .ES_QUAL_MASK6                      (16'b0000000000000000),           
    .ES_QUAL_MASK7                      (16'b0000000000000000),           
    .ES_QUAL_MASK8                      (16'b0000000000000000),           
    .ES_QUAL_MASK9                      (16'b0000000000000000),         
    .ES_QUALIFIER0                      (16'b0000000000000000),           
    .ES_QUALIFIER1                      (16'b0000000000000000),           
    .ES_QUALIFIER2                      (16'b0000000000000000),           
    .ES_QUALIFIER3                      (16'b0000000000000000),           
    .ES_QUALIFIER4                      (16'b0000000000000000), 
    .ES_QUALIFIER5                      (16'b0000000000000000),           
    .ES_QUALIFIER6                      (16'b0000000000000000),           
    .ES_QUALIFIER7                      (16'b0000000000000000),           
    .ES_QUALIFIER8                      (16'b0000000000000000),           
    .ES_QUALIFIER9                      (16'b0000000000000000),   
    .ES_SDATA_MASK0                     (16'b0000000000000000),           
    .ES_SDATA_MASK1                     (16'b0000000000000000),           
    .ES_SDATA_MASK2                     (16'b0000000000000000),           
    .ES_SDATA_MASK3                     (16'b0000000000000000),           
    .ES_SDATA_MASK4                     (16'b0000000000000000), 
    .ES_SDATA_MASK5                     (16'b0000000000000000),           
    .ES_SDATA_MASK6                     (16'b0000000000000000),           
    .ES_SDATA_MASK7                     (16'b0000000000000000),           
    .ES_SDATA_MASK8                     (16'b0000000000000000),   
    .ES_SDATA_MASK9                     (16'b0000000000000000),          
    .EYE_SCAN_SWAP_EN                   ( 1'b0),
    .RX_EYESCAN_VS_CODE                 ( 7'b0000000),
    .RX_EYESCAN_VS_NEG_DIR              ( 1'b0),
    .RX_EYESCAN_VS_RANGE                ( 2'b00),
    .RX_EYESCAN_VS_UT_SIGN              ( 1'b0),                        
  
    //----------------------------------------------------------------------------------------------
    //  Loopback & PRBS Attributes
    //----------------------------------------------------------------------------------------------
    .RXPRBS_ERR_LOOPBACK                ( 1'b0),     
    .RXPRBS_LINKACQ_CNT                 (15),                                                   
                                                                                                    
    //----------------------------------------------------------------------------------------------   
    //  Digital Monitor Attribute
    //----------------------------------------------------------------------------------------------                     
    .DMONITOR_CFG0                      (10'b0000000000),                                                  
    .DMONITOR_CFG1                      ( 8'b00000000),                                                   
                                                      
    //----------------------------------------------------------------------------------------------   
    //  AC JTAG Attributes
    //----------------------------------------------------------------------------------------------                     
    .ACJTAG_DEBUG_MODE                  ( 1'b0),                                                        
    .ACJTAG_MODE                        ( 1'b0),                                                        
    .ACJTAG_RESET                       ( 1'b0),      
    
    //----------------------------------------------------------------------------------------------
    //  USB Attributes
    //----------------------------------------------------------------------------------------------                 
    .USB_BOTH_BURST_IDLE                ( 1'b0),
    .USB_BURSTMAX_U3WAKE	              ( 7'b1111111),
    .USB_BURSTMIN_U3WAKE	              ( 7'b1100011),
    .USB_CLK_COR_EQ_EN                  ( 1'b1),                              
    .USB_EXT_CNTL                       ( 1'b1),
    .USB_IDLEMAX_POLLING                (10'b1010111011),
    .USB_IDLEMIN_POLLING                (10'b0100101011),
    .USB_LFPS_TPERIOD	                  ( 4'b0011),
    .USB_LFPS_TPERIOD_ACCURATE	        ( 1'b1),
    .USB_LFPSPING_BURST	                ( 9'b000000101),
    .USB_LFPSPOLLING_BURST	            ( 9'b000110001),
    .USB_LFPSPOLLING_IDLE_MS	          ( 9'b000000100),
    .USB_LFPSU1EXIT_BURST	              ( 9'b000011101),
    .USB_LFPSU2LPEXIT_BURST_MS	        ( 9'b001100011),
    .USB_LFPSU3WAKE_BURST_MS	          ( 9'b111110011),
    .USB_MODE                           (USB_MODE), 
    .USB_PCIE_ERR_REP_DIS               ( 1'b0),                                // For Debug
    .USB_PING_SATA_MAX_INIT             (21),
    .USB_PING_SATA_MIN_INIT             (12),
    .USB_POLL_SATA_MAX_BURST            ( 8),
    .USB_POLL_SATA_MIN_BURST            ( 4),
    .USB_RAW_ELEC                       ( 1'b1),                               
    .USB_RXIDLE_P0_CTRL                 ( 1'b1),
    .USB_TXIDLE_TUNE_ENABLE             ( 1'b1),
    .USB_U1_SATA_MAX_WAKE               ( 7),
    .USB_U1_SATA_MIN_WAKE               ( 4),
    .USB_U2_SAS_MAX_COM                 (64),   
    .USB_U2_SAS_MIN_COM                 (36),
    
    //---------------------------------------------------------------------------------------------- 
    //  SAS & SATA Attributes (Not used)
    //---------------------------------------------------------------------------------------------- 
  //.SAS12G_MODE                        ( 1'b0),
  //.SATA_BURST_SEQ_LEN                 ( 4'b1111),
  //.SATA_BURST_VAL                     ( 3'b100),
  //.SATA_CPLL_CFG                      ("VCO_3000MHZ"),
  //.SATA_EIDLE_VAL                     ( 3'b100), 
            
    //---------------------------------------------------------------------------------------------- 
    //  CKCAL Attributes
    //---------------------------------------------------------------------------------------------- 
    .CKCAL1_CFG_0	                      (16'hC0C0), //(16'b0000000000000000), [Changed for extracted model]
    .CKCAL1_CFG_1	                      (16'h00C0), //(16'b0000000000000000), [Changed for extracted model] 
    .CKCAL1_CFG_2	                      (16'b0000000000000000),
    .CKCAL1_CFG_3	                      (16'b0000000000000000),
    .CKCAL2_CFG_0	                      (16'h8181), //(16'b0000000000000000), [Changed for extracted model]
    .CKCAL2_CFG_1	                      (16'h8081), //(16'b0000000000000000), [Changed for extracted model]
    .CKCAL2_CFG_2	                      (16'b0000000000000000),
    .CKCAL2_CFG_3	                      (16'b0000000000000000),
    .CKCAL2_CFG_4	                      (16'b0000000000000000),
    //.CKCAL_RSVD0	                      (16'h4000),
    //.CKCAL_RSVD1	                      (16'h0000),
    .RXCKCAL1_I_LOOP_RST_CFG	          (16'h0000),
    .RXCKCAL1_IQ_LOOP_RST_CFG	          (16'h0000),
    .RXCKCAL1_Q_LOOP_RST_CFG	          (16'h0000),
    .RXCKCAL2_D_LOOP_RST_CFG	          (16'h0000),
    .RXCKCAL2_DX_LOOP_RST_CFG	          (16'h0000),
    .RXCKCAL2_S_LOOP_RST_CFG	          (16'h0000),
    .RXCKCAL2_X_LOOP_RST_CFG	          (16'h0000),
  
    //----------------------------------------------------------------------------------------------
    //  Summer Attributes
    //----------------------------------------------------------------------------------------------
    .RX_SUM_DFETAPREP_EN                ( 1'b0),
    .RX_SUM_IREF_TUNE                   ( 4'b0000),
    .RX_SUM_VCM_OVWR                    ( 1'b0),
    .RX_SUM_VCMTUNE                     ( 4'b1000),
    .RX_SUM_VREF_TUNE                   ( 3'b100),

    //----------------------------------------------------------------------------------------------
    //  Attributes
    //----------------------------------------------------------------------------------------------                 
    .A_RXOSCALRESET                     ( 1'b0),   
    .A_RXPROGDIVRESET                   ( 1'b0),
    .A_RXTERMINATION                    ( 1'b1),
    .A_TXDIFFCTRL                       ( 5'b11111),
    .A_TXPROGDIVRESET                   ( 1'b0),
    .ADAPT_CFG0                         ( 16'b1001001000000000),
    .ADAPT_CFG1                         ( 16'b1000000000011100),
    .ADAPT_CFG2                         ( 16'b0000000000000000), 
    //.CAPBYPASS_FORCE                    ( 1'b0),                                
    .CH_HSPMUX                          ( 16'h0000),
    .DDI_CTRL                           ( 2'b00),
    .DDI_REALIGN_WAIT                   (15),
    .DELAY_ELEC                         ( 1'b0),                              
    .ISCAN_CK_PH_SEL2                   ( 1'b0),                                
    .PREIQ_FREQ_BST                     ( 0),                                   
    //.PROCESS_PAR                        ( 3'b010), 
    .RX_CAPFF_SARC_ENB                  ( 1'b0),    
    .RX_DDI_SEL                         ( 6'b000000),  
    .RX_DEGEN_CTRL                      ( 3'b011),                              
    //.RX_DIV2_MODE_B                     ( 1'b0),                                
    //.RX_EN_HI_LR                        ( 1'b0),
    //.RX_EXT_RL_CTRL                     ( 9'b000000000),                        
    .RX_RESLOAD_CTRL	                  ( 4'b0000),                             
    .RX_RESLOAD_OVRD	                  ( 1'b0),                                
    .RX_VREG_CTRL	                      ( 3'b101),                              
    .RX_VREG_PDB	                      ( 1'b1),                                
    .RX_XMODE_SEL	                      ( 1'b0),                                
    .TAPDLY_SET_TX                      ( 2'b00),
    //.TEMPERATURE_PAR                    ( 4'b0010),
    .TST_RSV0                           ( 8'b00000000),                                     
    .TST_RSV1                           ( 8'b00000000),
    .TX_DCC_LOOP_RST_CFG                (16'h0000),                             
    //.TX_DRVMUX_CTRL                     ( 2),                                   
    //.TX_PREDRV_CTRL                     ( 2),                                   
    .TX_PMADATA_OPT                     ( 1'b0)    
)                                                                                                   
gtye4_channel_i                                                                                     
(                                                                                                                                                                                                   
    //----------------------------------------------------------------------------------------------
    //  Clock Ports
    //----------------------------------------------------------------------------------------------
    .GTGREFCLK                          ( 1'd0),                                                     
    .GTREFCLK0                          (GT_GTREFCLK0),                                            
    .GTREFCLK1                          ( 1'd0),                                                    
    .GTNORTHREFCLK0                     ( 1'd0),                                                    
    .GTNORTHREFCLK1                     ( 1'd0),                                                    
    .GTSOUTHREFCLK0                     ( 1'd0),                                                    
    .GTSOUTHREFCLK1                     ( 1'd0),                                             
    .TXUSRCLK                           (GT_TXUSRCLK),                                              
    .RXUSRCLK                           (GT_RXUSRCLK),                                              
    .TXUSRCLK2                          (GT_TXUSRCLK2),                                             
    .RXUSRCLK2                          (GT_RXUSRCLK2),  
    .TXPLLCLKSEL                        (PLLCLKSEL),            
    .RXPLLCLKSEL                        (PLLCLKSEL),                                                    
    .TXSYSCLKSEL                        (SYSCLKSEL),                                             
    .RXSYSCLKSEL                        (SYSCLKSEL),                             
    .TXOUTCLKSEL                        (GT_TXOUTCLKSEL), //( 3'd5),            // Select TXPROGDIVCLK
    .RXOUTCLKSEL                        ( 3'd2),                                // Select RXOUTCLKPMA
    .CLKRSVD0                           ( 1'd0),          
    .CLKRSVD1                           ( 1'd0),            
                                                                                                   
    .TXOUTCLK                           (GT_TXOUTCLK),                                             
    .RXOUTCLK                           (GT_RXOUTCLK),                                                        
    .TXOUTCLKFABRIC                     (GT_TXOUTCLKFABRIC),                                                        
    .RXOUTCLKFABRIC                     (GT_RXOUTCLKFABRIC),                                                        
    .TXOUTCLKPCS                        (GT_TXOUTCLKPCS),                                                        
    .RXOUTCLKPCS                        (GT_RXOUTCLKPCS),  
    .RXRECCLKOUT                        (GT_RXRECCLKOUT),                                                    
    .GTREFCLKMONITOR                    (),                                 
    
    //----------------------------------------------------------------------------------------------
    //  BUFG_GT Controller Ports
    //----------------------------------------------------------------------------------------------
    .BUFGTCE                            (GT_BUFGTCE),      
    .BUFGTCEMASK                        (GT_BUFGTCEMASK), 
    .BUFGTDIV                           (GT_BUFGTDIV), 
    .BUFGTRESET                         (GT_BUFGTRESET), 
    .BUFGTRSTMASK                       (GT_BUFGTRSTMASK),       
    
    //----------------------------------------------------------------------------------------------
    //  CPLL Ports
    //----------------------------------------------------------------------------------------------
    .CPLLFREQLOCK                       (GT_MASTER_CPLLLOCK),                 
    .CPLLLOCKDETCLK                     ( 1'd0),                              
    .CPLLLOCKEN                         ( 1'd1),    
    .CPLLPD                             (GT_CPLLPD),    
    .CPLLREFCLKSEL                      ( 3'd1),                               
    .CPLLRESET                          (GT_CPLLRESET),                               
  
    .CPLLFBCLKLOST                      (),     
    .CPLLLOCK                           (GT_CPLLLOCK),                                            
    .CPLLREFCLKLOST                     (),                    
             
    //----------------------------------------------------------------------------------------------
    //  QPLL Ports                                                                                   
    //----------------------------------------------------------------------------------------------
    .QPLL0CLK                           (GT_QPLL0CLK),                           
    .QPLL0REFCLK                        (GT_QPLL0REFCLK),                        
    .QPLL0FREQLOCK                      (GT_QPLL0LOCK),                         
    .QPLL1CLK                           (GT_QPLL1CLK),  
    .QPLL1REFCLK                        (GT_QPLL1REFCLK),           
    .QPLL1FREQLOCK                      (GT_QPLL1LOCK),                         
    
    //----------------------------------------------------------------------------------------------
    //  Reset Ports
    //----------------------------------------------------------------------------------------------                                                                                                                             
    .GTTXRESET                          (GT_GTTXRESET),                                             
    .GTRXRESET                          (GT_GTRXRESET),  
    .GTRXRESETSEL                       ( 1'd0),                                
    .GTTXRESETSEL                       ( 1'd0),                                
    .TXPROGDIVRESET                     (GT_TXPROGDIVRESET),                       
    .RXPROGDIVRESET                     ( 1'd0),                                                                            
    .TXPMARESET                         (GT_TXPMARESET),                                            
    .RXPMARESET                         (GT_RXPMARESET),                                            
    .TXPCSRESET                         (GT_TXPCSRESET),   
    .RXPCSRESET                         (GT_RXPCSRESET),   
    .TXUSERRDY                          (GT_TXUSERRDY),                                             
    .RXUSERRDY                          (GT_RXUSERRDY),   
    .CFGRESET                           ( 1'd0),                                                    
    .RESETOVRD                          ( GT_RESETOVRD),  
    .RXOOBRESET                         ( 1'd0),                                              
                                           
    .GTPOWERGOOD                        (GT_GTPOWERGOOD), 
    .TXPRGDIVRESETDONE                  (GT_TXPROGDIVRESETDONE),
    .RXPRGDIVRESETDONE                  (),        
    .TXPMARESETDONE                     (GT_TXPMARESETDONE),    
    .RXPMARESETDONE                     (GT_RXPMARESETDONE),                                                                                                      
    .TXRESETDONE                        (GT_TXRESETDONE),                                           
    .RXRESETDONE                        (GT_RXRESETDONE),  
    .RESETEXCEPTION                     (),

    //----------------------------------------------------------------------------------------------
    //  PCIe Ports
    //----------------------------------------------------------------------------------------------
    .PCIERSTIDLE                        (GT_PCIERSTIDLE),        
    .PCIERSTTXSYNCSTART                 (GT_PCIERSTTXSYNCSTART), 
    .PCIEEQRXEQADAPTDONE                (GT_PCIEEQRXEQADAPTDONE),
    .PCIEUSERRATEDONE                   (GT_PCIEUSERRATEDONE),
             
    .PCIEUSERPHYSTATUSRST               (GT_PCIEUSERPHYSTATUSRST),    
    .PCIERATEQPLLPD                     (GT_PCIERATEQPLLPD),                    
    .PCIERATEQPLLRESET                  (GT_PCIERATEQPLLRESET),                 
    .PCIERATEIDLE                       (GT_PCIERATEIDLE),            
    .PCIESYNCTXSYNCDONE                 (GT_PCIESYNCTXSYNCDONE),                          
    .PCIERATEGEN3                       (pcierategen3),    
    .PCIEUSERGEN3RDY                    (GT_PCIEUSERGEN3RDY),   
    .PCIEUSERRATESTART                  (GT_PCIEUSERRATESTART),    
           
    //----------------------------------------------------------------------------------------------
    //  Serial Line Ports
    //----------------------------------------------------------------------------------------------
    .GTYRXP                             (GT_RXP),                                                   
    .GTYRXN                             (GT_RXN),   
   
    .GTYTXP                             (GT_TXP),                                                 
    .GTYTXN                             (GT_TXN),   

    //----------------------------------------------------------------------------------------------
    //  TX Data Ports
    //----------------------------------------------------------------------------------------------
    .TXDATA                             (txdata),                                     
    .TXCTRL0                            (txctrl0),
    .TXCTRL1                            (txctrl1),  
    .TXCTRL2                            (txctrl2),
    .TXDATAEXTENDRSVD                   ( 8'd0),                                

    //----------------------------------------------------------------------------------------------
    //  RX Data Ports
    //----------------------------------------------------------------------------------------------
    .RXDATA                             (rxdata),                                                    
    .RXCTRL0                            (rxctrl0),   
    .RXCTRL1                            (), 
    .RXCTRL2                            (),
    .RXCTRL3                            (), 
    .RXDATAEXTENDRSVD                   (),                                     
 
    //----------------------------------------------------------------------------------------------
    //  PHY Command Ports
    //----------------------------------------------------------------------------------------------
    .TXDETECTRX                         (GT_TXDETECTRX),                                            
    .TXELECIDLE                         (GT_TXELECIDLE),                                      
    .TXPDELECIDLEMODE                   ( 1'd0),                                                                                 
    .RXELECIDLEMODE                     ( 2'd0),                                
    .SIGVALIDCLK                        ( 1'd0),                                                                                    
    .TXPOLARITY                         ( 1'd0),                                              
    .RXPOLARITY                         (GT_RXPOLARITY),                                
    .TXPD                               (GT_POWERDOWN),                                           
    .RXPD                               (GT_POWERDOWN),                                           
    .TXRATE                             ({1'd0, GT_RATE}),                                                
    .RXRATE                             ({1'd0, GT_RATE}),                                                
    .TXRATEMODE                         ( 1'd0),                                                    
    .RXRATEMODE                         ( 1'd0),                                                    
 
    //----------------------------------------------------------------------------------------------
    //  PHY Status Ports
    //----------------------------------------------------------------------------------------------
    .RXVALID                            (GT_RXVALID),                                              
    .PHYSTATUS                          (GT_PHYSTATUS),                                            
    .RXELECIDLE                         (rxelecidle_int),                                           
    .RXSTATUS                           (GT_RXSTATUS),                                             
    .TXRATEDONE                         (),                                           
    .RXRATEDONE                         (GT_RXRATEDONE),                  
 
    //----------------------------------------------------------------------------------------------
    //  TX Driver Ports
    //----------------------------------------------------------------------------------------------
    .TXMARGIN                           (GT_TXMARGIN),                                           
    .TXSWING                            (GT_TXSWING),                                            
    .TXDEEMPH                           (GT_TXDEEMPH),                                                                     
    .TXDIFFCTRL                         ( 5'b11111),
    .TXINHIBIT                          ( 1'd0),                                                  

    //----------------------------------------------------------------------------------------------
    //  TX Driver Ports (Gen3)
    //----------------------------------------------------------------------------------------------
    .TXPRECURSOR                        (GT_TXPRECURSOR),                                          
    .TXMAINCURSOR                       (GT_TXMAINCURSOR),                                         
    .TXPOSTCURSOR                       (GT_TXPOSTCURSOR),                                                                                     

    //----------------------------------------------------------------------------------------------
    //  PCS Reserved Ports
    //---------------------------------------------------------------------------------------------- 
    .PCSRSVDIN                          (16'h0001),                             // CHECK                                                                               
    .PCSRSVDOUT                         (pcsrsvdout),     
    
    //----------------------------------------------------------------------------------------------
    //  RX Monitor Ports
    //----------------------------------------------------------------------------------------------
    .RXMONITORSEL                       ( 2'd0), 
    .RXMONITOROUT                       (),                                                                                                                                                                                                            
                                                                 
    //----------------------------------------------------------------------------------------------
    //  Comma Detect & Align Ports
    //----------------------------------------------------------------------------------------------
    .RXCOMMADETEN                       ( 1'd1),                  
    .RXMCOMMAALIGNEN                    (!pcierategen3),          
    .RXPCOMMAALIGNEN                    (!pcierategen3),          
                                                                                 
    .RXCOMMADET                         (),                                            
    .RXBYTEISALIGNED                    (),                                        
    .RXBYTEREALIGN                      (),                                                                                                                 
                                                                                                    
    //----------------------------------------------------------------------------------------------
    // 8B10B Ports
    //----------------------------------------------------------------------------------------------
    .TX8B10BBYPASS                      ( 8'd0),                                                  
    .TX8B10BEN                          (!pcierategen3),                            
    .RX8B10BEN                          (!pcierategen3),                            
           
    //----------------------------------------------------------------------------------------------
    //  TX Buffer Ports
    //----------------------------------------------------------------------------------------------
    .TXBUFSTATUS                        (),                                                        
                                                                                                    
    //----------------------------------------------------------------------------------------------
    //  RX Buffer Ports
    //----------------------------------------------------------------------------------------------
    .RXBUFRESET                         (GT_RXBUFRESET),                                          
    .RXBUFSTATUS                        (),                
                      
    //----------------------------------------------------------------------------------------------
    //  Clock Correction Ports
    //----------------------------------------------------------------------------------------------
    .RXCLKCORCNT                        (),                            
                    
    //----------------------------------------------------------------------------------------------
    //  Channel Bonding Ports (disable)
    //----------------------------------------------------------------------------------------------
    .RXCHBONDEN                         ( 1'd0),                                         
    .RXCHBONDI                          ( 5'd0),                                         
    .RXCHBONDLEVEL                      ( 3'd0),                                         
    .RXCHBONDMASTER                     ( 1'd0),                                         
    .RXCHBONDSLAVE                      ( 1'd0),                                         
                                                                                    
    .RXCHANBONDSEQ                      (),                                         
    .RXCHANISALIGNED                    (),                                         
    .RXCHANREALIGN                      (),                                         
    .RXCHBONDO                          (),                                                                                                                                                                       
 
    //----------------------------------------------------------------------------------------------
    //  TX Phase Alignment Ports
    //----------------------------------------------------------------------------------------------
    .TXPHALIGN                          ( 1'd0),
    .TXPHALIGNEN                        ( 1'd0),
    .TXPHDLYPD                          ( 1'd0),
    .TXPHDLYRESET                       ( 1'd0),
    .TXPHDLYTSTCLK                      ( 1'd0),
    .TXPHINIT                           ( 1'd0),
    .TXPHOVRDEN                         ( 1'd0),
   
    .TXPHALIGNDONE                      (GT_TXPHALIGNDONE),
    .TXPHINITDONE                       (),
   
    //----------------------------------------------------------------------------------------------
    //  TX Delay Alignment Ports
    //----------------------------------------------------------------------------------------------
    .TXDLYBYPASS                        ( 1'd0),
    .TXDLYEN                            ( 1'd0),
    .TXDLYHOLD                          ( 1'd0),
    .TXDLYOVRDEN                        ( 1'd0),
    .TXDLYSRESET                        ( 1'd0),
    .TXDLYUPDOWN                        ( 1'd0),
       
    .TXDLYSRESETDONE                    (),       
          
    //----------------------------------------------------------------------------------------------
    //  TX Auto Sync Alignment Ports 
    //----------------------------------------------------------------------------------------------
    .TXSYNCALLIN                        (GT_TXSYNCALLIN),
    .TXSYNCIN                           (GT_TXSYNCIN),
    .TXSYNCMODE                         (MASTER_LANE),                                         
                
    .TXSYNCDONE                         (),
    .TXSYNCOUT                          (GT_TXSYNCOUT),

    //----------------------------------------------------------------------------------------------
    //  RX Phase Alignment Ports (disable)
    //----------------------------------------------------------------------------------------------
    .RXPHALIGN                          ( 1'd0),
    .RXPHALIGNEN                        ( 1'd0),
    .RXPHDLYPD                          ( 1'd0),
    .RXPHDLYRESET                       ( 1'd0),
  //.RXPHOVRDEN                         ( 1'd0),
   
    .RXPHALIGNDONE                      (),
    .RXPHALIGNERR                       (),
       
    //----------------------------------------------------------------------------------------------
    //  RX Delay Alignment Ports (disable)
    //----------------------------------------------------------------------------------------------
    .RXDLYBYPASS                        ( 1'd1),
    .RXDLYEN                            ( 1'd0),
    .RXDLYOVRDEN                        ( 1'd0),
    .RXDLYSRESET                        ( 1'd0),
   
    .RXDLYSRESETDONE                    (),                                           
        
    //----------------------------------------------------------------------------------------------
    //  RX Auto Sync Alignment Ports (disable)
    //----------------------------------------------------------------------------------------------
    .RXSYNCALLIN                        ( 1'd0),
    .RXSYNCIN                           ( 1'd0),
    .RXSYNCMODE                         ( 1'd0),                                                    
                                                                                                    
    .RXSYNCDONE                         (),                                                
    .RXSYNCOUT                          (),    
       
    //----------------------------------------------------------------------------------------------
    //  Gearbox Ports 
    //----------------------------------------------------------------------------------------------
    .TXHEADER                           ( 6'd0), 
    .TXLATCLK                           ( 1'd0),                                                    
    .TXSEQUENCE                         ( 7'd0),                                                    
    .RXGEARBOXSLIP                      ( 1'd0),  
    .RXLATCLK                           ( 1'd0),  
    .RXSLIDE                            ( 1'd0),                                                    
                                                                                                    
    .RXDATAVALID                        (),                 
    .RXHEADER                           (),                                                         
    .RXHEADERVALID                      (), 
    .RXSLIDERDY                         (),                                                         
    .RXSTARTOFSEQ                       (),                             
                   
    //----------------------------------------------------------------------------------------------
    //  RX Slip Ports 
    //----------------------------------------------------------------------------------------------
    .RXSLIPOUTCLK                       ( 1'd0),
    .RXSLIPPMA                          ( 1'd0),   
                                                                   
    .RXSLIPDONE                         (),     
    .RXSLIPOUTCLKRDY                    (),
    .RXSLIPPMARDY                       (),             
       
    //----------------------------------------------------------------------------------------------
    //  RX LPM Ports 
    //----------------------------------------------------------------------------------------------
    .RXLPMEN                            (!pcierategen3),    
    .RXLPMGCHOLD                        ( 1'b0),            
    .RXLPMGCOVRDEN                      ( 1'b0),
    .RXLPMHFHOLD                        ( 1'b0),            
    .RXLPMHFOVRDEN                      ( 1'b0),
    .RXLPMLFHOLD                        ( 1'b0),         
    .RXLPMLFKLOVRDEN                    ( 1'b0), 
    .RXLPMOSHOLD                        ( 1'b0),            
    .RXLPMOSOVRDEN                      ( 1'b0),
                                                                                                    
    //----------------------------------------------------------------------------------------------
    //  RX DFE Ports
    //----------------------------------------------------------------------------------------------
    ////.RXDFEAGCCTRL                       ( 2'h1), //( 2'b00),     [Changed for extracted model]
    .RXDFEAGCHOLD                       ( 1'b0),            
    .RXDFEAGCOVRDEN                     ( 1'b0),
    .RXDFECFOKFCNUM                     ( 4'b0000),                             
    .RXDFECFOKFEN                       ( 1'b0),                                
    .RXDFECFOKFPULSE                    ( 1'b0),                                
    .RXDFECFOKHOLD                      ( 1'b0),                                
    .RXDFECFOKOVREN                     ( 1'b0),                                
    .RXDFEKHHOLD                        ( 1'b0),
    .RXDFEKHOVRDEN                      ( 1'b0),
    .RXDFELFHOLD                        ( 1'b0),          
    .RXDFELFOVRDEN                      ( 1'b0),
    .RXDFELPMRESET                      (GT_RXDFELPMRESET),
    .RXDFETAP2HOLD                      ( 1'b0),
    .RXDFETAP2OVRDEN                    ( 1'b0),
    .RXDFETAP3HOLD                      ( 1'b0),
    .RXDFETAP3OVRDEN                    ( 1'b0),
    .RXDFETAP4HOLD                      ( 1'b0),
    .RXDFETAP4OVRDEN                    ( 1'b0),
    .RXDFETAP5HOLD                      ( 1'b0),
    .RXDFETAP5OVRDEN                    ( 1'b0),
    .RXDFETAP6HOLD                      ( 1'b0),
    .RXDFETAP6OVRDEN                    ( 1'b0),
    .RXDFETAP7HOLD                      ( 1'b0),
    .RXDFETAP7OVRDEN                    ( 1'b0),
    .RXDFETAP8HOLD                      ( 1'b0),
    .RXDFETAP8OVRDEN                    ( 1'b0),
    .RXDFETAP9HOLD                      ( 1'b0),
    .RXDFETAP9OVRDEN                    ( 1'b0),
    .RXDFETAP10HOLD                     ( 1'b0),
    .RXDFETAP10OVRDEN                   ( 1'b0),
    .RXDFETAP11HOLD                     ( 1'b0),
    .RXDFETAP11OVRDEN                   ( 1'b0),
    .RXDFETAP12HOLD                     ( 1'b0),
    .RXDFETAP12OVRDEN                   ( 1'b0),
    .RXDFETAP13HOLD                     ( 1'b0),
    .RXDFETAP13OVRDEN                   ( 1'b0),
    .RXDFETAP14HOLD                     ( 1'b0),
    .RXDFETAP14OVRDEN                   ( 1'b0),
    .RXDFETAP15HOLD                     ( 1'b0),
    .RXDFETAP15OVRDEN                   ( 1'b0),
    .RXDFEUTHOLD                        ( 1'b0),
    .RXDFEUTOVRDEN                      ( 1'b0),
    .RXDFEVPHOLD                        ( 1'b0),
    .RXDFEVPOVRDEN                      ( 1'b0),
    .RXDFEXYDEN                         ( 1'b1),                                                                                                    
    
    //----------------------------------------------------------------------------------------------
    //  TX PI Ports
    //----------------------------------------------------------------------------------------------
    .TXPIPPMEN                          ( 1'd0),
    .TXPIPPMOVRDEN                      ( 1'd0),
    .TXPIPPMPD                          ( 1'd0),
    .TXPIPPMSEL                         ( 1'd0),
    .TXPIPPMSTEPSIZE                    ( 5'd0),
    .TXPISOPD                           ( 1'd0),   
    
    //----------------------------------------------------------------------------------------------
    //  RX CDR Ports
    //----------------------------------------------------------------------------------------------
    .CDRSTEPDIR                         ( 1'b0),                                 
    .CDRSTEPSQ                          ( 1'b0),                                
    .CDRSTEPSX                          ( 1'b0),                               
    .RXCDRFREQRESET                     (GT_RXCDRFREQRESET),
    .RXCDRHOLD                          (GT_RXCDRHOLD),
    .RXCDROVRDEN                        ( 1'd0),
    .RXCDRRESET                         (rxcdrreset_int),
    
    .RXCDRLOCK                          (GT_RXCDRLOCK),    
    .RXCDRPHDONE                        (), 
       
    //----------------------------------------------------------------------------------------------
    //  Eye Scan Ports
    //----------------------------------------------------------------------------------------------                                          
    .EYESCANRESET                       ( 1'd0),                                             
    .EYESCANTRIGGER                     ( 1'd0),                                             
                                                                                            
    .EYESCANDATAERROR                   (),           
       
    //----------------------------------------------------------------------------------------------
    //  RX OS Ports
    //----------------------------------------------------------------------------------------------
    .RXOSCALRESET                       ( 1'b0),
    .RXOSHOLD                           ( 1'b0),
    .RXOSOVRDEN                         ( 1'b0),    
 
    .RXOSINTDONE                        (),                                                         
    .RXOSINTSTARTED                     (),                                                         
    .RXOSINTSTROBEDONE                  (),                                                         
    .RXOSINTSTROBESTARTED               (),         
           
    //----------------------------------------------------------------------------------------------
    //  DRP Ports
    //----------------------------------------------------------------------------------------------
    .DRPCLK                             (GT_DRPCLK), 
    .DRPRST                             ( 1'd0),                                                                                
    .DRPADDR                            (GT_DRPADDR),                                                    
    .DRPEN                              (GT_DRPEN),                                                    
    .DRPWE                              (GT_DRPWE), 
    .DRPDI                              (GT_DRPDI),                                                    
        
    .DRPRDY                             (GT_DRPRDY),                                                         
    .DRPDO                              (GT_DRPDO),

    //----------------------------------------------------------------------------------------------
    //  Loopback & PRBS Ports
    //----------------------------------------------------------------------------------------------
    .LOOPBACK                           (GT_LOOPBACK),      
    .TXPRBSSEL                          (GT_PRBSSEL),                                                    
    .RXPRBSSEL                          (GT_PRBSSEL),  
    .TXPRBSFORCEERR                     (GT_TXPRBSFORCEERR),  
    .RXPRBSCNTRESET                     (GT_RXPRBSCNTRESET),  
                   
    .RXPRBSERR                          (GT_RXPRBSERR),                                                
    .RXPRBSLOCKED                       (GT_RXPRBSLOCKED),       

    //----------------------------------------------------------------------------------------------
    //  Digital Monitor Ports                                                                             
    //----------------------------------------------------------------------------------------------
    .DMONFIFORESET                      ( 1'd0),                                                    
    .DMONITORCLK                        ( 1'd0),                                                    
    
    .DMONITOROUT                        (),    
    .DMONITOROUTCLK                     (),                                             
      
    //----------------------------------------------------------------------------------------------
    //  USB Ports
    //----------------------------------------------------------------------------------------------
    .TXONESZEROS                        (GT_TXONESZEROS),
    .RXEQTRAINING                       (GT_RXEQTRAINING),
    .RXTERMINATION                      (GT_RXTERMINATION),    
    
    .POWERPRESENT                       (GT_POWERPRESENT),           
        
    //----------------------------------------------------------------------------------------------
    //  USB LFPS Ports
    //----------------------------------------------------------------------------------------------
    .TXLFPSTRESET                       ( 1'b0),      
    .TXLFPSU2LPEXIT                     ( 1'b0),
    .TXLFPSU3WAKE                       ( 1'b0),
    
    .RXLFPSTRESETDET                    (),             
    .RXLFPSU2LPEXITDET                  (),             
    .RXLFPSU3WAKEDET                    (),            
      
    //----------------------------------------------------------------------------------------------
    //  SATA Ports 
    //----------------------------------------------------------------------------------------------
    .TXCOMINIT                          ( 1'd0),                                                    
    .TXCOMSAS                           ( 1'd0),                                                    
    .TXCOMWAKE                          ( 1'd0),                                                    

    .TXCOMFINISH                        (),                                                         
    .RXCOMINITDET                       (),                                                         
    .RXCOMSASDET                        (),                                                         
    .RXCOMWAKEDET                       (),                                                    

    //----------------------------------------------------------------------------------------------
    //  QPI
    //----------------------------------------------------------------------------------------------
    ////.RXQPIEN                            ( 1'd0),
    ////.TXQPIBIASEN                        ( 1'b0),                                
    ////.TXQPIWEAKPUP                       ( 1'b0),                              
    
    ////.RXQPISENN                          (),
    ////.RXQPISENP                          (),
    ////.TXQPISENN                          (),
    ////.TXQPISENP                          (),

    //----------------------------------------------------------------------------------------------
    //  GT Ports
    //----------------------------------------------------------------------------------------------
    .FREQOS                             ( 1'd0),    
    .GTRSVD                             (16'd0),
    .INCPCTRL                           ( 1'd0),
    .RXAFECFOKEN                        ( 1'd0),                                
    .RXCKCALRESET                       ( 1'b0),                                
    .RXCKCALSTART                       ( 7'd0),                                
    .TSTIN                              (20'h00000),                                                
    .TXDCCFORCESTART                    ( 1'b0),                                
    .TXDCCRESET                         ( 1'b0),                                
    .TXMUXDCDEXHOLD                     ( 1'b0),                                
    .TXMUXDCDORWREN                     ( 1'b0),                                
                                                                                   
    .PINRSRVDAS                         (),                                     
    .RXCKCALDONE                        (),                                     
    .TXDCCDONE                          ()                                      
);

end else begin: GTH_CHANNEL
//--------------------------------------------------------------------------------------------------
//  GTH Channel
//--------------------------------------------------------------------------------------------------
GTHE4_CHANNEL #
(  
    //----------------------------------------------------------------------------------------------
    //  Simulation Attributes
    //----------------------------------------------------------------------------------------------
    .SIM_MODE                           ("FAST"),                                    
    .SIM_RECEIVER_DETECT_PASS           ("TRUE"),
    .SIM_RESET_SPEEDUP                  ("TRUE"),
    .SIM_TX_EIDLE_DRIVE_LEVEL           (SIM_TX_EIDLE_DRIVE_LEVEL),
    .SIM_DEVICE                         ("ULTRASCALE_PLUS"),                             
   
    //----------------------------------------------------------------------------------------------     
    //  Clock Attributes
    //----------------------------------------------------------------------------------------------                       
    .TXREFCLKDIV2_SEL                   ( 1'b0),                              
    .RXREFCLKDIV2_SEL                   ( 1'b0),                                
    .TX_CLK25_DIV                       (CLK25_DIV),                                                    
    .RX_CLK25_DIV                       (CLK25_DIV),                                                    
    .TX_CLKMUX_EN                       ( 1'b1),                                                
    .RX_CLKMUX_EN                       ( 1'b1),                                                
    .TX_XCLK_SEL                        ("TXUSR"),                                              
    .RX_XCLK_SEL                        ("RXDES"),   
    .TXOUT_DIV                          (OUT_DIV), 
    .RXOUT_DIV                          (OUT_DIV), 
    .LOCAL_MASTER                       (LOCAL_MASTER),   
    .RX_CLK_SLIP_OVRD                   ( 5'b00000),  
    .RXPMACLK_SEL                       ("DATA"),                                                                                                                           
    .USE_PCS_CLK_PHASE_SEL              ( 1'b0),           
   
    //----------------------------------------------------------------------------------------------     
    //  Programmable Divider Attributes
    //----------------------------------------------------------------------------------------------                                                                                                                       
    .TX_PROGCLK_SEL                     ("CPLL"),                               
    .TX_PROGDIV_CFG                     (PROGDIV_CFG),                      
    .RX_PROGDIV_CFG                     (PROGDIV_CFG),   
    .TX_PROGDIV_RATE                    (16'h0001),                          
    .RX_PROGDIV_RATE                    (16'h0001),                                   
               
    //----------------------------------------------------------------------------------------------
    //  CPLL Attributes
    //----------------------------------------------------------------------------------------------                 
    .CPLL_CFG0                          (16'h00FA), //(16'h20FA),               // Optimize for PCIe PLL compliance  
    .CPLL_CFG1                          (16'h0023), //(16'h24AA),          
    .CPLL_CFG2                          (16'h0002),                             
    .CPLL_CFG3                          ( 6'h00),  
    .CPLL_FBDIV                         (CPLL_FBDIV),  
    .CPLL_FBDIV_45                      (CPLL_FBDIV_45),    
    .CPLL_INIT_CFG0                     (16'h02B2),                
    .CPLL_LOCK_CFG                      (16'h01E8), //(16'h01E8),                             
    .CPLL_REFCLK_DIV                    ( 1),     
             
    //----------------------------------------------------------------------------------------------
    //  Reset Attributes
    //----------------------------------------------------------------------------------------------                
    .RESET_POWERSAVE_DISABLE            ( 1'b0),   
                                                                              
    //----------------------------------------------------------------------------------------------
    //  Reset Time Attributes
    //----------------------------------------------------------------------------------------------    
    .TX_DIVRESET_TIME                   ( 5'b00010), //( 5'b00001),  
    .TXPCSRESET_TIME	                  ( 5'b00011),
    .TXPMARESET_TIME	                  ( 5'b00011),
    .RX_DIVRESET_TIME                   ( 5'b00010), //( 5'b00001),  
    .RXBUFRESET_TIME                    ( 5'b00011),
    .RXCDRFREQRESET_TIME                ( 5'b10000), //( 5'b00001),  
    .RXCDRPHRESET_TIME                  ( 5'b00001),    
    .RXDFELPMRESET_TIME                 ( 7'b0001111),    
    .RXISCANRESET_TIME	                ( 5'b00001), 
    .RXOSCALRESET_TIME	                ( 5'b00011), 
    .RXPCSRESET_TIME	                  ( 5'b00011),   
    .RXPMARESET_TIME	                  ( 5'b00011),   
               
    //----------------------------------------------------------------------------------------------
    //  PCIe Attributes
    //----------------------------------------------------------------------------------------------
    .PCIE_BUFG_DIV_CTRL                 (PCIE_BUFG_DIV_CTRL),                  
    .PCIE_RXPCS_CFG_GEN3                (PCIE_RXPCS_CFG_GEN3),                 
    .PCIE_RXPMA_CFG                     (PCIE_PMA_CFG),                        
    .PCIE_TXPCS_CFG_GEN3                (PCIE_TXPCS_CFG_GEN3),                 
    .PCIE_TXPMA_CFG                     (PCIE_PMA_CFG),                        
    .PCS_PCIE_EN                        (PCS_PCIE_EN),  
    .PCIE_PLL_SEL_MODE_GEN12            (PCIE_PLL_SEL_MODE_GEN12),                  
    .PCIE_PLL_SEL_MODE_GEN3             (PCIE_PLL_SEL_MODE_GEN3),  
    .PCIE_PLL_SEL_MODE_GEN4             (PCIE_PLL_SEL_MODE_GEN4),                     
           
    //---------------------------------------------------------------------------------------------- 
    //  Data Width Attributes
    //----------------------------------------------------------------------------------------------                          
    .TX_DATA_WIDTH                      (20),                                                                                                                                         
    .RX_DATA_WIDTH                      (20),  
    .TX_INT_DATAWIDTH                   ( 0),                                                                
    .RX_INT_DATAWIDTH                   ( 0),   
    .TX_FABINT_USRCLK_FLOP              ( 1'b0), 
    .RX_FABINT_USRCLK_FLOP              ( 1'b0),                                                    
              
    //----------------------------------------------------------------------------------------------
    //  Analog Front End Attributes
    //----------------------------------------------------------------------------------------------
    .LPBK_BIAS_CTRL	                    ( 3'b100),                           
    .LPBK_EN_RCAL_B	                    ( 1'b0),                             
    .LPBK_EXT_RCAL	                    ( 4'b1000),                          
    .LPBK_RG_CTRL	                      ( 4'b1110),                             
    .RX_AFE_CM_EN                       ( 1'b0),
    .RX_BIAS_CFG0                       (16'h1554),
    .RX_CM_BUF_CFG                      ( 4'b1010),
    .RX_CM_BUF_PD                       ( 1'b0),                                           
    .RX_CM_SEL                          (RX_CM_SEL),                                                        
    .RX_CM_TRIM                         (10),    
    .RX_TUNE_AFE_OS                     ( 2'b00),
    .TERM_RCAL_CFG                      (15'b100001000010001),                                     
    .TERM_RCAL_OVRD                     ( 3'b000),             
                                                                                                    
    //----------------------------------------------------------------------------------------------  
    //  Receiver Detection Attributes
    //----------------------------------------------------------------------------------------------                                      
    .TX_RXDETECT_CFG                    (14'h0032),                                                      
    .TX_RXDETECT_REF                    (3),                                  
    
    //----------------------------------------------------------------------------------------------  
    //  TX Electrical Idle Attributes
    //----------------------------------------------------------------------------------------------   
    .TX_EIDLE_ASSERT_DELAY              (TX_EIDLE_ASSERT_DELAY),                            
    .TX_EIDLE_DEASSERT_DELAY            (TX_EIDLE_DEASSERT_DELAY),             
    .TX_IDLE_DATA_ZERO                  ( 1'b0),                                // Optimized for PCIe      
 
    //----------------------------------------------------------------------------------------------  
    //  RX OOB Attributes
    //----------------------------------------------------------------------------------------------   
    .OOB_PWRUP                          ( 1'b1),                                
    .OOBDIVCTL                          (OOBDIVCTL),                                            
    .RX_SIG_VALID_DLY                   ( 4),                                   // Optimized for PCIe
    .RXOOB_CFG                          ( 9'b000000110),                          
    .RXOOB_CLK_CFG                      ("PMA"),      
    
    //----------------------------------------------------------------------------------------------  
    //  RX Electrical Idle Attributes
    //----------------------------------------------------------------------------------------------                                                   
    .RX_DFE_LPM_HOLD_DURING_EIDLE       ( 1'b0),                                
    .RXBUF_EIDLE_HI_CNT                 ( 4'b0100),                             // Optimized for PCIe
    .RXBUF_EIDLE_LO_CNT                 ( 4'b0000),
    .RXBUF_RESET_ON_EIDLE               ("TRUE"),
    .RXCDR_FR_RESET_ON_EIDLE            ( 1'b0),
    .RXCDR_PH_RESET_ON_EIDLE            ( 1'b0),
    .RXCDR_HOLD_DURING_EIDLE            ( 1'b0),                                // Optimized for PCIe
    .RXELECIDLE_CFG                     ("SIGCFG_1"),                           // Optimized for PCIe
 
    //----------------------------------------------------------------------------------------------  
    //  Power Down Attributes
    //----------------------------------------------------------------------------------------------   
    .PD_TRANS_TIME_FROM_P2              (12'h03C),                                                     
    .PD_TRANS_TIME_NONE_P2              ( 8'h19),                                                      
    .PD_TRANS_TIME_TO_P2                ( 8'h64),   
    .TX_PMA_POWER_SAVE                  ( 1'b0),   
    .RX_PMA_POWER_SAVE                  ( 1'b0),                               
  
    //----------------------------------------------------------------------------------------------  
    //  Rate Change Attributes
    //---------------------------------------------------------------------------------------------- 
    .RATE_SW_USE_DRP                    ( 1'b0),                                // Advance PCIe feature
    .TRANS_TIME_RATE                    ( 8'h0E),             
    .TXBUF_RESET_ON_RATE_CHANGE         ("TRUE"),                              
    .RXBUF_RESET_ON_RATE_CHANGE         ("TRUE"),                              

    //----------------------------------------------------------------------------------------------
    //  TX Driver Attributes
    //----------------------------------------------------------------------------------------------                                   
    .TX_DEEMPH0                         ( 6'b010100),                           // -6.0 dB 
    .TX_DEEMPH1                         ( 6'b001101),                           // -3.5 dB
    .TX_DEEMPH2                         ( 6'b000000),                           //  0.0 dB 
    .TX_DEEMPH3                         ( 6'b000000),                           //  0.0 dB  
    .TX_DRIVE_MODE                      ("PIPE"),                                
    .TX_LOOPBACK_DRIVE_HIZ              ("FALSE"),                   
    .TX_MAINCURSOR_SEL                  ( 1'b0),   
    .TX_MARGIN_FULL_0                   ( 7'b1001111),                          // 1200 mV
    .TX_MARGIN_FULL_1                   ( 7'b1001110),                          // 1100 mV
    .TX_MARGIN_FULL_2                   ( 7'b1001100),                          // 1000 mV 
    .TX_MARGIN_FULL_3                   ( 7'b1001010),                          //  900 mV
    .TX_MARGIN_FULL_4                   ( 7'b1001000),                          //  800 mV
    .TX_MARGIN_LOW_0                    ( 7'b1000110),                          //  700 mV            
    .TX_MARGIN_LOW_1                    ( 7'b1000101),                          //  600 mV           
    .TX_MARGIN_LOW_2                    ( 7'b1000011),                          //  500 mV          
    .TX_MARGIN_LOW_3                    ( 7'b1000010),                          //  400 mV           
    .TX_MARGIN_LOW_4                    ( 7'b1000000),                          //  300 mV                               
   
    //----------------------------------------------------------------------------------------------    
    //  Comma Align & Detect Attributes
    //----------------------------------------------------------------------------------------------       
    .ALIGN_COMMA_DOUBLE                 (ALIGN_COMMA_DOUBLE),                                                  
    .ALIGN_COMMA_ENABLE                 (10'b1111111111),                                           
    .ALIGN_COMMA_WORD                   ( 1),                                                       
    .ALIGN_MCOMMA_DET                   ("TRUE"),                                                   
    .ALIGN_MCOMMA_VALUE                 (10'b1010000011),                                           
    .ALIGN_PCOMMA_DET                   ("TRUE"),                                                   
    .ALIGN_PCOMMA_VALUE                 (10'b0101111100),                                           
    .DEC_MCOMMA_DETECT                  ("TRUE"),                                                      
    .DEC_PCOMMA_DETECT                  ("TRUE"),                                                      
    .DEC_VALID_COMMA_ONLY               ("FALSE"),                                                     
    .SHOW_REALIGN_COMMA                 (SHOW_REALIGN_COMMA),       
   
    //----------------------------------------------------------------------------------------------   
    //  8B/10B Attributes                                                                             
    //----------------------------------------------------------------------------------------------                   
    .RX_DISPERR_SEQ_MATCH               ("TRUE"),        
   
    //----------------------------------------------------------------------------------------------  
    //  TX Buffer Attributes
    //----------------------------------------------------------------------------------------------                      
    .TX_FIFO_BYP_EN                     ( 1'b1),                                
    .TXBUF_EN                           ("FALSE"),        
    .TXFIFO_ADDR_CFG                    ("LOW"),                                                                                      
 
    //----------------------------------------------------------------------------------------------
    //  RX Buffer Attributes                                                                        
    //----------------------------------------------------------------------------------------------     
    .RXBUF_ADDR_MODE                    ("FULL"),                               
    .RXBUF_EN                           ("TRUE"),
    .RXBUF_RESET_ON_CB_CHANGE           ("TRUE"),
    .RXBUF_RESET_ON_COMMAALIGN          ("FALSE"),
    .RXBUF_THRESH_OVFLW                 (RXBUF_THRESH_OVFLW),                                                      
    .RXBUF_THRESH_OVRD                  ("TRUE"),                             
    .RXBUF_THRESH_UNDFLW                (RXBUF_THRESH_UNDFLW),                                    
    .RX_BUFFER_CFG                      ( 6'b000000),
    .RX_DEFER_RESET_BUF_EN              ("TRUE"), 
   
    //----------------------------------------------------------------------------------------------   
    //  PCIe Gen3 RX Buffer Attributes                                                                                   
    //----------------------------------------------------------------------------------------------   
    .PCI3_AUTO_REALIGN                  ("OVR_1K_BLK"),                           
    .PCI3_PIPE_RX_ELECIDLE              ( 1'b0),                                
    .PCI3_RX_ASYNC_EBUF_BYPASS          ( 2'b00),                               
    .PCI3_RX_ELECIDLE_EI2_ENABLE        ( 1'b0),                                
    .PCI3_RX_ELECIDLE_H2L_COUNT         ( 6'b000000),                           
    .PCI3_RX_ELECIDLE_H2L_DISABLE       ( 3'b000),                              
    .PCI3_RX_ELECIDLE_HI_COUNT          ( 6'b000000),                           
    .PCI3_RX_ELECIDLE_LP4_DISABLE       ( 1'b0),                                
    .PCI3_RX_FIFO_DISABLE               ( 1'b0),                                
       
    //----------------------------------------------------------------------------------------------   
    //  PCIe Gen3 Clock Correction Attributes                                                                                   
    //----------------------------------------------------------------------------------------------          
    .PCIE3_CLK_COR_EMPTY_THRSH          (PCIE3_CLK_COR_EMPTY_THRSH),                           
    .PCIE3_CLK_COR_FULL_THRSH           (PCIE3_CLK_COR_FULL_THRSH),                          
    .PCIE3_CLK_COR_MAX_LAT              (PCIE3_CLK_COR_MAX_LAT),                          
    .PCIE3_CLK_COR_MIN_LAT              (PCIE3_CLK_COR_MIN_LAT),                          
    .PCIE3_CLK_COR_THRSH_TIMER          (PCIE3_CLK_COR_THRSH_TIMER),                      
       
    //---------------------------------------------------------------------------------------------- 
    //  Clock Correction Attributes
    //----------------------------------------------------------------------------------------------             
    .CBCC_DATA_SOURCE_SEL               ("DECODED"),  
    .CLK_COR_KEEP_IDLE                  (CLK_COR_KEEP_IDLE),
    .CLK_COR_MAX_LAT                    (CLK_COR_MAX_LAT),                                   
    .CLK_COR_MIN_LAT                    (CLK_COR_MIN_LAT),                                  
    .CLK_COR_PRECEDENCE                 ("TRUE"),
    .CLK_COR_REPEAT_WAIT                (0),
    .CLK_COR_SEQ_1_1                    (CLK_COR_SEQ_1_1),
    .CLK_COR_SEQ_1_2                    (CLK_COR_SEQ_1_2),
    .CLK_COR_SEQ_1_3                    (10'b0000000000),
    .CLK_COR_SEQ_1_4                    (10'b0000000000),
    .CLK_COR_SEQ_1_ENABLE               (4'b1111),
    .CLK_COR_SEQ_2_1                    (10'b0000000000),
    .CLK_COR_SEQ_2_2                    (10'b0000000000),
    .CLK_COR_SEQ_2_3                    (10'b0000000000),
    .CLK_COR_SEQ_2_4                    (10'b0000000000),
    .CLK_COR_SEQ_2_ENABLE               (CLK_COR_SEQ_2_ENABLE),
    .CLK_COR_SEQ_2_USE                  ("FALSE"),
    .CLK_COR_SEQ_LEN                    (CLK_COR_SEQ_LEN),
    .CLK_CORRECT_USE                    ("TRUE"),                
       
    //---------------------------------------------------------------------------------------------- 
    //  FTS Deskew Attributes                                                                            
    //----------------------------------------------------------------------------------------------                                         
    .FTS_DESKEW_SEQ_ENABLE              ( 4'b1111),                                        
    .FTS_LANE_DESKEW_CFG                ( 4'b1111),                                          
    .FTS_LANE_DESKEW_EN                 ("FALSE"),           
       
    //---------------------------------------------------------------------------------------------- 
    //  Channel Bonding Attributes (Disabled)
    //----------------------------------------------------------------------------------------------          
    .CHAN_BOND_KEEP_ALIGN               ("FALSE"),
    .CHAN_BOND_MAX_SKEW                 ( 1),
    .CHAN_BOND_SEQ_1_1                  (10'b0000000000),
    .CHAN_BOND_SEQ_1_2                  (10'b0000000000),
    .CHAN_BOND_SEQ_1_3                  (10'b0000000000),
    .CHAN_BOND_SEQ_1_4                  (10'b0000000000),
    .CHAN_BOND_SEQ_1_ENABLE             ( 4'b1111),
    .CHAN_BOND_SEQ_2_1                  (10'b0000000000),
    .CHAN_BOND_SEQ_2_2                  (10'b0000000000),
    .CHAN_BOND_SEQ_2_3                  (10'b0000000000),
    .CHAN_BOND_SEQ_2_4                  (10'b0000000000),  
    .CHAN_BOND_SEQ_2_ENABLE             ( 4'b1111),
    .CHAN_BOND_SEQ_2_USE                ("FALSE"), 
    .CHAN_BOND_SEQ_LEN                  ( 1),                                                           
  
    //----------------------------------------------------------------------------------------------            
    //  TX Sync Alignment Attributes                                                                              
    //----------------------------------------------------------------------------------------------     
    .TXDLY_CFG                          (16'b1000000000010000),    
    .TXDLY_LCFG                         (16'b0000000000110000),                
    .TXPH_CFG                           (16'b0000000100100011), //(16'b0000000100000011),               
    .TXPH_CFG2                          (16'b0000000000000000),                 
    .TXPH_MONITOR_SEL                   ( 5'b00000),
    .TXPHDLY_CFG0                       (16'b0110000000100000),                 
    .TXPHDLY_CFG1                       (16'b0000000000000010),              
                                                                                    
    //----------------------------------------------------------------------------------------------            
    //  TX Auto Sync Alignment Attributes                                                                               
    //----------------------------------------------------------------------------------------------                
    .TXSYNC_MULTILANE                   (MULTI_LANE),                                                                                                              
    .TXSYNC_OVRD                        (1'b0),                                 // Select auto TXSYNC mode                                                                                 
    .TXSYNC_SKIP_DA                     (1'b0),                     
                                                                                                    
    //----------------------------------------------------------------------------------------------            
    //  RX Sync Alignment Attributes (Not used)                                                                             
    //----------------------------------------------------------------------------------------------    
  //.RXDLY_CFG                          (16'h001F),   
  //.RXDLY_LCFG                         (16'h0030),   
  //.RXPH_MONITOR_SEL                   (5'b00000),
  //.RXPHBEACON_CFG                     (16'h0000),
  //.RXPHDLY_CFG                        (16'h2020),
  //.RXPHSAMP_CFG                       (16'h2100),
  //.RXPHSLIP_CFG                       (16'h9933),                             
     
    //----------------------------------------------------------------------------------------------            
    //  RX Auto Sync Alignment Attributes (Not used)                                                                                
    //----------------------------------------------------------------------------------------------                
  //.RXSYNC_MULTILANE                   (1'b0),                                                                                                              
  //.RXSYNC_OVRD                        (1'b0),                                                                                         
  //.RXSYNC_SKIP_DA                     (1'b0),                   
  
    //----------------------------------------------------------------------------------------------  
    //  Gearbox Attributes (Not used)                                                                
    //---------------------------------------------------------------------------------------------- 
  //.GEARBOX_MODE                       ( 5'b00000), 
  //.TX_SAMPLE_PERIOD                   ( 3'b101),
  //.RX_SAMPLE_PERIOD                   ( 3'b101),
  //.TXGEARBOX_EN                       ("FALSE"),
  //.RXGEARBOX_EN                       ("FALSE"),    
  //.TXGBOX_FIFO_INIT_RD_ADDR           ( 4),
  //.RXGBOX_FIFO_INIT_RD_ADDR           ( 4),
  //.RXSLIDE_AUTO_WAIT                  ( 7),                                                         
    .RXSLIDE_MODE                       (RXSLIDE_MODE),                          

    //----------------------------------------------------------------------------------------------
    //  PCS Reserved Attributes
    //----------------------------------------------------------------------------------------------
    .PCS_RSVD0                          (PCS_RSVD0),
  
    //----------------------------------------------------------------------------------------------  
    //  PMA Reserved Attributes
    //----------------------------------------------------------------------------------------------      
    .TX_PMA_RSV0                        (16'b0000000000001000),                             
    .RX_PMA_RSV0                        (16'b0000000000000000),                                        
      
    //----------------------------------------------------------------------------------------------
    //  CFOK Attributes                                                                 
    //----------------------------------------------------------------------------------------------              
    .RXCFOK_CFG0                        (16'b0000000000000000), //(16'b0011111000000000),   
    .RXCFOK_CFG1                        (16'b1000000000010101), //(16'b0000000001000010),    
    .RXCFOK_CFG2                        (16'b0000001010101110), //(16'b0000000000101101),  

    //----------------------------------------------------------------------------------------------
    //  RX CTLE
    //----------------------------------------------------------------------------------------------  
    .CTLE3_OCAP_EXT_CTRL	              ( 3'b000),                           
    .CTLE3_OCAP_EXT_EN	                ( 1'b0),                                
    .RX_EN_CTLE_RCAL_B                  ( 1'b0),                              

    //----------------------------------------------------------------------------------------------    
    //  RX LPM Attributes
    //----------------------------------------------------------------------------------------------        
    .RXLPM_CFG                          (16'b0000_0000_0000_0000),    
    .RXLPM_GC_CFG                       (16'b1000_0000_0000_0000),
    .RXLPM_KH_CFG0                      (16'b0000_0000_0000_0000), //(16'b0000000000000000),    
    .RXLPM_KH_CFG1                      (16'b0000_0000_0000_0010), //(16'b0000000000000010),    
    .RXLPM_OS_CFG0                      (16'b0000_0000_0000_0000),
    .RXLPM_OS_CFG1                      (16'b1000_0000_0000_0010), //(16'b0000000000000000), 
 
    //----------------------------------------------------------------------------------------------    
    //  RX DFE Attributes
    //----------------------------------------------------------------------------------------------       
    .RXDFE_CFG0                         (16'b0000101000000000), //(16'b0000110000000000),    
    .RXDFE_CFG1                         (16'b0000001010000000),
    .RXDFE_GC_CFG0                      (16'b0000000000000000), //(16'b0001111000000000),    
    .RXDFE_GC_CFG1                      (16'b1000000000000000), //(16'h1900),   different from GTY             
    .RXDFE_GC_CFG2                      (16'b1111111111100000), //(16'h0000),   different from GTY             
    .RXDFE_H2_CFG0                      (16'b0000000000000000), //(16'b0000000000000000),    
    .RXDFE_H2_CFG1                      (16'b0000000000000010), //(16'b0000000000000010),    
    .RXDFE_H3_CFG0                      (16'b0000000000000000), //(16'b0000000000000000),    
    .RXDFE_H3_CFG1                      (16'b1000000000000010), //(16'b0000000000000010),    
    .RXDFE_H4_CFG0                      (16'b0000000000000000), //(16'b0000000000000000),    
    .RXDFE_H4_CFG1                      (16'b1000000000000010), //(16'b0000000000000011),    
    .RXDFE_H5_CFG0                      (16'b0000000000000000), //(16'b0000000000000000),    
    .RXDFE_H5_CFG1                      (16'b1000000000000010), //(16'b0000000000000010),    
    .RXDFE_H6_CFG0                      (16'b0000000000000000), //(16'b0000000000000000),    
    .RXDFE_H6_CFG1                      (16'b1000000000000010), //(16'b0000000000000010),    
    .RXDFE_H7_CFG0                      (16'b0000000000000000), //(16'b0000000000000000),    
    .RXDFE_H7_CFG1                      (16'b1000000000000010), //(16'b0000000000000010),    
    .RXDFE_H8_CFG0                      (16'b0000000000000000), //(16'b0000000000000000),    
    .RXDFE_H8_CFG1                      (16'b1000000000000010), //(16'b0000000000000010),    
    .RXDFE_H9_CFG0                      (16'b0000000000000000), //(16'b0000000000000000),    
    .RXDFE_H9_CFG1                      (16'b1000000000000010), //(16'b0000000000000010),    
    .RXDFE_HA_CFG0                      (16'b0000000000000000), //(16'b0000000000000000),    
    .RXDFE_HA_CFG1                      (16'b1000000000000010), //(16'b0000000000000010),    
    .RXDFE_HB_CFG0                      (16'b0000000000000000), //(16'b0010000000000000),    
    .RXDFE_HB_CFG1                      (16'b1000000000000010), //(16'b0000000000000010),    
    .RXDFE_HC_CFG0                      (16'b0000000000000000), //(16'b0000000000000000),    
    .RXDFE_HC_CFG1                      (16'b1000000000000010), //(16'b0000000000000010),    
    .RXDFE_HD_CFG0                      (16'b0000000000000000), //(16'b0000000000000000),    
    .RXDFE_HD_CFG1                      (16'b1000000000000010), //(16'b0000000000000010),    
    .RXDFE_HE_CFG0                      (16'b0000000000000000), //(16'b0000000000000000),    
    .RXDFE_HE_CFG1                      (16'b1000000000000010), //(16'b0000000000000010),    
    .RXDFE_HF_CFG0                      (16'b0000000000000000), //(16'b0000000000000000),    
    .RXDFE_HF_CFG1                      (16'b1000000000000010), //(16'b0000000000000010),    
    .RXDFE_OS_CFG0                      (16'b0000000000000000), //(16'b0000000000000000),    
    .RXDFE_OS_CFG1                      (16'b1000000000000010), //(16'b0000001000000000),    
    .RXDFE_PWR_SAVING                   (RXDFE_PWR_SAVING),
    .RXDFE_UT_CFG0                      (16'b0000000000000000), //(16'b0000000000000000),    
    .RXDFE_UT_CFG1                      (16'b0000000000000011), //(16'b0000000000000010),    
    .RXDFE_UT_CFG2                      (16'b0000000000000000),
    .RXDFE_VP_CFG0                      (16'b0000000000000000), //(16'b0000000000000000),    
    .RXDFE_VP_CFG1                      (16'b1000000000110011), //(16'b0000000000100010),    
    .RXDFELPM_KL_CFG0                   (16'b0000000000000000),                  
    .RXDFELPM_KL_CFG1                   (16'b1010000011100010),             
    .RXDFELPM_KL_CFG2                   (16'b0000000100000000),                        
    .RX_DFE_AGC_CFG0                    ( 2'b10),                               
    .RX_DFE_AGC_CFG1                    ( 4),  
    .RX_DFE_KL_LPM_KH_CFG0              ( 1),
    .RX_DFE_KL_LPM_KH_CFG1              ( 4),
    .RX_DFE_KL_LPM_KL_CFG0              ( 2'b01),
    .RX_DFE_KL_LPM_KL_CFG1              ( 4),   
    .RX_DFELPM_CFG0                     ( 6),                                                            
    .RX_DFELPM_CFG1                     ( 1'b1),                                                               
    .RX_DFELPM_KLKH_AGC_STUP_EN         ( 1'b1),   
          
    //----------------------------------------------------------------------------------------------  
    //  TX PI attributes
    //----------------------------------------------------------------------------------------------
    .TX_PHICAL_CFG0	                    (16'h0000),                           
    .TX_PHICAL_CFG1	                    (16'h7e00),
    .TX_PHICAL_CFG2	                    (16'h0200), //(16'h0000),  
    .TX_PI_BIASSET	                    (TX_PI_BIASSET),                                  
    .TXPI_CFG0                          ( 2'b00),
    .TXPI_CFG1                          ( 2'b00),
    .TXPI_CFG2                          ( 2'b00),
    .TXPI_CFG3                          ( 1'b0),
    .TXPI_CFG4                          ( 1'b0),
    .TXPI_CFG5                          ( 3'b000),
    .TXPI_GRAY_SEL                      ( 1'b0),
    .TXPI_INVSTROBE_SEL                 ( 1'b0),
    .TXPI_LPM                           ( 1'b0),
    .TXPI_PPM_CFG                       ( 8'b00000000),
    .TXPI_PPMCLK_SEL                    ("TXUSRCLK2"),
    .TXPI_SYNFREQ_PPM                   ( 3'b001),
    .TXPI_VREFSEL                       ( 1'b0),
    
    //----------------------------------------------------------------------------------------------  
    //  RX PI Attributes
    //----------------------------------------------------------------------------------------------    
    .RXPI_AUTO_BW_SEL_BYPASS            ( 1'b0),
    .RXPI_CFG0                          (RXPI_CFG0),
    .RXPI_CFG1                          (16'h0000),
    .RXPI_LPM                           ( 1'b0),
    .RXPI_SEL_LC                        ( 2'b00),
    .RXPI_STARTCODE                     ( 2'b00),
    .RXPI_VREFSEL                       ( 1'b0),              

    //----------------------------------------------------------------------------------------------
    //  RX CDR Attributes
    //----------------------------------------------------------------------------------------------    
    .CDR_SWAP_MODE_EN                   ( 1'b0),                 
    .RX_WIDEMODE_CDR                    ( 2'b00),                               //Gen1/2 wide mode    
    .RX_WIDEMODE_CDR_GEN3               ( 2'b00), 
    .RX_WIDEMODE_CDR_GEN4               ( 2'b01),
    .RXCDR_CFG0                         (RXCDR_CFG0), 
    .RXCDR_CFG0_GEN3                    (RXCDR_CFG0_GEN3), 
    .RXCDR_CFG1                         (RXCDR_CFG1), 
    .RXCDR_CFG1_GEN3                    (RXCDR_CFG1_GEN3), 
    .RXCDR_CFG2                         (RXCDR_CFG2), 
    .RXCDR_CFG2_GEN3                    (RXCDR_CFG2_GEN3), 
    .RXCDR_CFG2_GEN4                    (RXCDR_CFG2_GEN4), 
    .RXCDR_CFG3                         (RXCDR_CFG3), 
    .RXCDR_CFG3_GEN3                    (RXCDR_CFG3_GEN3), 
    .RXCDR_CFG3_GEN4                    (RXCDR_CFG3_GEN4),
    .RXCDR_CFG4                         (RXCDR_CFG4), 
    .RXCDR_CFG4_GEN3                    (RXCDR_CFG4_GEN3), 
    .RXCDR_CFG5                         (RXCDR_CFG5), 
    .RXCDR_CFG5_GEN3                    (RXCDR_CFG5_GEN3), 
    .RXCDR_LOCK_CFG0                    (16'b0001_0010_0000_0001), //(16'h0001),  
    .RXCDR_LOCK_CFG1                    (16'b1001_1111_1111_1111), //(16'h0000),  
    .RXCDR_LOCK_CFG2                    (16'b0111_0111_1100_0011), //(16'b0000),  
    .RXCDR_LOCK_CFG3                    (16'b0000_0000_0000_0001), //(16'h0000),  

    //---------------------------------------------------------------------------------------------- 
    //  Eye Scan Attributes
    //----------------------------------------------------------------------------------------------
    .ES_CLK_PHASE_SEL                   ( 1'b0),                           
    .ES_CONTROL                         ( 6'b000000),                      
    .ES_ERRDET_EN                       ("FALSE"),                        
    .ES_EYE_SCAN_EN                     ("FALSE"),                        
    .ES_HORZ_OFFSET                     (12'b000000000000),                       
    .ES_PRESCALE                        ( 5'b00000),                                
    .ES_QUAL_MASK0                      (16'b0000000000000000),           
    .ES_QUAL_MASK1                      (16'b0000000000000000),           
    .ES_QUAL_MASK2                      (16'b0000000000000000),           
    .ES_QUAL_MASK3                      (16'b0000000000000000),           
    .ES_QUAL_MASK4                      (16'b0000000000000000),       
    .ES_QUAL_MASK5                      (16'b0000000000000000),           
    .ES_QUAL_MASK6                      (16'b0000000000000000),           
    .ES_QUAL_MASK7                      (16'b0000000000000000),           
    .ES_QUAL_MASK8                      (16'b0000000000000000),           
    .ES_QUAL_MASK9                      (16'b0000000000000000),         
    .ES_QUALIFIER0                      (16'b0000000000000000),           
    .ES_QUALIFIER1                      (16'b0000000000000000),           
    .ES_QUALIFIER2                      (16'b0000000000000000),           
    .ES_QUALIFIER3                      (16'b0000000000000000),           
    .ES_QUALIFIER4                      (16'b0000000000000000), 
    .ES_QUALIFIER5                      (16'b0000000000000000),           
    .ES_QUALIFIER6                      (16'b0000000000000000),           
    .ES_QUALIFIER7                      (16'b0000000000000000),           
    .ES_QUALIFIER8                      (16'b0000000000000000),           
    .ES_QUALIFIER9                      (16'b0000000000000000),   
    .ES_SDATA_MASK0                     (16'b0000000000000000),           
    .ES_SDATA_MASK1                     (16'b0000000000000000),           
    .ES_SDATA_MASK2                     (16'b0000000000000000),           
    .ES_SDATA_MASK3                     (16'b0000000000000000),           
    .ES_SDATA_MASK4                     (16'b0000000000000000), 
    .ES_SDATA_MASK5                     (16'b0000000000000000),           
    .ES_SDATA_MASK6                     (16'b0000000000000000),           
    .ES_SDATA_MASK7                     (16'b0000000000000000),           
    .ES_SDATA_MASK8                     (16'b0000000000000000),   
    .ES_SDATA_MASK9                     (16'b0000000000000000),          
    .EYE_SCAN_SWAP_EN                   ( 1'b0),
    .RX_EYESCAN_VS_CODE                 ( 7'b0000000),
    .RX_EYESCAN_VS_NEG_DIR              ( 1'b0),
    .RX_EYESCAN_VS_RANGE                ( 2'b00),
    .RX_EYESCAN_VS_UT_SIGN              ( 1'b0),                        
  
    //----------------------------------------------------------------------------------------------
    //  Loopback & PRBS Attributes
    //----------------------------------------------------------------------------------------------
    .RXPRBS_ERR_LOOPBACK                ( 1'b0),     
    .RXPRBS_LINKACQ_CNT                 (15),                                                   

    //----------------------------------------------------------------------------------------------   
    //  Digital Monitor Attribute
    //----------------------------------------------------------------------------------------------                     
    .DMONITOR_CFG0                      (10'b0000000000),                                                  
    .DMONITOR_CFG1                      ( 8'b00000000),                                                   

    //----------------------------------------------------------------------------------------------   
    //  AC JTAG Attributes
    //----------------------------------------------------------------------------------------------                     
    .ACJTAG_DEBUG_MODE                  ( 1'b0),                                                        
    .ACJTAG_MODE                        ( 1'b0),                                                        
    .ACJTAG_RESET                       ( 1'b0),      
    
    //----------------------------------------------------------------------------------------------
    //  USB Attributes
    //----------------------------------------------------------------------------------------------                 
    .USB_BOTH_BURST_IDLE                ( 1'b0),
    .USB_BURSTMAX_U3WAKE	              ( 7'b1111111),
    .USB_BURSTMIN_U3WAKE	              ( 7'b1100011),
    .USB_CLK_COR_EQ_EN                  ( 1'b1),                              
    .USB_EXT_CNTL                       ( 1'b1),
    .USB_IDLEMAX_POLLING                (10'b1010111011),
    .USB_IDLEMIN_POLLING                (10'b0100101011),
    .USB_LFPS_TPERIOD	                  ( 4'b0011),
    .USB_LFPS_TPERIOD_ACCURATE	        ( 1'b1),
    .USB_LFPSPING_BURST	                ( 9'b000000101),
    .USB_LFPSPOLLING_BURST	            ( 9'b000110001),
    .USB_LFPSPOLLING_IDLE_MS	          ( 9'b000000100),
    .USB_LFPSU1EXIT_BURST	              ( 9'b000011101),
    .USB_LFPSU2LPEXIT_BURST_MS	        ( 9'b001100011),
    .USB_LFPSU3WAKE_BURST_MS	          ( 9'b111110011),
    .USB_MODE                           (USB_MODE), 
    .USB_PCIE_ERR_REP_DIS               ( 1'b0),                                // For PCIe Debug
    .USB_PING_SATA_MAX_INIT             (21),
    .USB_PING_SATA_MIN_INIT             (12),
    .USB_POLL_SATA_MAX_BURST            ( 8),
    .USB_POLL_SATA_MIN_BURST            ( 4),
    .USB_RAW_ELEC                       ( 1'b1),                               
    .USB_RXIDLE_P0_CTRL                 ( 1'b1),
    .USB_TXIDLE_TUNE_ENABLE             ( 1'b1),
    .USB_U1_SATA_MAX_WAKE               ( 7),
    .USB_U1_SATA_MIN_WAKE               ( 4),
    .USB_U2_SAS_MAX_COM                 (64),   
    .USB_U2_SAS_MIN_COM                 (36),
    
    //---------------------------------------------------------------------------------------------- 
    //  SAS & SATA Attributes (Not used)
    //---------------------------------------------------------------------------------------------- 
  //.SAS12G_MODE                        ( 1'b0),
  //.SATA_BURST_SEQ_LEN                 ( 4'b1111),
  //.SATA_BURST_VAL                     ( 3'b100),
  //.SATA_CPLL_CFG                      ("VCO_3000MHZ"),
  //.SATA_EIDLE_VAL                     ( 3'b100), 
            
    //---------------------------------------------------------------------------------------------- 
    //  CKCAL Attributes
    //---------------------------------------------------------------------------------------------- 
    .CKCAL1_CFG_0	                      (16'hC0C0), //(16'b0000000000000000), 
    .CKCAL1_CFG_1	                      (16'h50C0), //(16'b0000000000000000), 
    .CKCAL1_CFG_2	                      (16'b0000000000001010),
    .CKCAL1_CFG_3	                      (16'b0000000000000000),
    .CKCAL2_CFG_0	                      (16'hC0C0), //(16'b0000000000000000), 
    .CKCAL2_CFG_1	                      (16'h80C0), //(16'b0000000000000000), 
    .CKCAL2_CFG_2	                      (16'b0000000000000000),
    .CKCAL2_CFG_3	                      (16'b0000000000000000),
    .CKCAL2_CFG_4	                      (16'b0000000000000000),
    .CKCAL_RSVD0	                      (16'h0000),
    .CKCAL_RSVD1	                      (16'b0000010000000000), //(16'h0000),
    .RXCKCAL1_I_LOOP_RST_CFG	          (16'h0004),
    .RXCKCAL1_IQ_LOOP_RST_CFG	          (16'h0004),
    .RXCKCAL1_Q_LOOP_RST_CFG	          (16'h0004),
    .RXCKCAL2_D_LOOP_RST_CFG	          (16'h0004),
    .RXCKCAL2_DX_LOOP_RST_CFG	          (16'h0004),
    .RXCKCAL2_S_LOOP_RST_CFG	          (16'h0004),
    .RXCKCAL2_X_LOOP_RST_CFG	          (16'h0004),
  
    //----------------------------------------------------------------------------------------------
    //  Summer Attributes
    //----------------------------------------------------------------------------------------------
    .RX_SUM_DFETAPREP_EN                ( 1'b0),
    .RX_SUM_IREF_TUNE                   (RX_SUM_IREF_TUNE),
    .RX_SUM_VCM_OVWR                    ( 1'b0),
    .RX_SUM_VCMTUNE                     (RX_SUM_VCMTUNE),
    .RX_SUM_VREF_TUNE                   ( 3'b100),

    //----------------------------------------------------------------------------------------------
    //  Attributes
    //----------------------------------------------------------------------------------------------                 
    .A_RXOSCALRESET                     ( 1'b0),   
    .A_RXPROGDIVRESET                   ( 1'b0),
    .A_RXTERMINATION                    ( 1'b1),
    .A_TXDIFFCTRL                       ( 5'b11111),
    .A_TXPROGDIVRESET                   ( 1'b0),
    .ADAPT_CFG0                         (16'b0001000000000000), //(16'b1001001000000000),   
    .ADAPT_CFG1                         (16'b1100101100000000), //(16'b1000000000011100),   
    .ADAPT_CFG2                         (16'b0000000000000000),   
    .CAPBYPASS_FORCE                    ( 1'b0),                                
    .CH_HSPMUX                          (16'b0110_1101_0110_1101), //(16'h0000),   
    .DDI_CTRL                           ( 2'b00),
    .DDI_REALIGN_WAIT                   (15),
    .DELAY_ELEC                         ( 1'b0),                                
    .ISCAN_CK_PH_SEL2                   ( 1'b0),                                
    .PREIQ_FREQ_BST                     ( 1),                                   
    .PROCESS_PAR                        ( 3'b010), 
    .RX_CAPFF_SARC_ENB                  ( 1'b0),    
    .RX_DDI_SEL                         ( 6'b000000),  
    .RX_DEGEN_CTRL                      ( 3'b011),                              
    .RX_DIV2_MODE_B                     ( 1'b0),                                
    .RX_EN_HI_LR                        ( 1'b1),
    .RX_EXT_RL_CTRL                     ( 9'b000000000),                        
    .RX_RESLOAD_CTRL	                  ( 4'b0000),                             
    .RX_RESLOAD_OVRD	                  ( 1'b0),                                
    .RX_VREG_CTRL	                      ( 3'b101),                              
    .RX_VREG_PDB	                      ( 1'b1),                                
    .RX_XMODE_SEL	                      ( 1'b0),                                
    .TAPDLY_SET_TX                      ( 2'b00),
    .TEMPERATURE_PAR                    ( 4'b0010),
    .TST_RSV0                           ( 8'b00000000),                                     
    .TST_RSV1                           ( 8'b00000000),
    .TX_DCC_LOOP_RST_CFG                (16'h0004),                             
    .TX_DRVMUX_CTRL                     ( 2),                                   
    .TX_PREDRV_CTRL                     ( 2),                                   
    .TX_PMADATA_OPT                     ( 1'b0)    
)                                                                                                   
gthe4_channel_i                                                                                     
(                                                                                                                                                                                                   
    //----------------------------------------------------------------------------------------------
    //  Clock Ports
    //----------------------------------------------------------------------------------------------
    .GTGREFCLK                          ( 1'd0),                                                     
    .GTREFCLK0                          (GT_GTREFCLK0),                                            
    .GTREFCLK1                          ( 1'd0),                                                    
    .GTNORTHREFCLK0                     ( 1'd0),                                                    
    .GTNORTHREFCLK1                     ( 1'd0),                                                    
    .GTSOUTHREFCLK0                     ( 1'd0),                                                    
    .GTSOUTHREFCLK1                     ( 1'd0),                                             
    .TXUSRCLK                           (GT_TXUSRCLK),                                              
    .RXUSRCLK                           (GT_RXUSRCLK),                                              
    .TXUSRCLK2                          (GT_TXUSRCLK2),                                             
    .RXUSRCLK2                          (GT_RXUSRCLK2),  
    .TXPLLCLKSEL                        (PLLCLKSEL),            
    .RXPLLCLKSEL                        (PLLCLKSEL),                                                    
    .TXSYSCLKSEL                        (SYSCLKSEL),                                             
    .RXSYSCLKSEL                        (SYSCLKSEL),                             
    .TXOUTCLKSEL                        (GT_TXOUTCLKSEL),                                // Select TXPROGDIVCLK
    .RXOUTCLKSEL                        ( 3'd2),                                // Select RXOUTCLKPMA
    .CLKRSVD0                           ( 1'd0),          
    .CLKRSVD1                           ( 1'd0),            
                                                                                                   
    .TXOUTCLK                           (GT_TXOUTCLK),                                             
    .RXOUTCLK                           (GT_RXOUTCLK),                                                        
    .TXOUTCLKFABRIC                     (GT_TXOUTCLKFABRIC),                                                        
    .RXOUTCLKFABRIC                     (GT_RXOUTCLKFABRIC),                                                        
    .TXOUTCLKPCS                        (GT_TXOUTCLKPCS),                                                        
    .RXOUTCLKPCS                        (GT_RXOUTCLKPCS),  
    .RXRECCLKOUT                        (GT_RXRECCLKOUT),                                                    
    .GTREFCLKMONITOR                    (),                                 
    
    //----------------------------------------------------------------------------------------------
    //  BUFG_GT Controller Ports
    //----------------------------------------------------------------------------------------------
    .BUFGTCE                            (GT_BUFGTCE),      
    .BUFGTCEMASK                        (GT_BUFGTCEMASK), 
    .BUFGTDIV                           (GT_BUFGTDIV), 
    .BUFGTRESET                         (GT_BUFGTRESET), 
    .BUFGTRSTMASK                       (GT_BUFGTRSTMASK),       
    
    //----------------------------------------------------------------------------------------------
    //  CPLL Ports
    //----------------------------------------------------------------------------------------------
    .CPLLFREQLOCK                       (GT_MASTER_CPLLLOCK),                 
    .CPLLLOCKDETCLK                     ( 1'd0),                              
    .CPLLLOCKEN                         ( 1'd1),    
    .CPLLPD                             (GT_CPLLPD),    
    .CPLLREFCLKSEL                      ( 3'd1),                               
    .CPLLRESET                          (GT_CPLLRESET),                               
  
    .CPLLFBCLKLOST                      (),     
    .CPLLLOCK                           (GT_CPLLLOCK),                                            
    .CPLLREFCLKLOST                     (),                    
             
    //----------------------------------------------------------------------------------------------
    //  QPLL Ports                                                                                   
    //----------------------------------------------------------------------------------------------
    .QPLL0CLK                           (GT_QPLL0CLK),                           
    .QPLL0REFCLK                        (GT_QPLL0REFCLK),                        
    .QPLL0FREQLOCK                      (GT_QPLL0LOCK),                         
    .QPLL1CLK                           (GT_QPLL1CLK),  
    .QPLL1REFCLK                        (GT_QPLL1REFCLK),           
    .QPLL1FREQLOCK                      (GT_QPLL1LOCK),                         
    
    //----------------------------------------------------------------------------------------------
    //  Reset Ports
    //----------------------------------------------------------------------------------------------                                                                                                                             
    .GTTXRESET                          (GT_GTTXRESET),                                             
    .GTRXRESET                          (GT_GTRXRESET),  
    .GTRXRESETSEL                       ( 1'd0),                                
    .GTTXRESETSEL                       ( 1'd0),                                
    .TXPROGDIVRESET                     (GT_TXPROGDIVRESET),                       
    .RXPROGDIVRESET                     ( 1'd0),                                                                            
    .TXPMARESET                         (GT_TXPMARESET),                                            
    .RXPMARESET                         (GT_RXPMARESET),                                            
    .TXPCSRESET                         (GT_TXPCSRESET),   
    .RXPCSRESET                         (GT_RXPCSRESET),   
    .TXUSERRDY                          (GT_TXUSERRDY),                                             
    .RXUSERRDY                          (GT_RXUSERRDY),   
    .CFGRESET                           ( 1'd0),                                                    
    .RESETOVRD                          (GT_RESETOVRD),  
    .RXOOBRESET                         ( 1'd0),                                              
                                           
    .GTPOWERGOOD                        (GT_GTPOWERGOOD), 
    .TXPRGDIVRESETDONE                  (GT_TXPROGDIVRESETDONE),
    .RXPRGDIVRESETDONE                  (),        
    .TXPMARESETDONE                     (GT_TXPMARESETDONE),    
    .RXPMARESETDONE                     (GT_RXPMARESETDONE),                                                                                                      
    .TXRESETDONE                        (GT_TXRESETDONE),                                           
    .RXRESETDONE                        (GT_RXRESETDONE),  
    .RESETEXCEPTION                     (),

    //----------------------------------------------------------------------------------------------
    //  PCIe Ports
    //----------------------------------------------------------------------------------------------
    .PCIERSTIDLE                        (GT_PCIERSTIDLE),        
    .PCIERSTTXSYNCSTART                 (GT_PCIERSTTXSYNCSTART), 
    .PCIEEQRXEQADAPTDONE                (GT_PCIEEQRXEQADAPTDONE),
    .PCIEUSERRATEDONE                   (GT_PCIEUSERRATEDONE),
             
    .PCIEUSERPHYSTATUSRST               (GT_PCIEUSERPHYSTATUSRST),    
    .PCIERATEQPLLPD                     (GT_PCIERATEQPLLPD),                    
    .PCIERATEQPLLRESET                  (GT_PCIERATEQPLLRESET),                 
    .PCIERATEIDLE                       (GT_PCIERATEIDLE),            
    .PCIESYNCTXSYNCDONE                 (GT_PCIESYNCTXSYNCDONE),                          
    .PCIERATEGEN3                       (pcierategen3),    
    .PCIEUSERGEN3RDY                    (GT_PCIEUSERGEN3RDY),   
    .PCIEUSERRATESTART                  (GT_PCIEUSERRATESTART),    
           
    //----------------------------------------------------------------------------------------------
    //  Serial Line Ports
    //----------------------------------------------------------------------------------------------
    .GTHRXP                             (GT_RXP),                                                   
    .GTHRXN                             (GT_RXN),   
   
    .GTHTXP                             (GT_TXP),                                                 
    .GTHTXN                             (GT_TXN),   

    //----------------------------------------------------------------------------------------------
    //  TX Data Ports
    //----------------------------------------------------------------------------------------------
    .TXDATA                             (txdata),                                     
    .TXCTRL0                            (txctrl0),
    .TXCTRL1                            (txctrl1),  
    .TXCTRL2                            (txctrl2),
    .TXDATAEXTENDRSVD                   ( 8'd0),                                

    //----------------------------------------------------------------------------------------------
    //  RX Data Ports
    //----------------------------------------------------------------------------------------------
    .RXDATA                             (rxdata),                                                    
    .RXCTRL0                            (rxctrl0),   
    .RXCTRL1                            (), 
    .RXCTRL2                            (),
    .RXCTRL3                            (), 
    .RXDATAEXTENDRSVD                   (),                                     
 
    //----------------------------------------------------------------------------------------------
    //  PHY Command Ports
    //----------------------------------------------------------------------------------------------
    .TXDETECTRX                         (GT_TXDETECTRX),                                            
    .TXELECIDLE                         (GT_TXELECIDLE),                                      
    .TXPDELECIDLEMODE                   ( 1'd0),                                                                                 
    .RXELECIDLEMODE                     ( 2'd0),                                
    .SIGVALIDCLK                        ( 1'd0),                                                                                    
    .TXPOLARITY                         ( 1'd0),                                              
    .RXPOLARITY                         (GT_RXPOLARITY),                                
    .TXPD                               (GT_POWERDOWN),                                           
    .RXPD                               (GT_POWERDOWN),                                           
    .TXRATE                             ({1'd0, GT_RATE}),                                                
    .RXRATE                             ({1'd0, GT_RATE}),                                                
    .TXRATEMODE                         ( 1'd0),                                                    
    .RXRATEMODE                         ( 1'd0),                                                    
 
    //----------------------------------------------------------------------------------------------
    //  PHY Status Ports
    //----------------------------------------------------------------------------------------------
    .RXVALID                            (GT_RXVALID),                                              
    .PHYSTATUS                          (GT_PHYSTATUS),                                            
    .RXELECIDLE                         (rxelecidle_int),                                           
    .RXSTATUS                           (GT_RXSTATUS),                                             
    .TXRATEDONE                         (),                                           
    .RXRATEDONE                         (GT_RXRATEDONE),                  
 
    //----------------------------------------------------------------------------------------------
    //  TX Driver Ports
    //----------------------------------------------------------------------------------------------
    .TXMARGIN                           (GT_TXMARGIN),                                           
    .TXSWING                            (GT_TXSWING),                                            
    .TXDEEMPH                           (GT_TXDEEMPH),                                                                     
    .TXDIFFCTRL                         (5'h14), //( 5'b11111), 
    .TXINHIBIT                          ( 1'd0),                                                  

    //----------------------------------------------------------------------------------------------
    //  TX Driver Ports (Gen3)
    //----------------------------------------------------------------------------------------------
    .TXPRECURSOR                        (GT_TXPRECURSOR),                                          
    .TXMAINCURSOR                       (GT_TXMAINCURSOR),                                         
    .TXPOSTCURSOR                       (GT_TXPOSTCURSOR),                                                                                     

    //----------------------------------------------------------------------------------------------
    //  PCS Reserved Ports
    //---------------------------------------------------------------------------------------------- 
    .PCSRSVDIN                          (16'h0001),                             // CHECK                                                                               
    .PCSRSVDOUT                         (pcsrsvdout),     
    
    //----------------------------------------------------------------------------------------------
    //  RX Monitor Ports
    //----------------------------------------------------------------------------------------------
    .RXMONITORSEL                       ( 2'd0), 
    .RXMONITOROUT                       (),                                                                                                                                                                                                            
                                                                 
    //----------------------------------------------------------------------------------------------
    //  Comma Detect & Align Ports
    //----------------------------------------------------------------------------------------------
    .RXCOMMADETEN                       ( 1'd1),                  
    .RXMCOMMAALIGNEN                    (!pcierategen3),          
    .RXPCOMMAALIGNEN                    (!pcierategen3),          
                                                                                 
    .RXCOMMADET                         (),                                            
    .RXBYTEISALIGNED                    (),                                        
    .RXBYTEREALIGN                      (),                                                                                                                 
                                                                                                    
    //----------------------------------------------------------------------------------------------
    // 8B10B Ports
    //----------------------------------------------------------------------------------------------
    .TX8B10BBYPASS                      ( 8'd0),                                                  
    .TX8B10BEN                          (!pcierategen3),                            
    .RX8B10BEN                          (!pcierategen3),                            
           
    //----------------------------------------------------------------------------------------------
    //  TX Buffer Ports
    //----------------------------------------------------------------------------------------------
    .TXBUFSTATUS                        (),                                                        
                                                                                                    
    //----------------------------------------------------------------------------------------------
    //  RX Buffer Ports
    //----------------------------------------------------------------------------------------------
    .RXBUFRESET                         (GT_RXBUFRESET),                                          
    .RXBUFSTATUS                        (),                
                      
    //----------------------------------------------------------------------------------------------
    //  Clock Correction Ports
    //----------------------------------------------------------------------------------------------
    .RXCLKCORCNT                        (),                            
                    
    //----------------------------------------------------------------------------------------------
    //  Channel Bonding Ports (disable)
    //----------------------------------------------------------------------------------------------
    .RXCHBONDEN                         ( 1'd0),                                         
    .RXCHBONDI                          ( 5'd0),                                         
    .RXCHBONDLEVEL                      ( 3'd0),                                         
    .RXCHBONDMASTER                     ( 1'd0),                                         
    .RXCHBONDSLAVE                      ( 1'd0),                                         
                                                                                    
    .RXCHANBONDSEQ                      (),                                         
    .RXCHANISALIGNED                    (),                                         
    .RXCHANREALIGN                      (),                                         
    .RXCHBONDO                          (),                                                                                                                                                                       
 
    //----------------------------------------------------------------------------------------------
    //  TX Phase Alignment Ports
    //----------------------------------------------------------------------------------------------
    .TXPHALIGN                          ( 1'd0),
    .TXPHALIGNEN                        ( 1'd0),
    .TXPHDLYPD                          ( 1'd0),
    .TXPHDLYRESET                       ( 1'd0),
    .TXPHDLYTSTCLK                      ( 1'd0),
    .TXPHINIT                           ( 1'd0),
    .TXPHOVRDEN                         ( 1'd0),
   
    .TXPHALIGNDONE                      (GT_TXPHALIGNDONE),
    .TXPHINITDONE                       (),
   
    //----------------------------------------------------------------------------------------------
    //  TX Delay Alignment Ports
    //----------------------------------------------------------------------------------------------
    .TXDLYBYPASS                        ( 1'd0),
    .TXDLYEN                            ( 1'd0),
    .TXDLYHOLD                          ( 1'd0),
    .TXDLYOVRDEN                        ( 1'd0),
    .TXDLYSRESET                        ( 1'd0),
    .TXDLYUPDOWN                        ( 1'd0),
       
    .TXDLYSRESETDONE                    (),       
          
    //----------------------------------------------------------------------------------------------
    //  TX Auto Sync Alignment Ports 
    //----------------------------------------------------------------------------------------------
    .TXSYNCALLIN                        (GT_TXSYNCALLIN),
    .TXSYNCIN                           (GT_TXSYNCIN),
    .TXSYNCMODE                         (MASTER_LANE),                                         
                
    .TXSYNCDONE                         (),
    .TXSYNCOUT                          (GT_TXSYNCOUT),

    //----------------------------------------------------------------------------------------------
    //  RX Phase Alignment Ports (disable)
    //----------------------------------------------------------------------------------------------
    .RXPHALIGN                          ( 1'd0),
    .RXPHALIGNEN                        ( 1'd0),
    .RXPHDLYPD                          ( 1'd0),
    .RXPHDLYRESET                       ( 1'd0),
    .RXPHOVRDEN                         ( 1'd0),
   
    .RXPHALIGNDONE                      (),
    .RXPHALIGNERR                       (),
       
    //----------------------------------------------------------------------------------------------
    //  RX Delay Alignment Ports (disable)
    //----------------------------------------------------------------------------------------------
    .RXDLYBYPASS                        ( 1'd1),
    .RXDLYEN                            ( 1'd0),
    .RXDLYOVRDEN                        ( 1'd0),
    .RXDLYSRESET                        ( 1'd0),
   
    .RXDLYSRESETDONE                    (),                                           
        
    //----------------------------------------------------------------------------------------------
    //  RX Auto Sync Alignment Ports (disable)
    //----------------------------------------------------------------------------------------------
    .RXSYNCALLIN                        ( 1'd0),
    .RXSYNCIN                           ( 1'd0),
    .RXSYNCMODE                         ( 1'd0),                                                    
                                                                                                    
    .RXSYNCDONE                         (),                                                
    .RXSYNCOUT                          (),    
       
    //----------------------------------------------------------------------------------------------
    //  Gearbox Ports 
    //----------------------------------------------------------------------------------------------
    .TXHEADER                           ( 6'd0), 
    .TXLATCLK                           ( 1'd0),                                                    
    .TXSEQUENCE                         ( 7'd0),                                                    
    .RXGEARBOXSLIP                      ( 1'd0),  
    .RXLATCLK                           ( 1'd0),  
    .RXSLIDE                            ( 1'd0),                                                    
                                                                                                    
    .RXDATAVALID                        (),                 
    .RXHEADER                           (),                                                         
    .RXHEADERVALID                      (), 
    .RXSLIDERDY                         (),                                                         
    .RXSTARTOFSEQ                       (),                             
                   
    //----------------------------------------------------------------------------------------------
    //  RX Slip Ports 
    //----------------------------------------------------------------------------------------------
    .RXSLIPOUTCLK                       ( 1'd0),
    .RXSLIPPMA                          ( 1'd0),   
                                                                   
    .RXSLIPDONE                         (),     
    .RXSLIPOUTCLKRDY                    (),
    .RXSLIPPMARDY                       (),             
       
    //----------------------------------------------------------------------------------------------
    //  RX LPM Ports 
    //----------------------------------------------------------------------------------------------
    .RXLPMEN                            (!pcierategen3),    
    .RXLPMGCHOLD                        ( 1'b0),            
    .RXLPMGCOVRDEN                      ( 1'b0),
    .RXLPMHFHOLD                        ( 1'b0),            
    .RXLPMHFOVRDEN                      ( 1'b0),
    .RXLPMLFHOLD                        ( 1'b0),         
    .RXLPMLFKLOVRDEN                    ( 1'b0), 
    .RXLPMOSHOLD                        ( 1'b0),            
    .RXLPMOSOVRDEN                      ( 1'b0),
                                                                                                    
    //----------------------------------------------------------------------------------------------
    //  RX DFE Ports
    //----------------------------------------------------------------------------------------------
    .RXDFEAGCCTRL                       ( 2'h1), //( 2'b00),   
    .RXDFEAGCHOLD                       ( 1'b0),            
    .RXDFEAGCOVRDEN                     ( 1'b0),
    .RXDFECFOKFCNUM                     ( 4'b0000),                             
    .RXDFECFOKFEN                       ( 1'b0),                                
    .RXDFECFOKFPULSE                    ( 1'b0),                                
    .RXDFECFOKHOLD                      ( 1'b0),                                
    .RXDFECFOKOVREN                     ( 1'b0),                                
    .RXDFEKHHOLD                        ( 1'b0),
    .RXDFEKHOVRDEN                      ( 1'b0),
    .RXDFELFHOLD                        ( 1'b0),          
    .RXDFELFOVRDEN                      ( 1'b0),
    .RXDFELPMRESET                      (GT_RXDFELPMRESET),
    .RXDFETAP2HOLD                      ( 1'b0),
    .RXDFETAP2OVRDEN                    ( 1'b0),
    .RXDFETAP3HOLD                      ( 1'b0),
    .RXDFETAP3OVRDEN                    ( 1'b0),
    .RXDFETAP4HOLD                      ( 1'b0),
    .RXDFETAP4OVRDEN                    ( 1'b0),
    .RXDFETAP5HOLD                      ( 1'b0),
    .RXDFETAP5OVRDEN                    ( 1'b0),
    .RXDFETAP6HOLD                      ( 1'b0),
    .RXDFETAP6OVRDEN                    ( 1'b0),
    .RXDFETAP7HOLD                      ( 1'b0),
    .RXDFETAP7OVRDEN                    ( 1'b0),
    .RXDFETAP8HOLD                      ( 1'b0),
    .RXDFETAP8OVRDEN                    ( 1'b0),
    .RXDFETAP9HOLD                      ( 1'b0),
    .RXDFETAP9OVRDEN                    ( 1'b0),
    .RXDFETAP10HOLD                     ( 1'b0),
    .RXDFETAP10OVRDEN                   ( 1'b0),
    .RXDFETAP11HOLD                     ( 1'b0),
    .RXDFETAP11OVRDEN                   ( 1'b0),
    .RXDFETAP12HOLD                     ( 1'b0),
    .RXDFETAP12OVRDEN                   ( 1'b0),
    .RXDFETAP13HOLD                     ( 1'b0),
    .RXDFETAP13OVRDEN                   ( 1'b0),
    .RXDFETAP14HOLD                     ( 1'b0),
    .RXDFETAP14OVRDEN                   ( 1'b0),
    .RXDFETAP15HOLD                     ( 1'b0),
    .RXDFETAP15OVRDEN                   ( 1'b0),
    .RXDFEUTHOLD                        ( 1'b0),
    .RXDFEUTOVRDEN                      ( 1'b0),
    .RXDFEVPHOLD                        ( 1'b0),
    .RXDFEVPOVRDEN                      ( 1'b0),
    .RXDFEXYDEN                         ( 1'b1),                                                                                                    
    
    //----------------------------------------------------------------------------------------------
    //  TX PI Ports
    //----------------------------------------------------------------------------------------------
    .TXPIPPMEN                          ( 1'd0),
    .TXPIPPMOVRDEN                      ( 1'd0),
    .TXPIPPMPD                          ( 1'd0),
    .TXPIPPMSEL                         ( 1'd0),
    .TXPIPPMSTEPSIZE                    ( 5'd0),
    .TXPISOPD                           ( 1'd0),   
    
    //----------------------------------------------------------------------------------------------
    //  RX CDR Ports
    //----------------------------------------------------------------------------------------------
    .CDRSTEPDIR                         ( 1'b0),                                 
    .CDRSTEPSQ                          ( 1'b0),                                
    .CDRSTEPSX                          ( 1'b0),                               
    .RXCDRFREQRESET                     (GT_RXCDRFREQRESET),   //*****
    .RXCDRHOLD                          (GT_RXCDRHOLD),
    .RXCDROVRDEN                        ( 1'd0),
    .RXCDRRESET                         (rxcdrreset_int),
    
    .RXCDRLOCK                          (GT_RXCDRLOCK),    
    .RXCDRPHDONE                        (), 
       
    //----------------------------------------------------------------------------------------------
    //  Eye Scan Ports
    //----------------------------------------------------------------------------------------------                                          
    .EYESCANRESET                       ( 1'd0),                                             
    .EYESCANTRIGGER                     ( 1'd0),                                             
                                                                                            
    .EYESCANDATAERROR                   (),           
       
    //----------------------------------------------------------------------------------------------
    //  RX OS Ports
    //----------------------------------------------------------------------------------------------
    .RXOSCALRESET                       ( 1'b0),
    .RXOSHOLD                           ( 1'b0),
    .RXOSOVRDEN                         ( 1'b0),    
 
    .RXOSINTDONE                        (),                                                         
    .RXOSINTSTARTED                     (),                                                         
    .RXOSINTSTROBEDONE                  (),                                                         
    .RXOSINTSTROBESTARTED               (),         
           
    //----------------------------------------------------------------------------------------------
    //  DRP Ports
    //----------------------------------------------------------------------------------------------
    .DRPCLK                             (GT_DRPCLK), 
    .DRPRST                             ( 1'd0),                                                                                
    .DRPADDR                            (GT_DRPADDR),                                                    
    .DRPEN                              (GT_DRPEN),                                                    
    .DRPWE                              (GT_DRPWE), 
    .DRPDI                              (GT_DRPDI),                                                    
        
    .DRPRDY                             (GT_DRPRDY),                                                         
    .DRPDO                              (GT_DRPDO),                      
 
    //----------------------------------------------------------------------------------------------
    //  Loopback & PRBS Ports
    //----------------------------------------------------------------------------------------------
    .LOOPBACK                           (GT_LOOPBACK),      
    .TXPRBSSEL                          (GT_PRBSSEL),                                                    
    .RXPRBSSEL                          (GT_PRBSSEL),  
    .TXPRBSFORCEERR                     (GT_TXPRBSFORCEERR),  
    .RXPRBSCNTRESET                     (GT_RXPRBSCNTRESET),  
                   
    .RXPRBSERR                          (GT_RXPRBSERR),                                                
    .RXPRBSLOCKED                       (GT_RXPRBSLOCKED),       

    //----------------------------------------------------------------------------------------------
    //  Digital Monitor Ports                                                                             
    //----------------------------------------------------------------------------------------------
    .DMONFIFORESET                      ( 1'd0),                                                    
    .DMONITORCLK                        ( 1'd0),                                                    
    
    .DMONITOROUT                        (),    
    .DMONITOROUTCLK                     (),                                             
      
    //----------------------------------------------------------------------------------------------
    //  USB Ports
    //----------------------------------------------------------------------------------------------
    .TXONESZEROS                        (GT_TXONESZEROS),
    .RXEQTRAINING                       (GT_RXEQTRAINING),
    .RXTERMINATION                      (GT_RXTERMINATION),    
    
    .POWERPRESENT                       (GT_POWERPRESENT),           
        
    //----------------------------------------------------------------------------------------------
    //  USB LFPS Ports
    //----------------------------------------------------------------------------------------------
    .TXLFPSTRESET                       ( 1'b0),      
    .TXLFPSU2LPEXIT                     ( 1'b0),
    .TXLFPSU3WAKE                       ( 1'b0),
    
    .RXLFPSTRESETDET                    (),             
    .RXLFPSU2LPEXITDET                  (),             
    .RXLFPSU3WAKEDET                    (),            
      
    //----------------------------------------------------------------------------------------------
    //  SATA Ports 
    //----------------------------------------------------------------------------------------------
    .TXCOMINIT                          ( 1'd0),                                                    
    .TXCOMSAS                           ( 1'd0),                                                    
    .TXCOMWAKE                          ( 1'd0),                                                    

    .TXCOMFINISH                        (),                                                         
    .RXCOMINITDET                       (),                                                         
    .RXCOMSASDET                        (),                                                         
    .RXCOMWAKEDET                       (),                                                    

    //----------------------------------------------------------------------------------------------
    //  QPI
    //----------------------------------------------------------------------------------------------
    .RXQPIEN                            ( 1'd0),
    .TXQPIBIASEN                        ( 1'b0),                                
    .TXQPIWEAKPUP                       ( 1'b0),                              
    
    .RXQPISENN                          (),
    .RXQPISENP                          (),
    .TXQPISENN                          (),
    .TXQPISENP                          (),

    //----------------------------------------------------------------------------------------------
    //  GT Ports
    //----------------------------------------------------------------------------------------------
    .FREQOS                             ( 1'd0),    
    .GTRSVD                             (16'd0),
    .INCPCTRL                           ( 1'd0),
    .RXAFECFOKEN                        ( 1'd0),                                
    .RXCKCALRESET                       ( 1'b0),                                
    .RXCKCALSTART                       ( 7'd0),                                
    .TSTIN                              (20'h00000),                                                
    .TXDCCFORCESTART                    ( 1'b0),                                
    .TXDCCRESET                         ( 1'b0),                                
    .TXMUXDCDEXHOLD                     ( 1'b0),                                
    .TXMUXDCDORWREN                     ( 1'b0),                                
                                                                                   
    .PINRSRVDAS                         (),                                     
    .RXCKCALDONE                        (),                                     
    .TXDCCDONE                          ()                                      
);

end
endgenerate

    
//--------------------------------------------------------------------------------------------------
//  Input Port Remapping
//--------------------------------------------------------------------------------------------------    
assign txdata[ 63: 0] = GT_TXDATA;
assign txdata[127:64] = 64'd0;

assign txctrl0[ 1:0] = 2'd0;
assign txctrl0[   2] = GT_TXDATA_VALID;
assign txctrl0[   3] = GT_TXSTART_BLOCK;
assign txctrl0[ 5:4] = GT_TXSYNC_HEADER;
assign txctrl0[15:6] = 10'd0;

assign txctrl1[   0] = GT_TXCOMPLIANCE;
assign txctrl1[15:1] = 15'd0;

assign txctrl2[ 1:0] = GT_TXDATAK;
assign txctrl2[ 7:2] = 6'd0;



//--------------------------------------------------------------------------------------------------
//  GT Channel Outputs
//--------------------------------------------------------------------------------------------------
assign GT_RXDATA         = rxdata[63:0];

assign GT_RXDATAK        = rxctrl0[1:0];
assign GT_RXDATA_VALID   = rxctrl0[2];
assign GT_RXSTART_BLOCK  = {rxctrl0[6], rxctrl0[3]};
assign GT_RXSYNC_HEADER  = rxctrl0[5:4];
assign GT_GEN34_EIOS_DET = rxctrl0[7]; 

assign GT_PCIERATEGEN3   = pcierategen3;
assign GT_QPLLRATE       = pcsrsvdout[2:0];
                        
assign GT_RXELECIDLE = rxelecidle_int;

endmodule


