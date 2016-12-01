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
// File       : pcie4_uscale_plus_0_gt_phy_wrapper.v
// Version    : 1.1 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
//  Design  :  Diablo PHY Wrapper REFERENCE DESIGN
//  Module  :  PHY Wrapper Top
//--------------------------------------------------------------------------------------------------
//  *** XILINX INTERNAL *** 
//--------------------------------------------------------------------------------------------------
//  Version :  0.73
//--------------------------------------------------------------------------------------------------

//--------------------------------------------------------------------------------------------------
//  PHY Wrapper Design Hierarchy in Static Mode
//--------------------------------------------------------------------------------------------------
//  PHY Wrapper Top :
//      - Clock 
//      - Reset
//      - PHY Lane :
//          - TX Equalization (Gen3/Gen4)
//          - RX Equalization (Gen3/Gen4)
//          - GT Channel (one channel for every lane)
//      - PHY Quad :
//          - GT Common (one quad for every four lanes)
//--------------------------------------------------------------------------------------------------

//--------------------------------------------------------------------------------------------------
//  PHY Wrapper Design Hierarchy in GT Wizard Mode
//--------------------------------------------------------------------------------------------------
//  PHY Wrapper Top :
//      - Clock 
//      - Reset
//      - PHY Lane :
//          - TX Equalization (Gen3/Gen4)
//          - RX Equalization (Gen3/Gen4)
//      - GT Wizard Top :
//          - GT Wizard Core
//              - GT Channel (one channel for every lane)
//              - GT Common (one quad for every four lanes)
//--------------------------------------------------------------------------------------------------

//--------------------------------------------------------------------------------------------------
//  PHY Wrapper User Parameter Encoding
//--------------------------------------------------------------------------------------------------
//  PHY_SIM_EN                : "FALSE" = Normal
//                            : "TRUE"  = Simulation
//  PHY_GT_XCVR               : "GTH" = GTH Transceiver
//                            : "GTY" = GTY Transceiver
//                            : "GTY64" = GTY with 64-bit support for PCIe Gen4
//  PHY_MODE                  : 0 = PCIe 4.0
//                            : 1 = USB  3.0
//  PHY_REFCLK_MODE           : 0 =          0 ppm (Common   REFCLK)
//                            : 1 = up to  600 ppm (Seperate REFCLK without SSC)
//                            : 2 = up to 5600 ppm (Seperate REFCLK with independent SSC)
//  PHY_GTWIZARD              : "FALSE" = Use Static Wrapper mode
//                            : "TRUE"  = Use GT Wizard Generated Wrapper mode
//  PHY_LANE                  : 1, 2, 4, 8, 16 
//  PHY_MAX_SPEED             : 1 = PCIe Gen1 ( 2.5 Gbps) Capable or USB3 Gen1 ( 5.0 Gb/s)        
//                            : 2 = PCIe Gen2 ( 5.0 Gbps) Capable
//                            : 3 = PCIe Gen3 ( 8.0 Gbps) Capable 
//                            : 4 = PCIe Gen4 (16.0 Gbps) Capable
//  PHY_GEN12_CDR_CTRL_ON_EIDLE : "FALSE" = Will not auto reset CDR upon EIOS detection (Gen1/Gen2)
//                            : "TRUE"  = Will     auto reset CDR upon EIOS detection (Gen1/Gen2)
//  PHY_GEN34_CDR_CTRL_ON_EIDLE : "FALSE" = Will not auto reset CDR upon EIOS detection (Gen3/Gen4)
//                            : "TRUE"  = Will     auto reset CDR upon EIOS detection (Gen3/Gen4)
//  PHY_REFCLK_FREQ           : 0 = 100.0 MHz 
//                            : 1 = 125.0 MHz
//                            : 2 = 250.0 MHz
//  PHY_CORECLK_FREQ          : 1 = 250.0 MHz
//                            : 2 = 500.0 MHz
//  PHY_USERCLK_FREQ          : 1 =  62.5 MHz
//                            : 2 = 125.0 MHz
//                            : 3 = 250.0 MHz
//                            : 4 = 500.0 MHz
//  PHY_MCAPCLK_FREQ          : 1 =  62.5 MHz
//                            : 2 = 125.0 MHz
//                            : 3 = 250.0 MHz
//                            : 4 = 500.0 MHz
//  PHY_GT_TXPRESET           : 0 to 10 
//  PHY_LP_TXPRESET           : 0 to 10 
//--------------------------------------------------------------------------------------------------

`timescale 1ps / 1ps

//--------------------------------------------------------------------------------------------------
//  PHY Wrapper Top
//--------------------------------------------------------------------------------------------------
(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie4_uscale_plus_0_gt_phy_wrapper #
(
    //--------------------------------------------------------------------------
    //  Parameters
    //--------------------------------------------------------------------------
    parameter         PHY_SIM_EN                 = "FALSE",   
    parameter         PHY_GT_XCVR                = "GTY",
    parameter         PHY_GTWIZARD               = "TRUE",
    parameter integer PHY_MODE                   = 0,  
    parameter integer PHY_REFCLK_MODE            = 0,       
    parameter integer PHY_LANE                   = 1,   
    parameter integer PHY_MAX_SPEED              = 4,  
    parameter         PHY_GEN12_CDR_CTRL_ON_EIDLE = "TRUE",                
    parameter         PHY_GEN34_CDR_CTRL_ON_EIDLE = "TRUE",     
    parameter integer PHY_REFCLK_FREQ            = 0, 
    parameter integer PHY_CORECLK_FREQ           = 2,       
    parameter integer PHY_USERCLK_FREQ           = 4,           
    parameter integer PHY_MCAPCLK_FREQ           = 4,    
    parameter integer PHY_GT_TXPRESET            = 0,
    parameter integer PHY_LP_TXPRESET            = 4         
)                                                            
(                                         


    //--------------------------------------------------------------------------
    //  Clock & Reset Ports
    //--------------------------------------------------------------------------
    input                               PHY_REFCLK,                             // For PHY Wrapper
    input                               PHY_GTREFCLK,                           // For GT
    input                               PHY_RST_N,                              // System RST
   
    output                              PHY_PCLK,                               
    output                              PHY_PCLK2,                              // For PCIe IP                          
    output                              PHY_CORECLK,                            // For PCIe IP
    output                              PHY_USERCLK,                            // For PCIe IP
    output                              PHY_MCAPCLK,                            // For PCIe IP
  
    //--------------------------------------------------------------------------
    //  Serial Line Ports
    //--------------------------------------------------------------------------
    input       [PHY_LANE-1:0]          PHY_RXP,               
    input       [PHY_LANE-1:0]          PHY_RXN,               

    output      [PHY_LANE-1:0]          PHY_TXP,               
    output      [PHY_LANE-1:0]          PHY_TXN,   
 
    //--------------------------------------------------------------------------
    //  TX Data Ports 
    //--------------------------------------------------------------------------
    input       [(PHY_LANE*64)-1:0]     PHY_TXDATA,         
    input       [(PHY_LANE* 2)-1:0]     PHY_TXDATAK,    
    input       [PHY_LANE-1:0]          PHY_TXDATA_VALID,
    input       [PHY_LANE-1:0]          PHY_TXSTART_BLOCK,      
    input       [(PHY_LANE* 2)-1:0]     PHY_TXSYNC_HEADER,                    

    //--------------------------------------------------------------------------
    //  RX Data Ports 
    //--------------------------------------------------------------------------
    output      [(PHY_LANE*64)-1:0]     PHY_RXDATA,         
    output      [(PHY_LANE* 2)-1:0]     PHY_RXDATAK,       
    output      [PHY_LANE-1:0]          PHY_RXDATA_VALID,         
    output      [(PHY_LANE* 2)-1:0]     PHY_RXSTART_BLOCK,  
    output      [(PHY_LANE* 2)-1:0]     PHY_RXSYNC_HEADER,
    
    //--------------------------------------------------------------------------
    //  PHY Command Port
    //--------------------------------------------------------------------------
    input                               PHY_TXDETECTRX,        
    input       [PHY_LANE-1:0]          PHY_TXELECIDLE,        
    input       [PHY_LANE-1:0]          PHY_TXCOMPLIANCE,      
    input       [PHY_LANE-1:0]          PHY_RXPOLARITY,        
    input       [1:0]                   PHY_POWERDOWN,         
    input                               PHY_RXCDRHOLD,                          // For Gen3/Gen4 RX EQ             
    
    //--------------------------------------------------------------------------   
    //  PHY Status Ports
    //-------------------------------------------------------------------------- 
    output      [PHY_LANE-1:0]          PHY_RXVALID,               
    output      [PHY_LANE-1:0]          PHY_PHYSTATUS,          
    output                              PHY_PHYSTATUS_RST,                      // For PCIe IP
    output      [PHY_LANE-1:0]          PHY_RXELECIDLE,         
    output      [(PHY_LANE*3)-1:0]      PHY_RXSTATUS,                       
    
    //--------------------------------------------------------------------------
    //  TX Driver Ports
    //--------------------------------------------------------------------------
    input       [ 2:0]                  PHY_TXMARGIN,          
    input                               PHY_TXSWING,           
    input       [ 1:0]                  PHY_TXDEEMPH,    
    
    //--------------------------------------------------------------------------   
    //  TX Equalization Ports (Gen3/Gen4)
    //--------------------------------------------------------------------------  
    input       [(PHY_LANE*2)-1:0]      PHY_TXEQ_CTRL,      
    input       [(PHY_LANE*4)-1:0]      PHY_TXEQ_PRESET,       
    input       [(PHY_LANE*6)-1:0]      PHY_TXEQ_COEFF,                                                            

    output      [ 5:0]                  PHY_TXEQ_FS,           
    output      [ 5:0]                  PHY_TXEQ_LF,           
    output      [(PHY_LANE*18)-1:0]     PHY_TXEQ_NEW_COEFF,        
    output      [PHY_LANE-1:0]          PHY_TXEQ_DONE,         

    //--------------------------------------------------------------------------
    //  RX Equalization Ports (Gen3/Gen4)
    //--------------------------------------------------------------------------                                                
    input       [(PHY_LANE*2)-1:0]      PHY_RXEQ_CTRL,     
    input       [(PHY_LANE*3)-1:0]      PHY_RXEQ_PRESET,  
    input       [(PHY_LANE*4)-1:0]      PHY_RXEQ_TXPRESET,      
    input       [(PHY_LANE*6)-1:0]      PHY_RXEQ_LFFS,                                                         

    output      [PHY_LANE-1:0]          PHY_RXEQ_LFFS_SEL,    
    output      [(PHY_LANE*18)-1:0]     PHY_RXEQ_NEW_TXCOEFF,   
    output      [PHY_LANE-1:0]          PHY_RXEQ_ADAPT_DONE,     
    output      [PHY_LANE-1:0]          PHY_RXEQ_DONE,         
    
    //--------------------------------------------------------------------------
    //  GT Channel Ports (USB3)
    //--------------------------------------------------------------------------
    input       [PHY_LANE-1:0]          USB_TXONESZEROS,                        
    input       [PHY_LANE-1:0]          USB_RXEQTRAINING,                       
    input       [PHY_LANE-1:0]          USB_RXTERMINATION,                        
    
    output      [PHY_LANE-1:0]          USB_POWERPRESENT,    
    
    //--------------------------------------------------------------------------   
    //  IBERT ports 
    //--------------------------------------------------------------------------                   
     input [(PHY_LANE * 5) -1:0]         ibert_txprecursor_in, 
     input [(PHY_LANE * 5) -1:0]         ibert_txpostcursor_in, 
     input [PHY_LANE-1:0]                ibert_eyescanreset_in, 
     input [(PHY_LANE * 5) -1:0]         ibert_txdiffctrl_in, 
     input [PHY_LANE-1:0]                ibert_rxlpmen_in, 
     input       [1:0]                   PHY_RATE,    

    output        [(PHY_LANE*5)-1:0]      txeq_precursor, 
    output        [(PHY_LANE*5)-1:0]      txeq_postcursor, 
    output        [PHY_LANE-1:0]          gt_pcierategen3,  
    //--------------------------------------------------------------------------
    //  GT Channel DRP Ports 
    //--------------------------------------------------------------------------
    output                               GT_DRPCLK,
    input        [(PHY_LANE*10)-1:0]     GT_DRPADDR,
    input        [PHY_LANE-1:0]          GT_DRPEN,
    input        [PHY_LANE-1:0]          GT_DRPWE,
    input        [(PHY_LANE*16)-1:0]     GT_DRPDI,

    output       [PHY_LANE-1:0]          GT_DRPRDY,
    output       [(PHY_LANE*16)-1:0]     GT_DRPDO,  
    //--------------------------------------------------------------------------
    //  GT Common DRP Ports 
    //--------------------------------------------------------------------------
    input       [((((PHY_LANE-1)>>2)+1)*16)-1:0]    GTCOM_DRPADDR,                                       
    input       [   (PHY_LANE-1)>>2          :0]    GTCOM_DRPEN,                                             
    input       [   (PHY_LANE-1)>>2          :0]    GTCOM_DRPWE,     
    input       [((((PHY_LANE-1)>>2)+1)*16)-1:0]    GTCOM_DRPDI,                                      
                                                                         
    output      [   (PHY_LANE-1)>>2          :0]    GTCOM_DRPRDY,    
    output      [((((PHY_LANE-1)>>2)+1)*16)-1:0]    GTCOM_DRPDO,       
    //----------------------------------------------------------------------------------------------
    //  GT Debug Ports
    //----------------------------------------------------------------------------------------------       
    input       [PHY_LANE-1:0]          DBG_RATE_DONE,
    
    output      [PHY_LANE-1:0]          DBG_RATE_START,             
    output      [PHY_LANE-1:0]          DBG_RATE_IDLE,
    output      [PHY_LANE-1:0]          DBG_RXCDRLOCK,     
    output      [PHY_LANE-1:0]          DBG_GEN34_EIOS_DET, 
    output      [PHY_LANE-1:0]          GT_TXPHINITDONE    ,         
    
    //--------------------------------------------------------------------------
    // CLK Debug Ports (Requires BUFG if used)
    //--------------------------------------------------------------------------
    output      [PHY_LANE-1:0]          DBG_TXOUTCLK, 
    output      [PHY_LANE-1:0]          DBG_RXOUTCLK, 
    output      [PHY_LANE-1:0]          DBG_TXOUTCLKFABRIC,                                                              
    output      [PHY_LANE-1:0]          DBG_RXOUTCLKFABRIC,                                                              
    output      [PHY_LANE-1:0]          DBG_TXOUTCLKPCS,                                                              
    output      [PHY_LANE-1:0]          DBG_RXOUTCLKPCS,                 
    output      [PHY_LANE-1:0]          DBG_RXRECCLKOUT, 
        
    //--------------------------------------------------------------------------
    // RST Debug Ports
    //--------------------------------------------------------------------------     
    input       [PHY_LANE-1:0]          DBG_TXPMARESET,                                            
    input       [PHY_LANE-1:0]          DBG_RXPMARESET,                                            
    input       [PHY_LANE-1:0]          DBG_TXPCSRESET,   
    input       [PHY_LANE-1:0]          DBG_RXPCSRESET,
    input       [PHY_LANE-1:0]          DBG_RXBUFRESET,
    input       [PHY_LANE-1:0]          DBG_RXCDRRESET,
    input       [PHY_LANE-1:0]          DBG_RXDFELPMRESET,
   
    output                              DBG_RRST_N,
    output                              DBG_PRST_N,       
    output      [PHY_LANE-1:0]          DBG_GTPOWERGOOD,  
    output      [PHY_LANE-1:0]          DBG_CPLLLOCK,      
    output      [(PHY_LANE-1)>>2:0]     DBG_QPLL0LOCK,    
    output      [(PHY_LANE-1)>>2:0]     DBG_QPLL1LOCK,  
    output      [PHY_LANE-1:0]          DBG_TXPROGDIVRESETDONE,
    output      [PHY_LANE-1:0]          DBG_TXPMARESETDONE,   
    output      [PHY_LANE-1:0]          DBG_RXPMARESETDONE, 
    output      [PHY_LANE-1:0]          DBG_TXRESETDONE,
    output      [PHY_LANE-1:0]          DBG_RXRESETDONE,    
    output      [PHY_LANE-1:0]          DBG_TXSYNCDONE,  
    output                              DBG_RST_IDLE,               
    output      [PHY_LANE-1:0]          GT_RXPHALIGNDONE,        
    output      [PHY_LANE-1:0]          GT_TXPHALIGNDONE,            

    input       [PHY_LANE-1:0]          GT_DMONFIFORESET,
    input       [PHY_LANE-1:0]          GT_DMONITORCLK,
    output      [(PHY_LANE*16)-1:0]     GT_DMONITOROUT,           
    output      [8:0]                   GT_BUFGTDIV,                 
    //--------------------------------------------------------------------------
    //  PRBS Debug Ports
    //--------------------------------------------------------------------------
    input       [(PHY_LANE*3)-1:0]      GT_LOOPBACK,             
    input       [PHY_LANE-1:0]          GT_TXINHIBIT,            
    input       [(PHY_LANE*4)-1:0]      DBG_PRBSSEL,
    input       [PHY_LANE-1:0]          DBG_TXPRBSFORCEERR,
    input       [PHY_LANE-1:0]          DBG_RXPRBSCNTRESET,                                                                                                      

    output      [PHY_LANE-1:0]          DBG_RXPRBSERR,                                              
    output      [PHY_LANE-1:0]          DBG_RXPRBSLOCKED,
    
    output      [PHY_LANE-1:0]          GT_RXCOMMADET,                   
    output      [(PHY_LANE*3)-1:0]      GT_RXBUFSTATUS,            

    output      [3:0]                   PHY_RST_FSM,                 
    output      [(PHY_LANE*3)-1:0]      PHY_TXEQ_FSM,                  
    output      [(PHY_LANE*3)-1:0]      PHY_RXEQ_FSM,                 

    output      [PHY_LANE-1:0]          GT_RXSYNCDONE,        
    output      [PHY_LANE-1:0]          GT_EYESCANDATAERROR,               
    output      [PHY_LANE-1:0]          GT_TXDLYSRESETDONE,         
    output      [PHY_LANE-1:0]          GT_RXDLYSRESETDONE,          

    //---------------------------------------------------------------------------
    //   Receiver Detect (Remote TX detecting our RX)
    //---------------------------------------------------------------------------
    input                               PHY_PCIE_MAC_IN_DETECT 
);

//--------------------------------------------------------------------------------------------------
//  Internal Signals
//--------------------------------------------------------------------------------------------------

    //--------------------------------------------------------------------------
    //  Clock 
    //--------------------------------------------------------------------------
    wire                                pclk; 
    wire                                pclk2_gt;
  
    //--------------------------------------------------------------------------
    //  Reset
    //--------------------------------------------------------------------------
    wire                                rrst_n;
    wire                                prst_n;
    
    wire                                rst_cpllpd;
    wire                                rst_cpllreset;  
    wire                                rst_qpllpd;  
    wire                                rst_qpllreset;
    wire                                rst_txprogdivreset;
    wire                                rst_gtreset;
    wire                                rst_userrdy; 
    wire                                rst_txsync_start;
    wire                                rst_idle;

    //--------------------------------------------------------------------------
    //  TX Equalization (Gen3/Gen4)
    //-------------------------------------------------------------------------- 
    wire        [(PHY_LANE*7)-1:0]      txeq_maincursor; 
    wire        [(PHY_LANE*18)-1:0]     txeq_new_coeff; 
    wire        [PHY_LANE-1:0]          txeq_done;  
    
    //--------------------------------------------------------------------------
    //  RX Equalization (Gen3/Gen4)
    //-------------------------------------------------------------------------- 
    wire        [PHY_LANE-1:0]          rxeq_lffs_sel;   
    wire        [(PHY_LANE*18)-1:0]     rxeq_new_txcoeff;    
    wire        [PHY_LANE-1:0]          rxeq_adapt_done;     
    wire        [PHY_LANE-1:0]          rxeq_done;   
    
    //--------------------------------------------------------------------------
    //  GT Channel 
    //--------------------------------------------------------------------------
    wire        [PHY_LANE-1:0]          gt_bufgtce;    
    wire        [(PHY_LANE*3)-1:0]      gt_bufgtcemask;
    wire        [PHY_LANE-1:0]          gt_bufgtreset;
    wire        [(PHY_LANE*3)-1:0]      gt_bufgtrstmask;   
    wire        [(PHY_LANE*9)-1:0]      gt_bufgtdiv;
    wire        [PHY_LANE-1:0]          gt_txoutclk; 

    wire        [PHY_LANE-1:0]          gt_gtpowergood;
    wire        [PHY_LANE-1:0]          gt_txprogdivresetdone;
    wire        [PHY_LANE-1:0]          gt_txresetdone;
    wire        [PHY_LANE-1:0]          gt_rxresetdone;
    
    wire        [(PHY_LANE*3)-1:0]      gt_qpllrate;                           
    
    wire        [PHY_LANE-1:0]          gt_phystatus;
    wire        [PHY_LANE-1:0]          gt_rxelecidle;
    
    wire        [PHY_LANE-1:0]          gt_pcieuserphystatusrst;
    wire        [(PHY_LANE*2)-1:0]      gt_pcierateqpllpd;                 
    wire        [(PHY_LANE*2)-1:0]      gt_pcierateqpllreset;               
    wire        [PHY_LANE-1:0]          gt_pcierateidle;            
    wire        [PHY_LANE-1:0]          gt_pciesynctxsyncdone;                 
    wire        [PHY_LANE-1:0]          gt_pcieusergen3rdy; 
    wire        [PHY_LANE-1:0]          gt_pcieuserratestart;  
    
    wire        [PHY_LANE-1:0]          gt_txphaligndone;                                          
    wire        [PHY_LANE-1:0]          gt_txsyncout;                          
    
    wire        [PHY_LANE-1:0]          gt_cplllock;     
    wire        [PHY_LANE-1:0]          gt_rxcdrlock;    
    
    wire        [PHY_LANE-1:0]          gt_rxcdrhold;
    wire        [PHY_LANE-1:0]          gt_gen34_eios_det;
                                   
    wire        [PHY_LANE-1:0]          gt_rxratedone;
    wire        [PHY_LANE-1:0]          gt_rxtermination;

    //--------------------------------------------------------------------------
    //  GT Common
    //--------------------------------------------------------------------------
    wire        [(PHY_LANE-1)>>2:0]     gtcom_qpll0lock;
    wire        [(PHY_LANE-1)>>2:0]     gtcom_qpll0outclk;          
    wire        [(PHY_LANE-1)>>2:0]     gtcom_qpll0outrefclk;       
                                       
    wire        [(PHY_LANE-1)>>2:0]     gtcom_qpll1lock;
    wire        [(PHY_LANE-1)>>2:0]     gtcom_qpll1outclk;          
    wire        [(PHY_LANE-1)>>2:0]     gtcom_qpll1outrefclk;       

    //--------------------------------------------------------------------------
    //  Signals for GT Common
    //--------------------------------------------------------------------------
    wire        [(PHY_LANE-1)>>2:0]     qpll0pd;                    
    wire        [(PHY_LANE-1)>>2:0]     qpll0reset;                 
    wire        [(PHY_LANE-1)>>2:0]     qpll1pd;                    
    wire        [(PHY_LANE-1)>>2:0]     qpll1reset;                 
                                       
    //--------------------------------------------------------------------------
    //  Signals converted from per lane
    //--------------------------------------------------------------------------
    wire                                qpll0lock_all;                         
    wire                                qpll1lock_all;
    wire                                txsyncallin_all;                       

    //--------------------------------------------------------------------------
    // Reciever Detect RX termination signals 
    //--------------------------------------------------------------------------    
    
    wire        [PHY_LANE-1:0]         rxterm_rxtermination;

    //--------------------------------------------------------------------------
    //  CDR Control signals
    //-------------------------------------------------------------------------- 
    
    wire        [PHY_LANE-1:0]         cdrctrl_rxcdrhold;
    wire        [PHY_LANE-1:0]         cdrctrl_rxcdrfreqreset;
    wire        [PHY_LANE-1:0]         cdrctrl_resetovrd;
    
    //--------------------------------------------------------------------------
    //  PHYSTATUS Reset Synchronizer for PCLK
    //--------------------------------------------------------------------------

    //(* ASYNC_REG = "TRUE", SHIFT_EXTRACT = "NO", keep = "true", max_fanout = 500 *) reg [3:0] rst_psrst_n_r;
   (* SHIFT_EXTRACT = "NO", max_fanout = 500 *) reg [3:0] rst_psrst_n_r;
   
    reg [31:0] cdrhold_shift [PHY_LANE-1:0]; 
    wire [PHY_LANE-1:0] cdrhold_shift_sync;
    wire [PHY_LANE-1:0] rxvalid_new;
    wire [PHY_LANE-1:0] gt_rxvalid;


    //----
    //  
    //----

    wire                                bufg_gt_ce;
    wire                                bufg_gt_reset;
   (* keep = "true" *) wire [2:0]       PHY_TXOUTCLKSEL;

    wire        [(PHY_LANE*2)-1:0]     rate_delayed;  

    assign bufg_gt_ce = rrst_n ? gt_bufgtce[0] : 1'b1;
    assign bufg_gt_reset = !rst_cpllreset ? gt_bufgtreset[0] : 1'b0;
    assign PHY_TXOUTCLKSEL = rst_cpllreset ? 3'h3 : 3'h5; 

   // 64-bit support for PCIe Gen4
    localparam PHY_GEN4_64BIT_EN = (PHY_GT_XCVR == "GTY64") ? "TRUE" : "FALSE";
//--------------------------------------------------------------------------------------------------
//  PHY Clock 
//--------------------------------------------------------------------------------------------------
pcie4_uscale_plus_0_gt_phy_clk #
(
    .PHY_MAX_SPEED                      (PHY_MAX_SPEED),
    .PHY_GEN4_64BIT_EN                  (PHY_GEN4_64BIT_EN),
    .PHY_CORECLK_FREQ                   (PHY_CORECLK_FREQ),   
    .PHY_USERCLK_FREQ                   (PHY_USERCLK_FREQ),  
    .PHY_MCAPCLK_FREQ                   (PHY_MCAPCLK_FREQ) 
)
phy_clk_i
(
    //--------------------------------------------------------------------------
    //  CLK Port
    //--------------------------------------------------------------------------
    .CLK_TXOUTCLK                       (gt_txoutclk[0]),                       // From master lane 0
    .CLK_PCLK2_GT                       (pclk2_gt),                             // To all [TX/RX]USRCLK2

    //--------------------------------------------------------------------------
    //  PCLK Ports
    //--------------------------------------------------------------------------   
    .CLK_PCLK_CE                        (bufg_gt_ce),                  
    .CLK_PCLK_CEMASK                    (gt_bufgtcemask[0]), 
    .CLK_PCLK_CLR                       (bufg_gt_reset),                     
    .CLK_PCLK_CLRMASK                   (gt_bufgtrstmask[0]),   
    .CLK_PCLK_DIV                       (gt_bufgtdiv[2:0]),    
    .CLK_PCLK                           (pclk),
    
    //--------------------------------------------------------------------------
    //  PCLK2 Ports
    //--------------------------------------------------------------------------    
    .CLK_PCLK2_CE                       (bufg_gt_ce),                  
    .CLK_PCLK2_CEMASK                   (gt_bufgtcemask[0]), 
    .CLK_PCLK2_CLR                      (bufg_gt_reset),                     
    .CLK_PCLK2_CLRMASK                  (gt_bufgtrstmask[0]),   
    .CLK_PCLK2_DIV                      (gt_bufgtdiv[8:6]),    
    .CLK_PCLK2                          (PHY_PCLK2),
    
    //--------------------------------------------------------------------------
    //  CORECLK Ports
    //--------------------------------------------------------------------------
    .CLK_CORECLK_CE                     (bufg_gt_ce),                               
    .CLK_CORECLK_CEMASK                 (rst_idle),            
    .CLK_CORECLK_CLR                    (bufg_gt_reset),                     
    .CLK_CORECLK_CLRMASK                (rst_idle),                                        
    .CLK_CORECLK                        (PHY_CORECLK), 
    
    //--------------------------------------------------------------------------
    //  USERCLK Ports
    //--------------------------------------------------------------------------                      
    .CLK_USERCLK_CE                     (bufg_gt_ce),                       
    .CLK_USERCLK_CEMASK                 (rst_idle),
    .CLK_USERCLK_CLR                    (bufg_gt_reset),                     
    .CLK_USERCLK_CLRMASK                (rst_idle),
    .CLK_USERCLK                        (PHY_USERCLK),
    
    //--------------------------------------------------------------------------
    //  MCAPCLK Ports
    //--------------------------------------------------------------------------                     
    .CLK_MCAPCLK_CE                     (bufg_gt_ce),
    .CLK_MCAPCLK_CEMASK                 (rst_idle),
    .CLK_MCAPCLK_CLR                    (bufg_gt_reset),                     
    .CLK_MCAPCLK_CLRMASK                (rst_idle),
    .CLK_MCAPCLK                        (PHY_MCAPCLK) 
);



//--------------------------------------------------------------------------------------------------
//  PHY Reset
//--------------------------------------------------------------------------------------------------
pcie4_uscale_plus_0_gt_phy_rst #
(
    .PHY_LANE                           (PHY_LANE),
    .PHY_MAX_SPEED                      (PHY_MAX_SPEED)            
)
phy_rst_i
(
    //-------------------------------------------------------------------------- 
    //  Input Ports
    //--------------------------------------------------------------------------       
    .RST_REFCLK                         (PHY_REFCLK),   
    .RST_PCLK                           (pclk),                         
    .RST_N                              (PHY_RST_N),  
    .RST_GTPOWERGOOD                    (gt_gtpowergood),                
    .RST_CPLLLOCK                       (gt_cplllock),   
    .RST_QPLL1LOCK                      (gtcom_qpll1lock), 
    .RST_QPLL0LOCK                      (gtcom_qpll0lock),
    .RST_TXPROGDIVRESETDONE             (gt_txprogdivresetdone),                           
    .RST_TXRESETDONE                    (gt_txresetdone), 
    .RST_RXRESETDONE                    (gt_rxresetdone), 
    .RST_TXSYNC_DONE                    (gt_pciesynctxsyncdone),     
    .RST_PHYSTATUS                      (gt_phystatus),                                             

    //-------------------------------------------------------------------------- 
    //  Output Ports
    //--------------------------------------------------------------------------   
    .phy_rst_fsm                        (PHY_RST_FSM),
    .RST_RRST_N                         (rrst_n),
    .RST_PRST_N                         (prst_n), 
    .RST_CPLLPD                         (rst_cpllpd),               
    .RST_CPLLRESET                      (rst_cpllreset),  
    .RST_QPLLPD                         (rst_qpllpd),
    .RST_QPLLRESET                      (rst_qpllreset),  
    .RST_TXPROGDIVRESET                 (rst_txprogdivreset),                              
    .RST_GTRESET                        (rst_gtreset),               
    .RST_USERRDY                        (rst_userrdy),   
    .RST_TXSYNC_START                   (rst_txsync_start),                                
    .RST_IDLE                           (rst_idle)                          
);
   


//--------------------------------------------------------------------------------------------------
//  Generate PHY Lane - Begin
//--------------------------------------------------------------------------------------------------
genvar i;   
    
generate for (i=0; i<PHY_LANE; i=i+1) 

    begin : phy_lane

    
    //----------------------------------------------------------------------------------------------
    //  PHY TX Equalization (Gen3)
    //----------------------------------------------------------------------------------------------
    pcie4_uscale_plus_0_gt_phy_txeq #
    (
        .PHY_GT_TXPRESET                (PHY_GT_TXPRESET)                
    )
    phy_txeq_i
    (
        //---------------------------------------------------------------------- 
        //  Input Ports
        //----------------------------------------------------------------------  
        .TXEQ_CLK                       (pclk),
        .TXEQ_RST_N                     (prst_n),    
        .TXEQ_CTRL                      (PHY_TXEQ_CTRL[(2*i)+1:(2*i)]), 
        .TXEQ_PRESET                    (PHY_TXEQ_PRESET[(4*i)+3:(4*i)]), 
        .TXEQ_COEFF                     (PHY_TXEQ_COEFF[(6*i)+5:(6*i)]),

        //---------------------------------------------------------------------- 
        //  Output Ports
        //----------------------------------------------------------------------   
        .phy_txeq_fsm                   (PHY_TXEQ_FSM[(3*i)+2:(3*i)]),
        .TXEQ_PRECURSOR                 (txeq_precursor[(5*i)+4:(5*i)]),        
        .TXEQ_MAINCURSOR                (txeq_maincursor[(7*i)+6:(7*i)]),       
        .TXEQ_POSTCURSOR                (txeq_postcursor[(5*i)+4:(5*i)]),       
        .TXEQ_NEW_COEFF                 (txeq_new_coeff[(18*i)+17:(18*i)]),          
        .TXEQ_DONE                      (txeq_done[i])      
    );                                                   



    //----------------------------------------------------------------------------------------------
    //  PHY RX Equalization (Gen3)
    //----------------------------------------------------------------------------------------------
    pcie4_uscale_plus_0_gt_phy_rxeq #
    (
        .PHY_SIM_EN                     (PHY_SIM_EN),
        .PHY_LP_TXPRESET                (PHY_LP_TXPRESET)                
    )
    phy_rxeq_i
    (
        //---------------------------------------------------------------------- 
        //  Input Ports
        //----------------------------------------------------------------------  
        .RXEQ_CLK                       (pclk),
        .RXEQ_RST_N                     (prst_n),  
        .RXEQ_CTRL                      (PHY_RXEQ_CTRL[(2*i)+1:(2*i)]), 
        .RXEQ_PRESET                    (PHY_RXEQ_PRESET[(3*i)+2:(3*i)]), 
        .RXEQ_TXPRESET                  (PHY_RXEQ_TXPRESET[(4*i)+3:(4*i)]),
        .RXEQ_TXCOEFF                   (PHY_TXEQ_COEFF[(6*i)+5:(6*i)]),
        .RXEQ_LFFS                      (PHY_RXEQ_LFFS[(6*i)+5:(6*i)]),

        //---------------------------------------------------------------------- 
        //  Output Ports
        //----------------------------------------------------------------------     
        .phy_rxeq_fsm                   (PHY_RXEQ_FSM[(3*i)+2:(3*i)]),
        .RXEQ_LFFS_SEL                  (rxeq_lffs_sel[i]),   
        .RXEQ_NEW_TXCOEFF               (rxeq_new_txcoeff[(18*i)+17:(18*i)]),    
        .RXEQ_ADAPT_DONE                (rxeq_adapt_done[i]),      
        .RXEQ_DONE                      (rxeq_done[i])      
    );

    //----------------------------------------------------------------------------------------------
    //  Receiver detect RX termination
    //----------------------------------------------------------------------------------------------    
    pcie4_uscale_plus_0_gt_receiver_detect_rxterm #
    ( 
      .CONSECUTIVE_CYCLE_OF_RXELECIDLE ((PHY_REFCLK_FREQ==0)?64:(PHY_REFCLK_FREQ==1)?80:160)
    )
    receiver_detect_termination_i
    (
      //---------- Input -------------------------------------
      .RXTERM_CLK                        (PHY_REFCLK), 
      .RXTERM_RST_N                      (rrst_n), 
      .RXTERM_RXELECIDLE                 (PHY_RXELECIDLE[i]), 
      .RXTERM_MAC_IN_DETECT              (PHY_PCIE_MAC_IN_DETECT), 
    
      //---------- Output ------------------------------------
      .RXTERM_RXTERMINATION              (rxterm_rxtermination[i]),
      .RXTERM_FSM                        () 
    );
    
    assign gt_rxtermination[i] = (PHY_MODE == 0) ? rxterm_rxtermination[i] : USB_RXTERMINATION[i];

    //--------------------------------------------------------------------------------------------------
    //  Reset CDR upon EIOS/EIDLE detection
    //--------------------------------------------------------------------------------------------------
    pcie4_uscale_plus_0_gt_cdr_ctrl_on_eidle #
    (
        .PHY_GEN12_CDR_CTRL_ON_EIDLE (PHY_GEN12_CDR_CTRL_ON_EIDLE),   
        .PHY_GEN34_CDR_CTRL_ON_EIDLE (PHY_GEN34_CDR_CTRL_ON_EIDLE), 
        .PHY_REFCLK_MODE             (PHY_REFCLK_MODE),
        .PHY_REFCLK_FREQ             (PHY_REFCLK_FREQ)
    )
    cdr_ctrl_on_eidle_i
    (
        //----------------------------------------------------------------------------
        //  Input Ports
        //----------------------------------------------------------------------------
        .CDRCTRL_PCLK                               (pclk2_gt),
        .CDRCTRL_PCLK_RST_N                         (rst_psrst_n_r[3]),
        .CDRCTRL_CLK                                (PHY_REFCLK),
        .CDRCTRL_RST_N                              (rst_idle),
        .CDRCTRL_RATE                               (PHY_RATE),
        .CDRCTRL_RXELECIDLE                         (gt_rxelecidle[i]),
        .CDRCTRL_GEN34_EIOS_DET                     (gt_gen34_eios_det[i]),
        .CDRCTRL_RXCDRHOLD_IN                       (PHY_RXCDRHOLD),
        .CDRCTRL_RXCDRFREQRESET_IN                  (1'b0),
        .CDRCTRL_RXRATEDONE                         (gt_rxratedone[i]),
        //----------------------------------------------------------------------------
        //  Output Ports
        //----------------------------------------------------------------------------  
        .CDRCTRL_RXCDRHOLD_OUT                      (cdrctrl_rxcdrhold[i]),
        .CDRCTRL_RXCDRFREQRESET_OUT                 (cdrctrl_rxcdrfreqreset[i]),
        .CDRCTRL_RESETOVRD_OUT                      (cdrctrl_resetovrd[i])
    );
      
    assign gt_rxcdrhold[i] = (PHY_GEN12_CDR_CTRL_ON_EIDLE == "TRUE") || (PHY_GEN34_CDR_CTRL_ON_EIDLE == "TRUE") ? cdrctrl_rxcdrhold[i] : PHY_RXCDRHOLD;
    
    always @ (posedge PHY_REFCLK) begin
      cdrhold_shift[i] <= {cdrhold_shift[i][30:0],gt_rxcdrhold[i]};
    end
    
    pcie4_uscale_plus_0_sync #(.WIDTH (1), .STAGE (3)) sync_cdrhold  (.CLK (pclk2_gt), .D (cdrhold_shift[i][31]), .Q (cdrhold_shift_sync[i]));
    
    assign rxvalid_new[i] = cdrhold_shift_sync[i]?1'b0:gt_rxvalid[i];
    
    assign PHY_RXVALID[i] = rxvalid_new[i]; 

    //----------------------------------------------------------------------------------------------
    //  Use Static GT Wrapper
    //----------------------------------------------------------------------------------------------
    if (PHY_GTWIZARD == "FALSE")
    
        begin : gt_wrapper
    
        //----------------------------------------------------------------------
        //  GT Channel
        //----------------------------------------------------------------------
        pcie4_uscale_plus_0_gt_gt_channel #
        (
            .PHY_SIM_EN                     (PHY_SIM_EN),   
            .PHY_GT_XCVR                    (PHY_GT_XCVR),
            .PHY_MODE                       (PHY_MODE),
            .PHY_REFCLK_MODE                (PHY_REFCLK_MODE),
            .PHY_LANE                       (PHY_LANE),    
            .PHY_MAX_SPEED                  (PHY_MAX_SPEED),
            .PHY_GEN4_64BIT_EN              (PHY_GEN4_64BIT_EN),
            .PHY_GEN12_CDR_CTRL_ON_EIDLE     (PHY_GEN12_CDR_CTRL_ON_EIDLE),
            .PHY_GEN34_CDR_CTRL_ON_EIDLE     (PHY_GEN34_CDR_CTRL_ON_EIDLE),
            .PHY_REFCLK_FREQ                (PHY_REFCLK_FREQ),    
            .PHY_CORECLK_FREQ               (PHY_CORECLK_FREQ),         
            .GT_LANE_NUM                    (i)                      
        )
        gt_channel_i
        (  
        
            //------------------------------------------------------------------
            //  Clock Ports
            //------------------------------------------------------------------
            .GT_GTREFCLK0                   (PHY_GTREFCLK),
            .GT_TXUSRCLK                    (pclk),
            .GT_RXUSRCLK                    (pclk), 
            .GT_TXUSRCLK2                   (pclk2_gt),
            .GT_RXUSRCLK2                   (pclk2_gt), 
            
            .GT_TXOUTCLK                    (gt_txoutclk[i]), 
            .GT_RXOUTCLK                    (DBG_RXOUTCLK[i]), 
            .GT_TXOUTCLKFABRIC              (DBG_TXOUTCLKFABRIC[i]),                                                        
            .GT_RXOUTCLKFABRIC              (DBG_RXOUTCLKFABRIC[i]),                                                        
            .GT_TXOUTCLKPCS                 (DBG_TXOUTCLKPCS[i]),                                                        
            .GT_RXOUTCLKPCS                 (DBG_RXOUTCLKPCS[i]),  
            .GT_RXRECCLKOUT                 (DBG_RXRECCLKOUT[i]),
            
	    .GT_TXOUTCLKSEL                 (PHY_TXOUTCLKSEL),

            //------------------------------------------------------------------
            //  BUFG_GT Controller Ports                                               
            //------------------------------------------------------------------ 
            .GT_BUFGTCE                     (gt_bufgtce[i]),     
            .GT_BUFGTCEMASK                 (gt_bufgtcemask[(3*i)+2:(3*i)]), 
            .GT_BUFGTRESET                  (gt_bufgtreset[i]),
            .GT_BUFGTRSTMASK                (gt_bufgtrstmask[(3*i)+2:(3*i)]),   
            .GT_BUFGTDIV                    (gt_bufgtdiv[(9*i)+8:(9*i)]),
            
            //------------------------------------------------------------------
            //  Reset Ports
            //------------------------------------------------------------------
            .GT_CPLLPD                      (rst_cpllpd),
            .GT_CPLLRESET                   (rst_cpllreset),
            .GT_TXPROGDIVRESET              (rst_txprogdivreset),
            .GT_GTTXRESET                   (rst_gtreset),
            .GT_GTRXRESET                   (rst_gtreset), 
            .GT_TXUSERRDY                   (rst_userrdy),
            .GT_RXUSERRDY                   (rst_userrdy),              
                             
            .GT_TXPMARESET                  (DBG_TXPMARESET[i]),                                            
            .GT_RXPMARESET                  (DBG_RXPMARESET[i]),                                            
            .GT_TXPCSRESET                  (DBG_TXPCSRESET[i]),   
            .GT_RXPCSRESET                  (DBG_RXPCSRESET[i]),  
            .GT_RXBUFRESET                  (DBG_RXBUFRESET[i]),
            .GT_RXCDRRESET                  (DBG_RXCDRRESET[i]),  
            .GT_RXDFELPMRESET               (DBG_RXDFELPMRESET[i]), 
            .GT_RXCDRFREQRESET              (cdrctrl_rxcdrfreqreset[i]),
            
            .GT_RESETOVRD                   (cdrctrl_resetovrd[i]),
                             
            .GT_GTPOWERGOOD                 (gt_gtpowergood[i]), 
            .GT_TXPROGDIVRESETDONE          (gt_txprogdivresetdone[i]),     
            .GT_TXPMARESETDONE              (DBG_TXPMARESETDONE[i]),     
            .GT_RXPMARESETDONE              (DBG_RXPMARESETDONE[i]),             
            .GT_TXRESETDONE                 (gt_txresetdone[i]),
            .GT_RXRESETDONE                 (gt_rxresetdone[i]),                

            //------------------------------------------------------------------
            //  QPLL Ports
            //------------------------------------------------------------------
            .GT_QPLL0CLK                    (gtcom_qpll0outclk[i>>2]),                       
            .GT_QPLL0REFCLK                 (gtcom_qpll0outrefclk[i>>2]), 
            .GT_QPLL0LOCK                   (qpll0lock_all),                    // From all lanes
            .GT_QPLL1CLK                    (gtcom_qpll1outclk[i>>2]),
            .GT_QPLL1REFCLK                 (gtcom_qpll1outrefclk[i>>2]), 
            .GT_QPLL1LOCK                   (qpll1lock_all),                    // From all lanes
            
            .GT_QPLLRATE                    (gt_qpllrate[(3*i)+2:(3*i)]),
            
            //------------------------------------------------------------------
            //  Serial Line Ports
            //------------------------------------------------------------------
            .GT_RXP                         (PHY_RXP[i]),
            .GT_RXN                         (PHY_RXN[i]),
            
            .GT_TXP                         (PHY_TXP[i]),
            .GT_TXN                         (PHY_TXN[i]),
            
            //------------------------------------------------------------------
            //  TX Data Ports
            //------------------------------------------------------------------
            .GT_TXDATA                      (PHY_TXDATA[(64*i)+63:(64*i)]),
            .GT_TXDATAK                     (PHY_TXDATAK[(2*i)+1:(2*i)]),
            .GT_TXDATA_VALID                (PHY_TXDATA_VALID[i]),
            .GT_TXSTART_BLOCK               (PHY_TXSTART_BLOCK[i]),
            .GT_TXSYNC_HEADER               (PHY_TXSYNC_HEADER[(2*i)+1:(2*i)]),
            
            //------------------------------------------------------------------
            //  RX Data Ports
            //------------------------------------------------------------------
            .GT_RXDATA                      (PHY_RXDATA[(64*i)+63:(64*i)]),
            .GT_RXDATAK                     (PHY_RXDATAK[(2*i)+1:(2*i)]),
            .GT_RXDATA_VALID                (PHY_RXDATA_VALID[i]),
            .GT_RXSTART_BLOCK               (PHY_RXSTART_BLOCK[(2*i)+1:(2*i)]),
            .GT_RXSYNC_HEADER               (PHY_RXSYNC_HEADER[(2*i)+1:(2*i)]),
            
            //------------------------------------------------------------------
            //  PHY Command Ports
            //------------------------------------------------------------------
            .GT_TXDETECTRX                  (PHY_TXDETECTRX),
            .GT_TXELECIDLE                  (PHY_TXELECIDLE[i]), 
            .GT_TXCOMPLIANCE                (PHY_TXCOMPLIANCE[i]),
            .GT_RXPOLARITY                  (PHY_RXPOLARITY[i]),
            .GT_POWERDOWN                   (PHY_POWERDOWN),
            .GT_RATE                        (PHY_RATE), 
            .GT_RXCDRHOLD                   (gt_rxcdrhold[i]),      
                
            //------------------------------------------------------------------
            //  PHY Status Ports
            //------------------------------------------------------------------
            .GT_RXVALID                     (PHY_RXVALID[i]),
            .GT_PHYSTATUS                   (gt_phystatus[i]),
            .GT_RXELECIDLE                  (gt_rxelecidle[i]),
            .GT_RXSTATUS                    (PHY_RXSTATUS[(3*i)+2:(3*i)]),
                
            //------------------------------------------------------------------
            //  TX Driver Ports
            //------------------------------------------------------------------
            .GT_TXMARGIN                    (PHY_TXMARGIN),
            .GT_TXSWING                     (PHY_TXSWING),
            .GT_TXDEEMPH                    (PHY_TXDEEMPH),  
            
            //------------------------------------------------------------------
            //  TX Equalization Ports (Gen3) 
            //------------------------------------------------------------------
            .GT_TXPRECURSOR                 (txeq_precursor[(5*i)+4:(5*i)]),
            .GT_TXMAINCURSOR                (txeq_maincursor[(7*i)+6:(7*i)]),
            .GT_TXPOSTCURSOR                (txeq_postcursor[(5*i)+4:(5*i)]),
            
            //------------------------------------------------------------------
            //  PCIe Ports (Advance feature)
            //------------------------------------------------------------------
            .GT_PCIERSTIDLE                 (rst_idle),        
            .GT_PCIERSTTXSYNCSTART          (rst_txsync_start), 
            .GT_PCIEEQRXEQADAPTDONE         (1'd0),                             // Not used in top level
            .GT_PCIEUSERRATEDONE            (DBG_RATE_DONE[i]),                 // For debug only
        
            .GT_PCIEUSERPHYSTATUSRST        (gt_pcieuserphystatusrst[i]),    
            .GT_PCIERATEQPLLPD              (gt_pcierateqpllpd[(2*i)+1:(2*i)]),     
            .GT_PCIERATEQPLLRESET           (gt_pcierateqpllreset[(2*i)+1:(2*i)]), 
            .GT_PCIERATEIDLE                (gt_pcierateidle[i]),            
            .GT_PCIESYNCTXSYNCDONE          (gt_pciesynctxsyncdone[i]),  
            .GT_PCIERATEGEN3                (gt_pcierategen3[i]),               // Not used in top level
            .GT_PCIEUSERGEN3RDY             (gt_pcieusergen3rdy[i]),            // Not used in top level
            .GT_PCIEUSERRATESTART           (gt_pcieuserratestart[i]),          // For debug
            
            //------------------------------------------------------------------
            //  USB Ports
            //------------------------------------------------------------------
            .GT_TXONESZEROS                 (USB_TXONESZEROS[i]),                        
            .GT_RXEQTRAINING                (USB_RXEQTRAINING[i]),                       
            .GT_RXTERMINATION               (gt_rxtermination[i]),                        
    
            .GT_POWERPRESENT                (USB_POWERPRESENT[i]),    
            
            //------------------------------------------------------------------
            //  TX Sync Alignment Ports
            //------------------------------------------------------------------
            .GT_TXSYNCALLIN                 (txsyncallin_all),                  // From all lanes
            .GT_TXSYNCIN                    (gt_txsyncout[0]),                  // From master lane 0        
        
            .GT_TXPHALIGNDONE               (gt_txphaligndone[i]),            
            .GT_TXSYNCOUT                   (gt_txsyncout[i]),
            
             //-----------------------------------------------------------------
             //  Loopback and PRBS Ports
             //-----------------------------------------------------------------  
            .GT_LOOPBACK                    (GT_LOOPBACK[(3*i)+2:(3*i)]),                                              
            .GT_PRBSSEL                     (DBG_PRBSSEL[(4*i)+3:(4*i)]),
            .GT_TXPRBSFORCEERR              (DBG_TXPRBSFORCEERR[i]), 
            .GT_RXPRBSCNTRESET              (DBG_RXPRBSCNTRESET[i]),                                                                                                      
        
            .GT_RXPRBSERR                   (DBG_RXPRBSERR[i]),                                              
            .GT_RXPRBSLOCKED                (DBG_RXPRBSLOCKED[i]),  
        
            //------------------------------------------------------------------
            //  GT Status Ports
            //------------------------------------------------------------------                                              
            .GT_MASTER_CPLLLOCK             (gt_cplllock[0]),                   // From master lane 0 
            
            .GT_CPLLLOCK                    (gt_cplllock[i]),  
            .GT_RXCDRLOCK                   (gt_rxcdrlock[i]),
            .GT_GEN34_EIOS_DET              (gt_gen34_eios_det[i]),
            .GT_RXRATEDONE                  (gt_rxratedone[i]),
            
            //------------------------------------------------------------------
            //  DRP Ports
            //------------------------------------------------------------------
            .GT_DRPCLK                      (PHY_REFCLK),
            .GT_DRPADDR                     (10'd0),
            .GT_DRPEN                       (1'b0),
            .GT_DRPWE                       (1'b0),
            .GT_DRPDI                       (16'd0),

            .GT_DRPRDY                      (),
            .GT_DRPDO                       ()            
        );
end // gt_channel            
        //------------------------------------------------------------------------------------------
        //  PHY Quad - Generate one Quad for every four Lanes
        //------------------------------------------------------------------------------------------
        if ((i%4)==0) 
                       
            begin : phy_quad   
                 
            //------------------------------------------------------------------
            //  Generate QPLL Powerdown and Reset
            //------------------------------------------------------------------
            //  * QPLL reset and powerdown for Quad 1 driven by       Master Lane 0
            //  * QPLL reset and powerdown for Quad 2 driven by Local Master Lane 4
            //------------------------------------------------------------------        
            assign qpll1pd[i>>2]    = (PHY_MAX_SPEED != 3) ? 1'd1 : (i > 3) ? (rst_qpllpd    || gt_pcierateqpllpd[(i*2)+1]) : 
                                                                              (rst_qpllpd    || gt_pcierateqpllpd[1]);
                                             
            assign qpll1reset[i>>2] = (PHY_MAX_SPEED != 3) ? 1'd1 : (i > 3) ? (rst_qpllreset || gt_pcierateqpllreset[(i*2)+1]) : 
                                                                              (rst_qpllreset || gt_pcierateqpllreset[1]);            
            
            assign qpll0pd[i>>2]    = (PHY_MAX_SPEED != 4) ? 1'd1 : (i > 3) ? (rst_qpllpd    || gt_pcierateqpllpd[(i*2)+0]) : 
                                                                              (rst_qpllpd    || gt_pcierateqpllpd[0]);
                                             
            assign qpll0reset[i>>2] = (PHY_MAX_SPEED != 4) ? 1'd1 : (i > 3) ? (rst_qpllreset || gt_pcierateqpllreset[(i*2)+0]) : 
                                                                              (rst_qpllreset || gt_pcierateqpllreset[0]);                                 
        
    if (PHY_GTWIZARD == "FALSE") begin : gt_common_int
            //------------------------------------------------------------------
            //  GT Common Module                                                   
            //------------------------------------------------------------------
            pcie4_uscale_plus_0_gt_gt_common #
            (
                //--------------------------------------------------------------
                //  User Attributes
                //--------------------------------------------------------------
                .PHY_SIM_EN                 (PHY_SIM_EN),   
                .PHY_GT_XCVR                (PHY_GT_XCVR),
                .PHY_MAX_SPEED              (PHY_MAX_SPEED),
                .PHY_REFCLK_FREQ            (PHY_REFCLK_FREQ)          
            )
            gt_common_i
            (    
                //--------------------------------------------------------------
                //  Clock Ports
                //--------------------------------------------------------------
                .GTCOM_REFCLK               (PHY_GTREFCLK),
                
                .GTCOM_QPLL0LOCK            (gtcom_qpll0lock[i>>2]),
                .GTCOM_QPLL0OUTCLK          (gtcom_qpll0outclk[i>>2]),
                .GTCOM_QPLL0OUTREFCLK       (gtcom_qpll0outrefclk[i>>2]),
                
                .GTCOM_QPLL1LOCK            (gtcom_qpll1lock[i>>2]),
                .GTCOM_QPLL1OUTCLK          (gtcom_qpll1outclk[i>>2]),
                .GTCOM_QPLL1OUTREFCLK       (gtcom_qpll1outrefclk[i>>2]),
                
                //--------------------------------------------------------------
                //  Reset Ports
                //--------------------------------------------------------------             
                .GTCOM_QPLL0PD              (qpll0pd[i>>2]),         
                .GTCOM_QPLL0RESET           (qpll0reset[i>>2]),
                
                .GTCOM_QPLL1PD              (qpll1pd[i>>2]),         
                .GTCOM_QPLL1RESET           (qpll1reset[i>>2]),
                
                //--------------------------------------------------------------
                //  PCIe Ports
                //--------------------------------------------------------------    
                .GTCOM_QPLLRATE             ({1'd0, PHY_RATE}),               
                
                //--------------------------------------------------------------
                //  DRP Ports
                //--------------------------------------------------------------
                .GTCOM_DRPCLK               (PHY_REFCLK),                                     
                .GTCOM_DRPADDR              (GTCOM_DRPADDR[(16*(i>>2))+15:(16*(i>>2))]),                        
                .GTCOM_DRPEN                (GTCOM_DRPEN[i>>2]),                             
                .GTCOM_DRPWE                (GTCOM_DRPWE[i>>2]),
                .GTCOM_DRPDI                (GTCOM_DRPDI[(16*(i>>2))+15:(16*(i>>2))]),                     
                                                                             
                .GTCOM_DRPRDY               (GTCOM_DRPRDY[i>>2]),
                .GTCOM_DRPDO                (GTCOM_DRPDO[(16*(i>>2))+15:(16*(i>>2))])
            );
           end // gt_common_int

            end // phy_quad 
            
        end // phy_lane
       
endgenerate 
//--------------------------------------------------------------------------------------------------
//  Generate - End
//--------------------------------------------------------------------------------------------------
generate
    if (PHY_GTWIZARD == "TRUE") begin :gt_wizard

pcie4_uscale_plus_0_gtwizard_top #
        (
            .PHY_LANE                       (PHY_LANE),                    
            .PHY_MAX_SPEED                  (PHY_MAX_SPEED),
            .PHY_GT_XCVR                    (PHY_GT_XCVR)
        )
        gtwizard_top_i
        (  

 
            //------------------------------------------------------------------
            //  Clock Ports *
            //------------------------------------------------------------------
            .GT_GTREFCLK0                   (PHY_GTREFCLK),                     
            .GT_TXUSRCLK                    ({PHY_LANE{pclk}}),
            .GT_RXUSRCLK                    ({PHY_LANE{pclk}}), 
            .GT_TXUSRCLK2                   ({PHY_LANE{pclk2_gt}}),
            .GT_RXUSRCLK2                   ({PHY_LANE{pclk2_gt}}), 
            
            .GT_RXOUTCLK                    (DBG_RXOUTCLK), 
            .GT_TXOUTCLKFABRIC              (DBG_TXOUTCLKFABRIC),                                                        
            .GT_RXOUTCLKFABRIC              (DBG_RXOUTCLKFABRIC),                                                        
            .GT_TXOUTCLKPCS                 (DBG_TXOUTCLKPCS),                                                        
            .GT_RXOUTCLKPCS                 (DBG_RXOUTCLKPCS),  
            .GT_RXRECCLKOUT                 (DBG_RXRECCLKOUT),
            .GT_TXOUTCLKSEL                 ({PHY_LANE{PHY_TXOUTCLKSEL}}),
            //------------------------------------------------------------------
            //  BUFG_GT Controller Ports *                                               
            //------------------------------------------------------------------ 
            .GT_BUFGTCE                     (gt_bufgtce),     
            .GT_BUFGTCEMASK                 (gt_bufgtcemask), 
            .GT_BUFGTRESET                  (gt_bufgtreset),
            .GT_BUFGTRSTMASK                (gt_bufgtrstmask),   
            .GT_BUFGTDIV                    (gt_bufgtdiv),
            .GT_TXOUTCLK                    (gt_txoutclk),   
            
            //------------------------------------------------------------------  
            //  Reset Ports *                                                      
            //------------------------------------------------------------------  
            .GT_CPLLPD                      ({PHY_LANE{rst_cpllpd}}),              
            .GT_CPLLRESET                   ({PHY_LANE{rst_cpllreset}}),           
            .GT_TXPROGDIVRESET              ({PHY_LANE{rst_txprogdivreset}}),        
            .GT_RXPROGDIVRESET              ({PHY_LANE{rst_txprogdivreset}}),        
            .GT_GTTXRESET                   ({PHY_LANE{rst_gtreset}}),             
            .GT_GTRXRESET                   ({PHY_LANE{rst_gtreset}}),             
            .GT_TXUSERRDY                   ({PHY_LANE{rst_userrdy}}),             
            .GT_RXUSERRDY                   ({PHY_LANE{rst_userrdy}}),             
                                                                                  
            .GT_TXPMARESET                  (DBG_TXPMARESET),                                            
            .GT_RXPMARESET                  (DBG_RXPMARESET),                                            
            .GT_TXPCSRESET                  (DBG_TXPCSRESET),   
            .GT_RXPCSRESET                  (DBG_RXPCSRESET),  
            .GT_RXBUFRESET                  (DBG_RXBUFRESET),
            .GT_RXCDRRESET                  (DBG_RXCDRRESET),  
            .GT_RXDFELPMRESET               (DBG_RXDFELPMRESET),                                

            .GT_GTPOWERGOOD                 (gt_gtpowergood),                     
            .GT_TXPROGDIVRESETDONE          (gt_txprogdivresetdone),              
            .GT_TXRESETDONE                 (gt_txresetdone),                     
            .GT_RXRESETDONE                 (gt_rxresetdone),                     
            .GT_TXPMARESETDONE              (DBG_TXPMARESETDONE),     
            .GT_RXPMARESETDONE              (DBG_RXPMARESETDONE),             
            
            //--------------------------------------------------------------
            //  Common QPLL Ports *
            //--------------------------------------------------------------
            .GTCOM_QPLLPD                   (rst_qpllpd),         
            .GTCOM_QPLLRESET                (rst_qpllreset), 
            
            .GTCOM_QPLL1LOCK                (gtcom_qpll1lock),
            .GTCOM_QPLL0LOCK                (gtcom_qpll0lock),

            .GTCOM_QPLL0OUTCLK              (gtcom_qpll0outclk),
            .GTCOM_QPLL0OUTREFCLK           (gtcom_qpll0outrefclk),
            .GTCOM_QPLL1OUTCLK              (gtcom_qpll1outclk),
            .GTCOM_QPLL1OUTREFCLK           (gtcom_qpll1outrefclk),
            //--------------------------------------------------------------
            //  GT Common DRP Ports *
            //--------------------------------------------------------------
            .GTCOM_DRPCLK                   (PHY_REFCLK),                                     
            .GTCOM_DRPADDR                  (GTCOM_DRPADDR),                        
            .GTCOM_DRPEN                    (GTCOM_DRPEN),                             
            .GTCOM_DRPWE                    (GTCOM_DRPWE),
            .GTCOM_DRPDI                    (GTCOM_DRPDI),                     
                                                                             
            .GTCOM_DRPRDY                   (GTCOM_DRPRDY),
            .GTCOM_DRPDO                    (GTCOM_DRPDO),
            //--------------------------------------------------------------
            //  GT Channel DRP Ports *
            //--------------------------------------------------------------
            .GT_DRPCLK                      ({PHY_LANE{PHY_REFCLK}}),
            .GT_DRPADDR                     (GT_DRPADDR),
            .GT_DRPEN                       (GT_DRPEN),
            .GT_DRPWE                       (GT_DRPWE),
            .GT_DRPDI                       (GT_DRPDI),

            .GT_DRPRDY                      (GT_DRPRDY),
            .GT_DRPDO                       (GT_DRPDO),     
            //--------------------------------------------------------------
            //  IBERT ports 
            //--------------------------------------------------------------
            .GT_TXPRECURSOR                 ( ibert_txprecursor_in ),  //(txeq_precursor),
            .GT_TXPOSTCURSOR                ( ibert_txpostcursor_in ), //(txeq_postcursor),
            .GT_RATE                        ( {PHY_LANE{PHY_RATE}} ),
            .GT_EYESCANRESET                ( ibert_eyescanreset_in ),
            .GT_TXDIFFCTRL                  ( ibert_txdiffctrl_in ),
            .GT_RXLPMEN                     ( ibert_rxlpmen_in ),
            
            .GT_PCIERATEGEN3                (gt_pcierategen3),    
       
            //------------------------------------------------------------------
            //  Serial Line Ports *
            //------------------------------------------------------------------
            .GT_RXP                         (PHY_RXP),
            .GT_RXN                         (PHY_RXN),
            
            .GT_TXP                         (PHY_TXP),
            .GT_TXN                         (PHY_TXN),
            
            //------------------------------------------------------------------
            //  TX Data Ports *
            //------------------------------------------------------------------
            .GT_TXDATA                      (PHY_TXDATA),
            .GT_TXDATAK                     (PHY_TXDATAK),
            .GT_TXDATA_VALID                (PHY_TXDATA_VALID),
            .GT_TXSTART_BLOCK               (PHY_TXSTART_BLOCK),
            .GT_TXSYNC_HEADER               (PHY_TXSYNC_HEADER),
            
            //------------------------------------------------------------------
            //  RX Data Ports *
            //------------------------------------------------------------------
            .GT_RXDATA                      (PHY_RXDATA),
            .GT_RXDATAK                     (PHY_RXDATAK),
            .GT_RXDATA_VALID                (PHY_RXDATA_VALID),
            .GT_RXSTART_BLOCK               (PHY_RXSTART_BLOCK),
            .GT_RXSYNC_HEADER               (PHY_RXSYNC_HEADER),
            
            //------------------------------------------------------------------
            //  PHY Command Ports *
            //------------------------------------------------------------------
            .GT_TXDETECTRX                  ({PHY_LANE{PHY_TXDETECTRX}}),
            .GT_TXELECIDLE                  (PHY_TXELECIDLE), 
            .GT_TXCOMPLIANCE                (PHY_TXCOMPLIANCE),
            .GT_RXPOLARITY                  (PHY_RXPOLARITY),
            .GT_POWERDOWN                   ({PHY_LANE{PHY_POWERDOWN}}),
            .GT_RXCDRHOLD                   (gt_rxcdrhold),      
                
            //------------------------------------------------------------------
            //  PHY Status Ports *
            //------------------------------------------------------------------
            .GT_RXVALID                     (gt_rxvalid),//(PHY_RXVALID),
            .GT_PHYSTATUS                   (gt_phystatus),
            .GT_RXELECIDLE                  (gt_rxelecidle),
            .GT_RXSTATUS                    (PHY_RXSTATUS),
                
            //------------------------------------------------------------------
            //  TX Driver Ports *
            //------------------------------------------------------------------
            .GT_TXMARGIN                    ({PHY_LANE{PHY_TXMARGIN}}),
            .GT_TXSWING                     ({PHY_LANE{PHY_TXSWING}}),
            .GT_TXDEEMPH                    ({PHY_LANE{PHY_TXDEEMPH}}),  
            
            //------------------------------------------------------------------
            //  TX Equalization Ports (Gen3) *
            //------------------------------------------------------------------
            .GT_TXMAINCURSOR                (txeq_maincursor),
            
            //------------------------------------------------------------------
            //  PCIe PCS (Advance Feature) *
            //------------------------------------------------------------------
            .GT_PCIERSTIDLE                 ({PHY_LANE{rst_idle}}),        
            .GT_PCIERSTTXSYNCSTART          ({PHY_LANE{rst_txsync_start}}), 
            .GT_PCIEEQRXEQADAPTDONE         ({PHY_LANE{1'd0}}),                 // Not used
            .GT_PCIEUSERRATEDONE            (DBG_RATE_DONE),                 // For debug only
        
            .GT_PCIEUSERPHYSTATUSRST        (gt_pcieuserphystatusrst),    
            .GT_PCIERATEQPLLPD              (gt_pcierateqpllpd),     
            .GT_PCIERATEQPLLRESET           (gt_pcierateqpllreset), 
            .GT_PCIERATEIDLE                (gt_pcierateidle),            
            .GT_PCIESYNCTXSYNCDONE          (gt_pciesynctxsyncdone),  
            .GT_PCIEUSERGEN3RDY             (gt_pcieusergen3rdy),  
            .GT_PCIEUSERRATESTART           (gt_pcieuserratestart), 
            
            .GT_TXPHALIGNDONE               (gt_txphaligndone),            
            .GT_RXPHALIGNDONE               (GT_RXPHALIGNDONE),            
             //-----------------------------------------------------------------
             //  Loopback and PRBS Ports *
             //-----------------------------------------------------------------  
            .GT_LOOPBACK                    (GT_LOOPBACK),                                        
            .GT_PRBSSEL                     (DBG_PRBSSEL),
            .GT_TXPRBSFORCEERR              (DBG_TXPRBSFORCEERR), 
            .GT_TXINHIBIT                   (GT_TXINHIBIT),
            .GT_RXPRBSCNTRESET              (DBG_RXPRBSCNTRESET),                                                                                                      
            
            .GT_RXPRBSERR                   (DBG_RXPRBSERR),                                              
            .GT_RXPRBSLOCKED                (DBG_RXPRBSLOCKED),  
        
            .GT_RXDLYSRESETDONE             (GT_RXDLYSRESETDONE ),    
            .GT_TXDLYSRESETDONE             (GT_TXDLYSRESETDONE ),    
            .GT_EYESCANDATAERROR            (GT_EYESCANDATAERROR ),
            .GT_RXSYNCDONE                  (GT_RXSYNCDONE ),
            .GT_TXPHINITDONE                (GT_TXPHINITDONE),
            .GT_RXCOMMADET                  (GT_RXCOMMADET),
            .GT_RXBUFSTATUS                 (GT_RXBUFSTATUS),
            //------------------------------------------------------------------
            //  GT Status Ports *
            //------------------------------------------------------------------                                                   
            .GT_CPLLLOCK                    (gt_cplllock),  
            .GT_RXCDRLOCK                   (gt_rxcdrlock),

            .GT_GEN34_EIOS_DET              (gt_gen34_eios_det),
            .GT_RXRATEDONE                  (gt_rxratedone),

            .GT_DMONITOROUT                 (GT_DMONITOROUT ),
            .GT_DMONFIFORESET               (GT_DMONFIFORESET),
            .GT_DMONITORCLK                 (GT_DMONITORCLK),
            //------------------------------------------------------------------
            //  GT RX Termination
            //------------------------------------------------------------------   
            .GT_RXTERMINATION               (gt_rxtermination),
            //------------------------------------------------------------------
            //  GT RX RATEMODE
            //------------------------------------------------------------------             
            .GT_RXRATEMODE                  ({PHY_LANE{1'd0}})
        );
    end
endgenerate 

//--------------------------------------------------------------------------------------------------
//  Convert per-lane signals to per-design 
//--------------------------------------------------------------------------------------------------
    assign qpll0lock_all   = &gtcom_qpll0lock;
    assign qpll1lock_all   = &gtcom_qpll1lock;
    assign txsyncallin_all = &gt_txphaligndone;

//------------------------------------------------------------------------------
//  PHYSTATUS Reset Synchronizer for PCLK 
//------------------------------------------------------------------------------

always @ (posedge pclk or negedge rst_idle)
  begin
    if (!rst_idle)
      rst_psrst_n_r <= 4'd0;
    else
      rst_psrst_n_r <= {rst_psrst_n_r[2:0], 1'd1};
  end

//--------------------------------------------------------------------------------------------------
//  PHY Wrapper Outputs
//--------------------------------------------------------------------------------------------------
assign PHY_PCLK               = pclk;
assign PHY_PHYSTATUS          = gt_phystatus;
assign PHY_PHYSTATUS_RST      = !rst_psrst_n_r[3];
assign PHY_RXELECIDLE         = gt_rxelecidle;

//------------------------------------------------------------------------------
//  TX Equalization Outputs (Gen3/Gen4) 
//------------------------------------------------------------------------------
assign PHY_TXEQ_FS            = 6'd40;                                          // Value based on GT TX driver characteristic                                    
assign PHY_TXEQ_LF            = 6'd12;                                          // Value based on GT TX driver characteristic
assign PHY_TXEQ_NEW_COEFF     = txeq_new_coeff;        
assign PHY_TXEQ_DONE          = txeq_done;                                                   
      
//------------------------------------------------------------------------------
//  RX Equalization Outputs (Gen3/Gen4)
//------------------------------------------------------------------------------     
assign PHY_RXEQ_LFFS_SEL      = rxeq_lffs_sel;                                                  
assign PHY_RXEQ_NEW_TXCOEFF   = rxeq_new_txcoeff;     
assign PHY_RXEQ_ADAPT_DONE    = rxeq_adapt_done;   
assign PHY_RXEQ_DONE          = rxeq_done;   

//------------------------------------------------------------------------------
//  Debug Outputs 
//------------------------------------------------------------------------------ 
assign DBG_RATE_START         = gt_pcieuserratestart;
assign DBG_RST_IDLE           = rst_idle;
assign DBG_RATE_IDLE          = gt_pcierateidle;
assign DBG_RXCDRLOCK          = gt_rxcdrlock;     
assign DBG_TXOUTCLK           = gt_txoutclk;     
assign DBG_RRST_N             = rrst_n;
assign DBG_PRST_N             = prst_n;
assign DBG_GTPOWERGOOD        = gt_gtpowergood;
assign DBG_CPLLLOCK           = gt_cplllock;
assign DBG_QPLL0LOCK          = gtcom_qpll0lock;
assign DBG_QPLL1LOCK          = gtcom_qpll1lock;
assign DBG_TXPROGDIVRESETDONE = gt_txprogdivresetdone;
assign DBG_TXRESETDONE        = gt_txresetdone;
assign DBG_RXRESETDONE        = gt_rxresetdone;
assign DBG_TXSYNCDONE         = gt_pciesynctxsyncdone;
assign DBG_GEN34_EIOS_DET     = gt_gen34_eios_det;
assign GT_TXPHALIGNDONE       = gt_txphaligndone;          
assign GT_BUFGTDIV            = gt_bufgtdiv;
assign GT_DRPCLK              = PHY_REFCLK;                                           
           

endmodule

