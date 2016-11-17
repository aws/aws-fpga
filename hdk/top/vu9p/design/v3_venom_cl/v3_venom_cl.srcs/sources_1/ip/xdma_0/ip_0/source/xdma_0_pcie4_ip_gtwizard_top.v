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
// File       : xdma_0_pcie4_ip_gtwizard_top.v
// Version    : 1.1 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
//  Design :  PCIe PHY Wrapper 
//  Module :  GT Wizard Top 
//--------------------------------------------------------------------------------------------------

`timescale 1ps / 1ps

//--------------------------------------------------------------------------------------------------
//  GT Wizard Top Module
//--------------------------------------------------------------------------------------------------
(* DowngradeIPIdentifiedWarnings = "yes" *)
module xdma_0_pcie4_ip_gtwizard_top #
(
    parameter         PHY_GT_XCVR = "GTY",
    parameter integer PHY_MAX_SPEED = 3,
    parameter integer PHY_LANE = 1
)
(    
                                                                                                      
    //--------------------------------------------------------------------------
    //  Clock Ports
    //--------------------------------------------------------------------------
    input                               GT_GTREFCLK0,
    input       [PHY_LANE-1:0]          GT_TXUSRCLK,
    input       [PHY_LANE-1:0]          GT_RXUSRCLK,  
    input       [PHY_LANE-1:0]          GT_TXUSRCLK2, 
    input       [PHY_LANE-1:0]          GT_RXUSRCLK2,    
    //--------------------------------------------------------------------------   
    //  IBERT ports 
    //--------------------------------------------------------------------------                   
    input       [PHY_LANE-1:0]          GT_EYESCANRESET,
    input       [(PHY_LANE* 2)-1:0]     GT_RATE,  
    input       [(PHY_LANE* 5)-1:0]     GT_TXDIFFCTRL,
    input       [(PHY_LANE* 5)-1:0]     GT_TXPRECURSOR,  
    input       [(PHY_LANE* 5)-1:0]     GT_TXPOSTCURSOR,      
    input       [PHY_LANE-1:0]          GT_RXLPMEN,

    output      [PHY_LANE-1:0]          GT_PCIERATEGEN3,   
    //--------------------------------------------------------------------------                   
    output      [PHY_LANE-1:0]          GT_RXOUTCLK,        
    output      [PHY_LANE-1:0]          GT_TXOUTCLKFABRIC,
    output      [PHY_LANE-1:0]          GT_RXOUTCLKFABRIC,
    output      [PHY_LANE-1:0]          GT_TXOUTCLKPCS,
    output      [PHY_LANE-1:0]          GT_RXOUTCLKPCS,
    output      [PHY_LANE-1:0]          GT_RXRECCLKOUT,
    //--------------------------------------------------------------------------   
    //  BUFG_GT Controller Ports                                                                        
    //--------------------------------------------------------------------------                   
    output      [PHY_LANE-1:0]          GT_BUFGTCE,       
    output      [(PHY_LANE* 3)-1:0]     GT_BUFGTCEMASK, 
    output      [PHY_LANE-1:0]          GT_BUFGTRESET,
    output      [(PHY_LANE* 3)-1:0]     GT_BUFGTRSTMASK,
    output      [(PHY_LANE* 9)-1:0]     GT_BUFGTDIV,   
    output      [PHY_LANE-1:0]          GT_TXOUTCLK,  
                
    //--------------------------------------------------------------------------
    //  Reset Ports
    //--------------------------------------------------------------------------
    input       [PHY_LANE-1:0]          GT_CPLLPD,    
    input       [PHY_LANE-1:0]          GT_CPLLRESET,

    input       [PHY_LANE-1:0]          GT_TXPROGDIVRESET,  
    input       [PHY_LANE-1:0]          GT_RXPROGDIVRESET,   
    input       [PHY_LANE-1:0]          GT_GTTXRESET,  
    input       [PHY_LANE-1:0]          GT_GTRXRESET,  
    input       [PHY_LANE-1:0]          GT_TXUSERRDY, 
    input       [PHY_LANE-1:0]          GT_RXUSERRDY, 
                                        
    input       [PHY_LANE-1:0]          GT_TXPMARESET,
    input       [PHY_LANE-1:0]          GT_RXPMARESET,
    input       [PHY_LANE-1:0]          GT_TXPCSRESET,
    input       [PHY_LANE-1:0]          GT_RXPCSRESET,
    input       [PHY_LANE-1:0]          GT_RXBUFRESET,
    input       [PHY_LANE-1:0]          GT_RXCDRRESET,
    input       [PHY_LANE-1:0]          GT_RXDFELPMRESET,

    output      [PHY_LANE-1:0]          GT_GTPOWERGOOD, 
    output      [PHY_LANE-1:0]          GT_TXPROGDIVRESETDONE,  
    output      [PHY_LANE-1:0]          GT_TXRESETDONE,   
    output      [PHY_LANE-1:0]          GT_RXRESETDONE,                  
    output      [PHY_LANE-1:0]          GT_TXPMARESETDONE,   
    output      [PHY_LANE-1:0]          GT_RXPMARESETDONE,               
    
    output      [PHY_LANE-1:0]          GT_TXPHALIGNDONE,            
    output      [PHY_LANE-1:0]          GT_TXPHINITDONE,
    output      [PHY_LANE-1:0]          GT_RXCOMMADET,


    //--------------------------------------------------------------------------
    //  Common QPLL Ports
    //--------------------------------------------------------------------------
    input                               GTCOM_QPLLPD,     
    input                               GTCOM_QPLLRESET,

    output      [(PHY_LANE-1)>>2:0]     GTCOM_QPLL0LOCK, 
    output      [(PHY_LANE-1)>>2:0]     GTCOM_QPLL0OUTCLK,
    output      [(PHY_LANE-1)>>2:0]     GTCOM_QPLL0OUTREFCLK, 
    output      [(PHY_LANE-1)>>2:0]     GTCOM_QPLL1LOCK, 
    output      [(PHY_LANE-1)>>2:0]     GTCOM_QPLL1OUTCLK,
    output      [(PHY_LANE-1)>>2:0]     GTCOM_QPLL1OUTREFCLK, 
    
 

    //----------------------------------------------------------------------------------------------
    //  Common DRP Ports
    //----------------------------------------------------------------------------------------------
    input                                           GTCOM_DRPCLK,
    input       [((((PHY_LANE-1)>>2)+1)*16)-1:0]    GTCOM_DRPADDR,                                       
    input       [   (PHY_LANE-1)>>2          :0]    GTCOM_DRPEN,                                             
    input       [   (PHY_LANE-1)>>2          :0]    GTCOM_DRPWE,     
    input       [((((PHY_LANE-1)>>2)+1)*16)-1:0]    GTCOM_DRPDI,                                      
                                                                         
    output      [   (PHY_LANE-1)>>2          :0]    GTCOM_DRPRDY,    
    output      [((((PHY_LANE-1)>>2)+1)*16)-1:0]    GTCOM_DRPDO,         
    
   input       [((PHY_LANE *  1)-1):0]    GT_DRPCLK,   
   input       [((PHY_LANE * 10)-1):0]    GT_DRPADDR, 
   input       [((PHY_LANE *  1)-1):0]    GT_DRPEN,    
   input       [((PHY_LANE *  1)-1):0]    GT_DRPWE,    
   input       [((PHY_LANE * 16)-1):0]    GT_DRPDI,   
                                           
   output      [((PHY_LANE *  1)-1):0]    GT_DRPRDY,   
   output      [((PHY_LANE * 16)-1):0]    GT_DRPDO,     

    //--------------------------------------------------------------------------
    //  Serial Line Ports
    //--------------------------------------------------------------------------
    input       [PHY_LANE-1:0]          GT_RXN,  
    input       [PHY_LANE-1:0]          GT_RXP,  
    
    output      [PHY_LANE-1:0]          GT_TXP,  
    output      [PHY_LANE-1:0]          GT_TXN,  
    
    //--------------------------------------------------------------------------
    //  TX Data Ports 
    //--------------------------------------------------------------------------
    input       [(PHY_LANE*64)-1:0]     GT_TXDATA,    
    input       [(PHY_LANE* 2)-1:0]     GT_TXDATAK,  
    input       [PHY_LANE-1:0]          GT_TXDATA_VALID,  
    input       [PHY_LANE-1:0]          GT_TXSTART_BLOCK,      
    input       [(PHY_LANE* 2)-1:0]     GT_TXSYNC_HEADER,  
    
    //--------------------------------------------------------------------------
    //  RX Data Ports 
    //--------------------------------------------------------------------------
    output      [(PHY_LANE*64)-1:0]     GT_RXDATA,      
    output      [(PHY_LANE* 2)-1:0]     GT_RXDATAK,        
    output      [PHY_LANE-1:0]          GT_RXDATA_VALID,  
    output      [(PHY_LANE* 2)-1:0]     GT_RXSTART_BLOCK,       
    output      [(PHY_LANE* 2)-1:0]     GT_RXSYNC_HEADER,     
    
    //--------------------------------------------------------------------------
    //  PHY Command Ports
    //--------------------------------------------------------------------------
    input       [PHY_LANE-1:0]          GT_TXDETECTRX,      
    input       [PHY_LANE-1:0]          GT_TXELECIDLE, 
    input       [PHY_LANE-1:0]          GT_TXCOMPLIANCE, 
    input       [PHY_LANE-1:0]          GT_RXPOLARITY,
    input       [(PHY_LANE* 2)-1:0]     GT_POWERDOWN,      
      
    //--------------------------------------------------------------------------
    //  PHY Status Ports
    //--------------------------------------------------------------------------
    output      [PHY_LANE-1:0]          GT_RXVALID, 
    output      [PHY_LANE-1:0]          GT_PHYSTATUS,
    output      [PHY_LANE-1:0]          GT_RXELECIDLE,
    output      [(PHY_LANE* 3)-1:0]     GT_RXSTATUS,
      
    //--------------------------------------------------------------------------
    //  TX Equalization Ports 
    //--------------------------------------------------------------------------
    input       [(PHY_LANE* 3)-1:0]     GT_TXMARGIN,  
    input       [(PHY_LANE* 3)-1:0]     GT_TXOUTCLKSEL, 
    input       [PHY_LANE-1:0]          GT_TXSWING,  
    input       [(PHY_LANE* 2)-1:0]     GT_TXDEEMPH, 
    input       [PHY_LANE-1:0]          GT_RXCDRHOLD, 
    
    //--------------------------------------------------------------------------
    //  TX Equalization Ports (Gen3)
    //--------------------------------------------------------------------------
    input       [(PHY_LANE* 7)-1:0]     GT_TXMAINCURSOR,  
    
    //--------------------------------------------------------------------------
    //  PCIe PCS Ports
    //--------------------------------------------------------------------------
    input       [PHY_LANE-1:0]          GT_PCIERSTIDLE,        
    input       [PHY_LANE-1:0]          GT_PCIERSTTXSYNCSTART,  
    input       [PHY_LANE-1:0]          GT_PCIEEQRXEQADAPTDONE, 
    input       [PHY_LANE-1:0]          GT_PCIEUSERRATEDONE,    
             
    output      [PHY_LANE-1:0]          GT_PCIEUSERPHYSTATUSRST,  
    output      [(PHY_LANE* 2)-1:0]     GT_PCIERATEQPLLPD,              
    output      [(PHY_LANE* 2)-1:0]     GT_PCIERATEQPLLRESET,                
    output      [PHY_LANE-1:0]          GT_PCIERATEIDLE,          
    output      [PHY_LANE-1:0]          GT_PCIESYNCTXSYNCDONE,                      
    output      [PHY_LANE-1:0]          GT_PCIEUSERGEN3RDY, 
    output      [PHY_LANE-1:0]          GT_PCIEUSERRATESTART,  
   
    //--------------------------------------------------------------------------
    //  Loopback & PRBS Ports
    //--------------------------------------------------------------------------     
    input       [(PHY_LANE* 3)-1:0]     GT_LOOPBACK,                                                 
    input       [(PHY_LANE* 4)-1:0]     GT_PRBSSEL,  
    input       [PHY_LANE-1:0]          GT_TXPRBSFORCEERR,     
    input       [PHY_LANE-1:0]          GT_TXINHIBIT,     
    input       [PHY_LANE-1:0]          GT_RXPRBSCNTRESET,                                                                                                       

    output      [PHY_LANE-1:0]          GT_RXPRBSERR,                                              
    output      [PHY_LANE-1:0]          GT_RXPRBSLOCKED,  
      
    output      [PHY_LANE-1:0]          GT_RXPHALIGNDONE,  
    output      [PHY_LANE-1:0]          GT_RXDLYSRESETDONE,     
    output      [PHY_LANE-1:0]          GT_TXDLYSRESETDONE,     
    output      [PHY_LANE-1:0]          GT_RXSYNCDONE, 
    output      [PHY_LANE-1:0]          GT_EYESCANDATAERROR,
    output      [(PHY_LANE*16)-1:0]     GT_DMONITOROUT,
    input       [PHY_LANE-1:0]          GT_DMONITORCLK,
    input       [PHY_LANE-1:0]          GT_DMONFIFORESET,
    output      [(PHY_LANE*3)-1:0]      GT_RXBUFSTATUS,
    //--------------------------------------------------------------------------
    //  GT Status Ports
    //--------------------------------------------------------------------------                                                     
    output      [PHY_LANE-1:0]          GT_CPLLLOCK,       
    output      [PHY_LANE-1:0]          GT_RXCDRLOCK,                                                                 
    output      [PHY_LANE-1:0]          GT_RXRATEDONE,  
    output      [PHY_LANE-1:0]          GT_GEN34_EIOS_DET,                                                                 
    
   //--------------------------------------------------------------------------
   //  GT RX RATEMODE
   //--------------------------------------------------------------------------
   input        [PHY_LANE-1:0]          GT_RXRATEMODE, 
   //--------------------------------------------------------------------------
   //  GT RX Termination 
   //--------------------------------------------------------------------------   
   input        [PHY_LANE-1:0]          GT_RXTERMINATION
);

  wire                qpll0lock_all;    
  wire                qpll1lock_all;    
  wire                txsyncallin_all;

    wire [(PHY_LANE-1)>>2:0] gtrefclk01_in;
    wire [(PHY_LANE-1)>>2:0] gtrefclk00_in;
    wire [((((PHY_LANE-1)>>2)+1)*3)-1:0] pcierateqpll0_in;
    wire [((((PHY_LANE-1)>>2)+1)*3)-1:0] pcierateqpll1_in;
    wire [(PHY_LANE-1)>>2:0]     qpll0lock_out;
    wire [(PHY_LANE-1)>>2:0]     qpll0outclk_out;
    wire [(PHY_LANE-1)>>2:0]     qpll0outrefclk_out;
    wire [(PHY_LANE-1)>>2:0]     qpll1lock_out;
    wire [(PHY_LANE-1)>>2:0]     qpll1outclk_out;
    wire [(PHY_LANE-1)>>2:0]     qpll1outrefclk_out;

    wire [PHY_LANE-1:0] bufgtce_out ;
    wire [(PHY_LANE* 3)-1:0] bufgtcemask_out ;
    wire [(PHY_LANE* 9)-1:0] bufgtdiv_out ;
    wire [PHY_LANE-1:0] bufgtreset_out ;
    wire [(PHY_LANE* 3)-1:0] bufgtrstmask_out ;
    wire [PHY_LANE-1:0] cpllfreqlock_in;
    wire [PHY_LANE-1:0] cplllock_out;  
    wire [PHY_LANE-1:0] cpllpd_in;
    wire [PHY_LANE-1:0] cpllreset_in;
    wire [PHY_LANE-1:0] dmonfiforeset_in ;
    wire [PHY_LANE-1:0] dmonitorclk_in ;
    wire [(PHY_LANE*16)-1:0] dmonitorout_out ;
    wire [PHY_LANE-1:0] eyescanreset_in;
    wire [PHY_LANE-1:0] gtpowergood_out;
    wire [PHY_LANE-1:0] gtrefclk0_in;
    wire [PHY_LANE-1:0] gtrxreset_in ;                                          
    wire [PHY_LANE-1:0] gttxreset_in ;                                          
    wire gtwiz_reset_rx_done_in     ;                                                                                      
    wire gtwiz_reset_tx_done_in     ;                                                
    wire gtwiz_userclk_rx_active_in ;                                                
    wire gtwiz_userclk_tx_active_in ;                                                

    wire [(PHY_LANE* 3)-1:0] loopback_in ;                                               
    wire [PHY_LANE-1:0] pcieeqrxeqadaptdone_in ;                                          
    wire [PHY_LANE-1:0] pcierategen3_out ;  
    wire [PHY_LANE-1:0] pcierateidle_out ;       
    wire [PHY_LANE-1:0] pcierstidle_in ;                                          
    wire [PHY_LANE-1:0] pciersttxsyncstart_in ;                                          
    wire [PHY_LANE-1:0] pciesynctxsyncdone_out ;                      
    wire [PHY_LANE-1:0] pcieusergen3rdy_out ; 
    wire [PHY_LANE-1:0] pcieuserphystatusrst_out;  
    wire [PHY_LANE-1:0] pcieuserratedone_in ;                                          
    wire [PHY_LANE-1:0] pcieuserratestart_out ;  
    wire [PHY_LANE-1:0] phystatus_out ;
    wire [PHY_LANE-1:0] rx8b10ben_in ;                                                          
    wire [PHY_LANE-1:0] rxbufreset_in ;
    wire [(PHY_LANE*3)-1:0] rxbufstatus_out ;
    wire [PHY_LANE-1 : 0] rxbyteisaligned_out ; 
    wire [PHY_LANE-1 : 0] rxbyterealign_out ; 
    wire [PHY_LANE-1:0] rxcdrhold_in ;                                          
    wire [PHY_LANE-1:0] rxcdrlock_out ;                                                          
    wire [PHY_LANE-1:0] rxcdrreset_in ;
    wire [(PHY_LANE * 2)-1 : 0] rxclkcorcnt_out; 
    wire [PHY_LANE-1:0] rxcommadet_out ;
    wire [PHY_LANE-1:0] rxcommadeten_in  ;
    wire [(PHY_LANE*16)-1:0] rxctrl0_out;  
    wire [(PHY_LANE*16)-1:0] rxctrl1_out;  
    wire [(PHY_LANE*8)-1:0] rxctrl2_out;  
    wire [(PHY_LANE*8)-1:0] rxctrl3_out;  
    wire [(PHY_LANE*128)-1:0] rxdata_out;  
    wire [PHY_LANE-1 : 0] rxdfeagchold_in;  
    wire [PHY_LANE-1 : 0] rxdfecfokhold_in; 
    wire [PHY_LANE-1 : 0] rxdfekhhold_in;             
    wire [PHY_LANE-1 : 0] rxdfelfhold_in;   
    wire [PHY_LANE-1:0] rxdfelpmreset_in;
    wire [PHY_LANE-1 : 0] rxdfetap10hold_in;       
    wire [PHY_LANE-1 : 0] rxdfetap11hold_in;       
    wire [PHY_LANE-1 : 0] rxdfetap12hold_in;        
    wire [PHY_LANE-1 : 0] rxdfetap13hold_in;       
    wire [PHY_LANE-1 : 0] rxdfetap14hold_in;       
    wire [PHY_LANE-1 : 0] rxdfetap15hold_in;       
    wire [PHY_LANE-1 : 0] rxdfetap2hold_in;        
    wire [PHY_LANE-1 : 0] rxdfetap3hold_in;        
    wire [PHY_LANE-1 : 0] rxdfetap4hold_in;       
    wire [PHY_LANE-1 : 0] rxdfetap5hold_in;           
    wire [PHY_LANE-1 : 0] rxdfetap6hold_in;       
    wire [PHY_LANE-1 : 0] rxdfetap7hold_in;        
    wire [PHY_LANE-1 : 0] rxdfetap8hold_in;       
    wire [PHY_LANE-1 : 0] rxdfetap9hold_in;       
    wire [PHY_LANE-1 : 0] rxdfeuthold_in;             
    wire [PHY_LANE-1 : 0] rxdfevphold_in;             
    wire [PHY_LANE-1:0] rxdlysresetdone_out ;     
    wire [PHY_LANE-1:0] rxelecidle_out;
    wire [PHY_LANE-1:0] rxlpmen_in;                                                            
    wire [PHY_LANE-1 : 0] rxlpmgchold_in;              
    wire [PHY_LANE-1 : 0] rxlpmhfhold_in;            
    wire [PHY_LANE-1 : 0] rxlpmlfhold_in;              
    wire [PHY_LANE-1 : 0] rxlpmoshold_in;   
    wire [PHY_LANE-1:0] rxmcommaalignen_in;                                                    
    wire [PHY_LANE-1 : 0] rxoshold_in;                  
    wire [PHY_LANE-1 : 0] rxoutclk_out; 
    wire [PHY_LANE-1:0] rxoutclkfabric_out;
    wire [PHY_LANE-1:0] rxoutclkpcs_out;   
    wire [PHY_LANE-1:0] rxpcommaalignen_in;                                                    
    wire [PHY_LANE-1:0] rxpcsreset_in;
    wire [(PHY_LANE* 2)-1:0]rxpd_in ;                                              
    wire [PHY_LANE-1:0] rxphaligndone_out ;
    wire [PHY_LANE-1:0] rxpmareset_in ;
    wire [PHY_LANE-1:0] rxpmaresetdone_out ;           
    wire [PHY_LANE-1:0] rxpolarity_in ;                                          
    wire [PHY_LANE-1:0] rxprbscntreset_in ; 
    wire [PHY_LANE-1:0] rxprbserr_out ;                                        
    wire [PHY_LANE-1:0] rxprbslocked_out ;
    wire [(PHY_LANE* 4)-1:0] rxprbssel_in ;                                               
    wire [PHY_LANE-1:0] rxprogdivreset_in ;                                          
    wire [(PHY_LANE* 3)-1:0] rxrate_in;
    wire [PHY_LANE-1:0] rxratedone_out;
    wire [PHY_LANE-1:0] rxrecclkout_out;   
    wire [PHY_LANE-1:0] rxresetdone_out ;              
    wire [PHY_LANE-1:0] rxslide_in ;                                                
    wire [(PHY_LANE* 3)-1:0] rxstatus_out;
    wire [PHY_LANE-1:0] rxsyncdone_out;
    wire [PHY_LANE-1:0] rxtermination_in;
    wire [PHY_LANE-1:0] rxuserrdy_in;                                          
    wire [PHY_LANE-1:0] rxusrclk2_in;                                          
    wire [PHY_LANE-1:0] rxusrclk_in;                                          
    wire [PHY_LANE-1:0] rxvalid_out;
    wire [PHY_LANE-1:0] tx8b10ben_in;                                                          
    wire [(PHY_LANE*16)-1:0] txctrl0_in;
    wire [(PHY_LANE*16)-1:0] txctrl1_in;
    wire [(PHY_LANE* 8)-1:0] txctrl2_in;
    wire [(PHY_LANE*128)-1:0] txdata_in; 
    wire [(PHY_LANE* 2)-1:0] txdeemph_in ;                                          
    wire [PHY_LANE-1:0] txdetectrx_in ;                                          
    wire [(PHY_LANE*5)-1:0] txdiffctrl_in;
    wire [PHY_LANE-1:0] txdlybypass_in ;                                                
    wire [PHY_LANE-1:0] txdlyen_in ;                                                
    wire [PHY_LANE-1:0] txdlyhold_in ;                                                
    wire [PHY_LANE-1:0] txdlyovrden_in ;                                                
    wire [PHY_LANE-1:0] txdlysreset_in ;                                                
    wire [PHY_LANE-1:0] txdlysresetdone_out ;     
    wire [PHY_LANE-1:0] txdlyupdown_in ;                                                
    wire [PHY_LANE-1:0] txelecidle_in ;                                          
    wire [(PHY_LANE* 7)-1:0] txmaincursor_in ;                                               
    wire [(PHY_LANE* 3)-1:0]txmargin_in ;                                              
    wire [PHY_LANE-1:0] txoutclk_out ;
    wire [PHY_LANE-1:0] txoutclkfabric_out;
    wire [PHY_LANE-1:0] txoutclkpcs_out;   
    wire [(PHY_LANE* 3)-1:0]txoutclksel_in ;                                           
    wire [PHY_LANE-1:0] txpcsreset_in;
    wire [(PHY_LANE* 2)-1:0]txpd_in ;                                              
    wire [PHY_LANE-1:0] txphalign_in ;                                                
    wire [PHY_LANE-1:0] txphaligndone_out;  
    wire [PHY_LANE-1:0] txphalignen_in ;                                                
    wire [PHY_LANE-1:0] txphdlypd_in ;                                                
    wire [PHY_LANE-1:0] txphdlyreset_in ;                                                
    wire [PHY_LANE-1:0] txphdlytstclk_in ;                                                
    wire [PHY_LANE-1:0] txphinit_in ;                                                
    wire [PHY_LANE-1:0] txphinitdone_out ;
    wire [PHY_LANE-1:0] txphovrden_in ;                                                
    wire [PHY_LANE-1:0] txpmareset_in;
    wire [PHY_LANE-1 : 0] txpmaresetdone_out; 
    wire [(PHY_LANE* 5)-1:0] txpostcursor_in ;                                               
    wire [PHY_LANE-1:0] txprbsforceerr_in ;                                          
    wire [(PHY_LANE* 4)-1:0] txprbssel_in ;                                               
    wire [(PHY_LANE* 5)-1:0] txprecursor_in ;                                               
    wire [PHY_LANE-1:0] txprgdivresetdone_out ;  
    wire [PHY_LANE-1:0] txprogdivreset_in ;                                          
    wire [(PHY_LANE* 3)-1:0] txrate_in ;
    wire [PHY_LANE-1:0] txresetdone_out ;
    wire [PHY_LANE-1:0] txswing_in ;                                          
    wire [(PHY_LANE-1) : 0] txsyncallin_in; 
    wire [PHY_LANE-1 : 0] txsyncdone_out; 
    wire [(PHY_LANE-1) : 0] txsyncin_in;   
    wire [PHY_LANE-1:0] txsyncmode_in;
    wire [PHY_LANE-1:0] txsyncout_out;  
    wire [PHY_LANE-1:0] txuserrdy_in ;                                          
    wire [PHY_LANE-1:0] txusrclk2_in ;                                          
    wire [PHY_LANE-1:0] txusrclk_in ;                                          

    wire [PHY_LANE-1:0] rxcdrfreqreset_in;
    wire [PHY_LANE-1:0] resetovrd_in;
    wire [PHY_LANE-1:0] rxratemode_in;

    assign rxcdrfreqreset_in = {PHY_LANE{1'b0}};
    assign resetovrd_in = {PHY_LANE{1'b0}};

    wire [PHY_LANE-1:0] qpll0freqlock_in; 
    wire [PHY_LANE-1:0] qpll1freqlock_in; 

    assign qpll0freqlock_in = {PHY_LANE{qpll0lock_all}};
    assign qpll1freqlock_in = {PHY_LANE{qpll1lock_all}};

    wire [(PHY_LANE-1)>>2 : 0]   qpll0pd_in;
    wire [(PHY_LANE-1)>>2 : 0]   qpll0reset_in;
    wire [(PHY_LANE-1)>>2 : 0]   qpll1pd_in;
    wire [(PHY_LANE-1)>>2 : 0]   qpll1reset_in;
    wire [(PHY_LANE*2)-1 : 0]    pcierateqpllpd_out;              
    wire [(PHY_LANE*2)-1 : 0]    pcierateqpllreset_out;



    wire [(PHY_LANE* 1)-1:0]  drpclk_in;
    wire [(PHY_LANE-1)>>2:0]  drpclk_common_in;

    assign drpclk_in = GT_DRPCLK;

    wire [(PHY_LANE* 10)-1:0] drpaddr_in;
    wire [(PHY_LANE* 16)-1:0] drpdi_in;
    wire [(PHY_LANE* 1)-1:0]  drpen_in;
    wire [(PHY_LANE* 1)-1:0]  drpwe_in;
    wire [(PHY_LANE* 16)-1:0] drpdo_out;
    wire [(PHY_LANE* 1)-1:0]  drprdy_out;

    wire [((((PHY_LANE-1)>>2)+1)*16)-1:0] drpaddr_common_in;
    wire [   (PHY_LANE-1)>>2          :0] drpen_common_in;
    wire [   (PHY_LANE-1)>>2          :0] drpwe_common_in;
    wire [((((PHY_LANE-1)>>2)+1)*16)-1:0] drpdi_common_in;
    wire [   (PHY_LANE-1)>>2          :0] drprdy_common_out;
    wire [((((PHY_LANE-1)>>2)+1)*16)-1:0] drpdo_common_out;

genvar m;                                                                                                      

generate for (m=0; m<PHY_LANE; m=m+1)                                                      
                                                                                                    
    begin : drp_sigs 
                                 
    assign drpaddr_in[(10*m)+9:(10*m)] = GT_DRPADDR[(10 * ((PHY_LANE - 1) - m)) + 9 : (10 * ((PHY_LANE - 1) - m))];
    assign drpdi_in[(16*m)+15:(16*m)] = GT_DRPDI[(16 * ((PHY_LANE - 1) - m)) + 15 : (16 * ((PHY_LANE - 1) - m))];
    assign drpen_in[m] = GT_DRPEN[((PHY_LANE-1)-m)];
    assign drpwe_in[m] = GT_DRPWE[((PHY_LANE-1)-m)];
    assign GT_DRPDO[(16*m)+15:(16*m)] = drpdo_out[(16 * ((PHY_LANE - 1) - m)) + 15 : (16 * ((PHY_LANE - 1) - m))];
    assign GT_DRPRDY[m] = drprdy_out[((PHY_LANE-1)-m)];

    end
endgenerate

   // assign drpaddr_in = GT_DRPADDR;
   // assign drpdi_in = GT_DRPDI;
   // assign drpen_in = GT_DRPEN;
   // assign drpwe_in = GT_DRPWE;
   // assign GT_DRPDO = drpdo_out;
   // assign GT_DRPRDY = drprdy_out;

    assign drpaddr_common_in = GTCOM_DRPADDR;
    assign drpen_common_in = GTCOM_DRPEN;
    assign drpwe_common_in = GTCOM_DRPWE;
    assign drpdi_common_in = GTCOM_DRPDI;
    assign GTCOM_DRPRDY = drprdy_common_out;
    assign GTCOM_DRPDO = drpdo_common_out;

    wire gtwiz_userclk_tx_reset_in;
    wire [(PHY_LANE* 18)-1:0] gtwiz_gtye4_cpll_cal_txoutclk_period_in;
    wire [(PHY_LANE* 18)-1:0] gtwiz_gtye4_cpll_cal_cnt_tol_in;
    wire [(PHY_LANE*  1)-1:0] gtwiz_gtye4_cpll_cal_bufg_ce_in;

/*
    assign gtwiz_gtye4_cpll_cal_txoutclk_period_in = {PHY_LANE{18'd4000}}; 
    assign gtwiz_gtye4_cpll_cal_cnt_tol_in         = {PHY_LANE{18'd40}};    
*/
    assign gtwiz_gtye4_cpll_cal_txoutclk_period_in = {PHY_LANE{18'd5000}};  
    assign gtwiz_gtye4_cpll_cal_cnt_tol_in         = {PHY_LANE{18'd50}};    
    assign gtwiz_userclk_tx_reset_in                 = bufgtreset_out[15];
    assign gtwiz_gtye4_cpll_cal_bufg_ce_in  = {PHY_LANE{bufgtce_out[15]}};
//-------------------------------------------------------------------------------------------------
//  Internal Signals
//-------------------------------------------------------------------------------------------------- 

    wire [(PHY_LANE* 3)-1:0] rate;
    wire [(PHY_LANE*16)-1:0] pcsrsvdout_out;
    wire [(PHY_LANE*16)-1:0] pcsrsvdin_in;
    wire [((((PHY_LANE-1)>>2)+1)* 5)-1:0] qpllrsvd2_3;
 
 
    wire [PHY_LANE-1:0]         gtyrxn_in ; 
    wire [PHY_LANE-1:0]         gtyrxp_in ; 
    wire [PHY_LANE-1:0]         gtytxn_out; 
    wire [PHY_LANE-1:0]         gtytxp_out; 

    wire [PHY_LANE-1:0] eyescandataerror_out;
    wire [PHY_LANE-1:0] txinhibit_in;    // Check                                      

    wire [((((PHY_LANE-1)>>2)+1)* 5)-1:0] qpllrsvd2_in;
    wire [((((PHY_LANE-1)>>2)+1)* 5)-1:0] qpllrsvd3_in;

//---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    assign qpll0lock_all   = &qpll0lock_out;
    assign qpll1lock_all   = &qpll1lock_out;
    assign txsyncallin_all = &txphaligndone_out;    
    
    assign gtwiz_userclk_tx_active_in = GT_TXUSERRDY[PHY_LANE-1];                                                
    assign gtwiz_userclk_rx_active_in = GT_RXUSERRDY[PHY_LANE-1];                                                
    assign gtwiz_reset_tx_done_in     = GT_TXRESETDONE[PHY_LANE-1];                                                
    assign gtwiz_reset_rx_done_in     = GT_RXRESETDONE[PHY_LANE-1];                                                                                      
    assign gtrefclk01_in         = ({(((PHY_LANE-1)>>2)+1){GT_GTREFCLK0}});                                                  
    assign gtrefclk00_in         = ({(((PHY_LANE-1)>>2)+1){GT_GTREFCLK0}});   // Check                                               
    assign gtrefclk0_in          = ({PHY_LANE{GT_GTREFCLK0}});                                                    
    assign rx8b10ben_in          = (~pcierategen3_out);                                                
    assign rxlpmen_in            = GT_RXLPMEN;
    assign rxmcommaalignen_in    = (~pcierategen3_out);                                                
    assign rxpcommaalignen_in    = (~pcierategen3_out);                                                
    assign tx8b10ben_in          = (~pcierategen3_out);                                                
    assign rxcommadeten_in       = ({PHY_LANE{1'd1}});     // Always 1'd1            
    assign rxslide_in            = ({PHY_LANE{1'd0}});                                                
    assign txdlyen_in            = ({PHY_LANE{1'd0}});                                                
    assign txdlyhold_in          = ({PHY_LANE{1'd0}});                                                
    assign txdlyovrden_in        = ({PHY_LANE{1'd0}});                                                
    assign txdlysreset_in        = ({PHY_LANE{1'd0}});                                                
    assign txdlyupdown_in        = ({PHY_LANE{1'd0}});                                                
    assign txphalign_in          = ({PHY_LANE{1'd0}});                                                
    assign txphalignen_in        = ({PHY_LANE{1'd0}});                                                
    assign txdlybypass_in        = ({PHY_LANE{1'd0}});                                                
 

    assign txphdlypd_in          = {1'b0, !txpmaresetdone_out[1], !txpmaresetdone_out[2], !txpmaresetdone_out[3], !txpmaresetdone_out[4], !txpmaresetdone_out[5], !txpmaresetdone_out[6], !txpmaresetdone_out[7], !txpmaresetdone_out[8], !txpmaresetdone_out[9], !txpmaresetdone_out[10], !txpmaresetdone_out[11], !txpmaresetdone_out[12], !txpmaresetdone_out[13], !txpmaresetdone_out[14], !txpmaresetdone_out[15] };
 
 
 
 
    assign txphdlyreset_in       = ({PHY_LANE{1'd0}});                                                
    assign txphdlytstclk_in      = ({PHY_LANE{1'd0}});                                                
    assign txphinit_in           = ({PHY_LANE{1'd0}});                                                
    assign txphovrden_in         = ({PHY_LANE{1'd0}});                                                
    assign txsyncallin_in        = ({PHY_LANE{txsyncallin_all}}); // From all lanes                         

    assign qpllrsvd2_in          = qpllrsvd2_3;
    assign qpllrsvd3_in          = qpllrsvd2_3;
    assign rxrate_in             = rate;
    assign txrate_in             = rate;
//---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
 // dynamic GT Wizard instance call
   xdma_0_pcie4_ip_gt xdma_0_pcie4_ip_gt_i
  (
   .bufgtce_out(bufgtce_out),
   .bufgtcemask_out(bufgtcemask_out),
   .bufgtdiv_out(bufgtdiv_out),
   .bufgtreset_out(bufgtreset_out),
   .bufgtrstmask_out(bufgtrstmask_out),
   .cpllfreqlock_in(cpllfreqlock_in),
   .cplllock_out(cplllock_out),
   .cpllpd_in(cpllpd_in),
   .cpllreset_in(cpllreset_in),
   .dmonfiforeset_in(dmonfiforeset_in),
   .dmonitorclk_in(dmonitorclk_in),
   .dmonitorout_out(dmonitorout_out),
   .drpaddr_common_in(drpaddr_common_in),
   .drpaddr_in(drpaddr_in),
   .drpclk_common_in(drpclk_common_in),
   .drpclk_in(drpclk_in),
   .drpdi_common_in(drpdi_common_in),
   .drpdi_in(drpdi_in),
   .drpdo_common_out(drpdo_common_out),
   .drpdo_out(drpdo_out),
   .drpen_common_in(drpen_common_in),
   .drpen_in(drpen_in),
   .drprdy_common_out(drprdy_common_out),
   .drprdy_out(drprdy_out),
   .drpwe_common_in(drpwe_common_in),
   .drpwe_in(drpwe_in),
   .eyescanreset_in(eyescanreset_in),
   .gtpowergood_out(gtpowergood_out),
   .gtrefclk00_in(gtrefclk00_in),
   .gtrefclk01_in(gtrefclk01_in),
   .gtrefclk0_in(gtrefclk0_in),
   .gtrxreset_in(gtrxreset_in),
   .gttxreset_in(gttxreset_in),
   .gtwiz_gtye4_cpll_cal_bufg_ce_in(gtwiz_gtye4_cpll_cal_bufg_ce_in),
   .gtwiz_gtye4_cpll_cal_cnt_tol_in(gtwiz_gtye4_cpll_cal_cnt_tol_in),
   .gtwiz_gtye4_cpll_cal_txoutclk_period_in(gtwiz_gtye4_cpll_cal_txoutclk_period_in),
   .gtwiz_reset_rx_done_in(gtwiz_reset_rx_done_in),
   .gtwiz_reset_tx_done_in(gtwiz_reset_tx_done_in),
   .gtwiz_userclk_rx_active_in(gtwiz_userclk_rx_active_in),
   .gtwiz_userclk_tx_active_in(gtwiz_userclk_tx_active_in),
   .gtwiz_userclk_tx_reset_in(gtwiz_userclk_tx_reset_in),
   .gtyrxn_in(gtyrxn_in),
   .gtyrxp_in(gtyrxp_in),
   .gtytxn_out(gtytxn_out),
   .gtytxp_out(gtytxp_out),
   .loopback_in(loopback_in),
   .pcieeqrxeqadaptdone_in(pcieeqrxeqadaptdone_in),
   .pcierategen3_out(pcierategen3_out),
   .pcierateidle_out(pcierateidle_out),
   .pcierateqpll0_in(pcierateqpll0_in),
   .pcierateqpll1_in(pcierateqpll1_in),
   .pcierateqpllpd_out(pcierateqpllpd_out),
   .pcierateqpllreset_out(pcierateqpllreset_out),
   .pcierstidle_in(pcierstidle_in),
   .pciersttxsyncstart_in(pciersttxsyncstart_in),
   .pciesynctxsyncdone_out(pciesynctxsyncdone_out),
   .pcieusergen3rdy_out(pcieusergen3rdy_out),
   .pcieuserphystatusrst_out(pcieuserphystatusrst_out),
   .pcieuserratedone_in(pcieuserratedone_in),
   .pcieuserratestart_out(pcieuserratestart_out),
   .phystatus_out(phystatus_out),
   .qpll0freqlock_in(qpll0freqlock_in),
   .qpll0lock_out(qpll0lock_out),
   .qpll0outclk_out(qpll0outclk_out),
   .qpll0outrefclk_out(qpll0outrefclk_out),
   .qpll0pd_in(qpll0pd_in),
   .qpll0reset_in(qpll0reset_in),
   .qpll1freqlock_in(qpll1freqlock_in),
   .qpll1lock_out(qpll1lock_out),
   .qpll1outclk_out(qpll1outclk_out),
   .qpll1outrefclk_out(qpll1outrefclk_out),
   .qpll1pd_in(qpll1pd_in),
   .qpll1reset_in(qpll1reset_in),
   .resetovrd_in(resetovrd_in),
   .rx8b10ben_in(rx8b10ben_in),
   .rxbufreset_in(rxbufreset_in),
   .rxbufstatus_out(rxbufstatus_out),
   .rxbyteisaligned_out(rxbyteisaligned_out),
   .rxbyterealign_out(rxbyterealign_out),
   .rxcdrfreqreset_in(rxcdrfreqreset_in),
   .rxcdrhold_in(rxcdrhold_in),
   .rxcdrlock_out(rxcdrlock_out),
   .rxcdrreset_in(rxcdrreset_in),
   .rxclkcorcnt_out(rxclkcorcnt_out),
   .rxcommadet_out(rxcommadet_out),
   .rxcommadeten_in(rxcommadeten_in),
   .rxctrl0_out(rxctrl0_out),
   .rxctrl1_out(rxctrl1_out),
   .rxctrl2_out(rxctrl2_out),
   .rxctrl3_out(rxctrl3_out),
   .rxdata_out(rxdata_out),
   .rxdfeagchold_in(rxdfeagchold_in),
   .rxdfecfokhold_in(rxdfecfokhold_in),
   .rxdfekhhold_in(rxdfekhhold_in),
   .rxdfelfhold_in(rxdfelfhold_in),
   .rxdfelpmreset_in(rxdfelpmreset_in),
   .rxdfetap10hold_in(rxdfetap10hold_in),
   .rxdfetap11hold_in(rxdfetap11hold_in),
   .rxdfetap12hold_in(rxdfetap12hold_in),
   .rxdfetap13hold_in(rxdfetap13hold_in),
   .rxdfetap14hold_in(rxdfetap14hold_in),
   .rxdfetap15hold_in(rxdfetap15hold_in),
   .rxdfetap2hold_in(rxdfetap2hold_in),
   .rxdfetap3hold_in(rxdfetap3hold_in),
   .rxdfetap4hold_in(rxdfetap4hold_in),
   .rxdfetap5hold_in(rxdfetap5hold_in),
   .rxdfetap6hold_in(rxdfetap6hold_in),
   .rxdfetap7hold_in(rxdfetap7hold_in),
   .rxdfetap8hold_in(rxdfetap8hold_in),
   .rxdfetap9hold_in(rxdfetap9hold_in),
   .rxdfeuthold_in(rxdfeuthold_in),
   .rxdfevphold_in(rxdfevphold_in),
   .rxdlysresetdone_out(rxdlysresetdone_out),
   .rxelecidle_out(rxelecidle_out),
   .rxlpmen_in(rxlpmen_in),
   .rxlpmgchold_in(rxlpmgchold_in),
   .rxlpmhfhold_in(rxlpmhfhold_in),
   .rxlpmlfhold_in(rxlpmlfhold_in),
   .rxlpmoshold_in(rxlpmoshold_in),
   .rxmcommaalignen_in(rxmcommaalignen_in),
   .rxoshold_in(rxoshold_in),
   .rxoutclk_out(rxoutclk_out),
   .rxoutclkfabric_out(rxoutclkfabric_out),
   .rxoutclkpcs_out(rxoutclkpcs_out),
   .rxpcommaalignen_in(rxpcommaalignen_in),
   .rxpcsreset_in(rxpcsreset_in),
   .rxpd_in(rxpd_in),
   .rxphaligndone_out(rxphaligndone_out),
   .rxpmareset_in(rxpmareset_in),
   .rxpmaresetdone_out(rxpmaresetdone_out),
   .rxpolarity_in(rxpolarity_in),
   .rxprbscntreset_in(rxprbscntreset_in),
   .rxprbserr_out(rxprbserr_out),
   .rxprbslocked_out(rxprbslocked_out),
   .rxprbssel_in(rxprbssel_in),
   .rxprogdivreset_in(rxprogdivreset_in),
   .rxrate_in(rxrate_in),
   .rxratedone_out(rxratedone_out),
   .rxratemode_in(rxratemode_in),
   .rxrecclkout_out(rxrecclkout_out),
   .rxresetdone_out(rxresetdone_out),
   .rxslide_in(rxslide_in),
   .rxstatus_out(rxstatus_out),
   .rxsyncdone_out(rxsyncdone_out),
   .rxtermination_in(rxtermination_in),
   .rxuserrdy_in(rxuserrdy_in),
   .rxusrclk2_in(rxusrclk2_in),
   .rxusrclk_in(rxusrclk_in),
   .rxvalid_out(rxvalid_out),
   .tx8b10ben_in(tx8b10ben_in),
   .txctrl0_in(txctrl0_in),
   .txctrl1_in(txctrl1_in),
   .txctrl2_in(txctrl2_in),
   .txdata_in(txdata_in),
   .txdeemph_in(txdeemph_in),
   .txdetectrx_in(txdetectrx_in),
   .txdiffctrl_in(txdiffctrl_in),
   .txdlybypass_in(txdlybypass_in),
   .txdlyen_in(txdlyen_in),
   .txdlyhold_in(txdlyhold_in),
   .txdlyovrden_in(txdlyovrden_in),
   .txdlysreset_in(txdlysreset_in),
   .txdlysresetdone_out(txdlysresetdone_out),
   .txdlyupdown_in(txdlyupdown_in),
   .txelecidle_in(txelecidle_in),
   .txmaincursor_in(txmaincursor_in),
   .txmargin_in(txmargin_in),
   .txoutclk_out(txoutclk_out),
   .txoutclkfabric_out(txoutclkfabric_out),
   .txoutclkpcs_out(txoutclkpcs_out),
   .txoutclksel_in(txoutclksel_in),
   .txpcsreset_in(txpcsreset_in),
   .txpd_in(txpd_in),
   .txphalign_in(txphalign_in),
   .txphaligndone_out(txphaligndone_out),
   .txphalignen_in(txphalignen_in),
   .txphdlypd_in(txphdlypd_in),
   .txphdlyreset_in(txphdlyreset_in),
   .txphdlytstclk_in(txphdlytstclk_in),
   .txphinit_in(txphinit_in),
   .txphinitdone_out(txphinitdone_out),
   .txphovrden_in(txphovrden_in),
   .txpmareset_in(txpmareset_in),
   .txpmaresetdone_out(txpmaresetdone_out),
   .txpostcursor_in(txpostcursor_in),
   .txprbsforceerr_in(txprbsforceerr_in),
   .txprbssel_in(txprbssel_in),
   .txprecursor_in(txprecursor_in),
   .txprgdivresetdone_out(txprgdivresetdone_out),
   .txprogdivreset_in(txprogdivreset_in),
   .txrate_in(txrate_in),
   .txresetdone_out(txresetdone_out),
   .txswing_in(txswing_in),
   .txsyncallin_in(txsyncallin_in),
   .txsyncdone_out(txsyncdone_out),
   .txsyncin_in(txsyncin_in),
   .txsyncmode_in(txsyncmode_in),
   .txsyncout_out(txsyncout_out),
   .txuserrdy_in(txuserrdy_in),
   .txusrclk2_in(txusrclk2_in),
   .txusrclk_in(txusrclk_in)
  );

//--------------------------------------------------------------------- Mapping ----------------------------------------------------------------------------------------------------------------------------------------------

    assign cpllfreqlock_in = ({PHY_LANE{cplllock_out[15]}});
    assign txsyncmode_in    = 16'h8000; // X0Y15 is the Master. So, txsyncmode_in[15] = 1'b1;
    assign txsyncin_in      = ({PHY_LANE{txsyncout_out[15]}}); // From Master Lane 0 - X0Y15                  
    assign pcsrsvdin_in     = {PHY_LANE{14'd0,cplllock_out[15],qpll1lock_all}};
    assign drpclk_common_in = {4{GTCOM_DRPCLK}};
    assign pcierateqpll0_in = {4{1'b0,GT_RATE[1:0]}};
    assign pcierateqpll1_in = {4{1'b0,GT_RATE[1:0]}};

    assign gtyrxn_in              = {GT_RXN[0],GT_RXN[1],GT_RXN[2],GT_RXN[3],GT_RXN[4],GT_RXN[5],GT_RXN[6],GT_RXN[7],GT_RXN[8],GT_RXN[9],GT_RXN[10],GT_RXN[11],GT_RXN[12],GT_RXN[13],GT_RXN[14],GT_RXN[15]};
    assign gtyrxp_in              = {GT_RXP[0],GT_RXP[1],GT_RXP[2],GT_RXP[3],GT_RXP[4],GT_RXP[5],GT_RXP[6],GT_RXP[7],GT_RXP[8],GT_RXP[9],GT_RXP[10],GT_RXP[11],GT_RXP[12],GT_RXP[13],GT_RXP[14],GT_RXP[15]};
    assign GT_TXN                 = {gtytxn_out[0],gtytxn_out[1],gtytxn_out[2],gtytxn_out[3],gtytxn_out[4],gtytxn_out[5],gtytxn_out[6],gtytxn_out[7],gtytxn_out[8],gtytxn_out[9],gtytxn_out[10],gtytxn_out[11],gtytxn_out[12],gtytxn_out[13],gtytxn_out[14],gtytxn_out[15]};                                  
    assign GT_TXP                 = {gtytxp_out[0],gtytxp_out[1],gtytxp_out[2],gtytxp_out[3],gtytxp_out[4],gtytxp_out[5],gtytxp_out[6],gtytxp_out[7],gtytxp_out[8],gtytxp_out[9],gtytxp_out[10],gtytxp_out[11],gtytxp_out[12],gtytxp_out[13],gtytxp_out[14],gtytxp_out[15]};                                  
    assign rxratemode_in          = {GT_RXRATEMODE[0],GT_RXRATEMODE[1],GT_RXRATEMODE[2],GT_RXRATEMODE[3],GT_RXRATEMODE[4],GT_RXRATEMODE[5],GT_RXRATEMODE[6],GT_RXRATEMODE[7],GT_RXRATEMODE[8],GT_RXRATEMODE[9],GT_RXRATEMODE[10],GT_RXRATEMODE[11],GT_RXRATEMODE[12],GT_RXRATEMODE[13],GT_RXRATEMODE[14],GT_RXRATEMODE[15]};
    assign cpllpd_in              = {GT_CPLLPD[0],GT_CPLLPD[1],GT_CPLLPD[2],GT_CPLLPD[3],GT_CPLLPD[4],GT_CPLLPD[5],GT_CPLLPD[6],GT_CPLLPD[7],GT_CPLLPD[8],GT_CPLLPD[9],GT_CPLLPD[10],GT_CPLLPD[11],GT_CPLLPD[12],GT_CPLLPD[13],GT_CPLLPD[14],GT_CPLLPD[15]};
    assign rxtermination_in           = {GT_RXTERMINATION[0],GT_RXTERMINATION[1],GT_RXTERMINATION[2],GT_RXTERMINATION[3],GT_RXTERMINATION[4],GT_RXTERMINATION[5],GT_RXTERMINATION[6],GT_RXTERMINATION[7],GT_RXTERMINATION[8],GT_RXTERMINATION[9],GT_RXTERMINATION[10],GT_RXTERMINATION[11],GT_RXTERMINATION[12],GT_RXTERMINATION[13],GT_RXTERMINATION[14],GT_RXTERMINATION[15]};
    assign txpmareset_in              = {GT_TXPMARESET[0],GT_TXPMARESET[1],GT_TXPMARESET[2],GT_TXPMARESET[3],GT_TXPMARESET[4],GT_TXPMARESET[5],GT_TXPMARESET[6],GT_TXPMARESET[7],GT_TXPMARESET[8],GT_TXPMARESET[9],GT_TXPMARESET[10],GT_TXPMARESET[11],GT_TXPMARESET[12],GT_TXPMARESET[13],GT_TXPMARESET[14],GT_TXPMARESET[15]};
    assign rxpmareset_in              = {GT_RXPMARESET[0],GT_RXPMARESET[1],GT_RXPMARESET[2],GT_RXPMARESET[3],GT_RXPMARESET[4],GT_RXPMARESET[5],GT_RXPMARESET[6],GT_RXPMARESET[7],GT_RXPMARESET[8],GT_RXPMARESET[9],GT_RXPMARESET[10],GT_RXPMARESET[11],GT_RXPMARESET[12],GT_RXPMARESET[13],GT_RXPMARESET[14],GT_RXPMARESET[15]};
    assign txpcsreset_in              = {GT_TXPCSRESET[0],GT_TXPCSRESET[1],GT_TXPCSRESET[2],GT_TXPCSRESET[3],GT_TXPCSRESET[4],GT_TXPCSRESET[5],GT_TXPCSRESET[6],GT_TXPCSRESET[7],GT_TXPCSRESET[8],GT_TXPCSRESET[9],GT_TXPCSRESET[10],GT_TXPCSRESET[11],GT_TXPCSRESET[12],GT_TXPCSRESET[13],GT_TXPCSRESET[14],GT_TXPCSRESET[15]};
    assign rxpcsreset_in              = {GT_RXPCSRESET[0],GT_RXPCSRESET[1],GT_RXPCSRESET[2],GT_RXPCSRESET[3],GT_RXPCSRESET[4],GT_RXPCSRESET[5],GT_RXPCSRESET[6],GT_RXPCSRESET[7],GT_RXPCSRESET[8],GT_RXPCSRESET[9],GT_RXPCSRESET[10],GT_RXPCSRESET[11],GT_RXPCSRESET[12],GT_RXPCSRESET[13],GT_RXPCSRESET[14],GT_RXPCSRESET[15]};
    assign rxbufreset_in              = {GT_RXBUFRESET[0],GT_RXBUFRESET[1],GT_RXBUFRESET[2],GT_RXBUFRESET[3],GT_RXBUFRESET[4],GT_RXBUFRESET[5],GT_RXBUFRESET[6],GT_RXBUFRESET[7],GT_RXBUFRESET[8],GT_RXBUFRESET[9],GT_RXBUFRESET[10],GT_RXBUFRESET[11],GT_RXBUFRESET[12],GT_RXBUFRESET[13],GT_RXBUFRESET[14],GT_RXBUFRESET[15]};
    assign rxcdrreset_in              = {GT_RXCDRRESET[0],GT_RXCDRRESET[1],GT_RXCDRRESET[2],GT_RXCDRRESET[3],GT_RXCDRRESET[4],GT_RXCDRRESET[5],GT_RXCDRRESET[6],GT_RXCDRRESET[7],GT_RXCDRRESET[8],GT_RXCDRRESET[9],GT_RXCDRRESET[10],GT_RXCDRRESET[11],GT_RXCDRRESET[12],GT_RXCDRRESET[13],GT_RXCDRRESET[14],GT_RXCDRRESET[15]};
    assign rxdfelpmreset_in              = {GT_RXDFELPMRESET[0],GT_RXDFELPMRESET[1],GT_RXDFELPMRESET[2],GT_RXDFELPMRESET[3],GT_RXDFELPMRESET[4],GT_RXDFELPMRESET[5],GT_RXDFELPMRESET[6],GT_RXDFELPMRESET[7],GT_RXDFELPMRESET[8],GT_RXDFELPMRESET[9],GT_RXDFELPMRESET[10],GT_RXDFELPMRESET[11],GT_RXDFELPMRESET[12],GT_RXDFELPMRESET[13],GT_RXDFELPMRESET[14],GT_RXDFELPMRESET[15]};
    assign cpllreset_in           = {GT_CPLLRESET[0],GT_CPLLRESET[1],GT_CPLLRESET[2],GT_CPLLRESET[3],GT_CPLLRESET[4],GT_CPLLRESET[5],GT_CPLLRESET[6],GT_CPLLRESET[7],GT_CPLLRESET[8],GT_CPLLRESET[9],GT_CPLLRESET[10],GT_CPLLRESET[11],GT_CPLLRESET[12],GT_CPLLRESET[13],GT_CPLLRESET[14],GT_CPLLRESET[15]};
    assign eyescanreset_in        = {GT_EYESCANRESET[0],GT_EYESCANRESET[1],GT_EYESCANRESET[2],GT_EYESCANRESET[3],GT_EYESCANRESET[4],GT_EYESCANRESET[5],GT_EYESCANRESET[6],GT_EYESCANRESET[7],GT_EYESCANRESET[8],GT_EYESCANRESET[9],GT_EYESCANRESET[10],GT_EYESCANRESET[11],GT_EYESCANRESET[12],GT_EYESCANRESET[13],GT_EYESCANRESET[14],GT_EYESCANRESET[15]};
    assign txdiffctrl_in          = {GT_TXDIFFCTRL[4:0],GT_TXDIFFCTRL[9:5],GT_TXDIFFCTRL[14:10],GT_TXDIFFCTRL[19:15],GT_TXDIFFCTRL[24:20],GT_TXDIFFCTRL[29:25],GT_TXDIFFCTRL[34:30],GT_TXDIFFCTRL[39:35],GT_TXDIFFCTRL[44:40],GT_TXDIFFCTRL[49:45],GT_TXDIFFCTRL[54:50],GT_TXDIFFCTRL[59:55],GT_TXDIFFCTRL[64:60],GT_TXDIFFCTRL[69:65],GT_TXDIFFCTRL[74:70],GT_TXDIFFCTRL[79:75]};
    assign txswing_in             = {GT_TXSWING[0],GT_TXSWING[1],GT_TXSWING[2],GT_TXSWING[3],GT_TXSWING[4],GT_TXSWING[5],GT_TXSWING[6],GT_TXSWING[7],GT_TXSWING[8],GT_TXSWING[9],GT_TXSWING[10],GT_TXSWING[11],GT_TXSWING[12],GT_TXSWING[13],GT_TXSWING[14],GT_TXSWING[15]};
    assign txusrclk_in            = {GT_TXUSRCLK[0],GT_TXUSRCLK[1],GT_TXUSRCLK[2],GT_TXUSRCLK[3],GT_TXUSRCLK[4],GT_TXUSRCLK[5],GT_TXUSRCLK[6],GT_TXUSRCLK[7],GT_TXUSRCLK[8],GT_TXUSRCLK[9],GT_TXUSRCLK[10],GT_TXUSRCLK[11],GT_TXUSRCLK[12],GT_TXUSRCLK[13],GT_TXUSRCLK[14],GT_TXUSRCLK[15]};
    assign rxusrclk_in            = {GT_RXUSRCLK[0],GT_RXUSRCLK[1],GT_RXUSRCLK[2],GT_RXUSRCLK[3],GT_RXUSRCLK[4],GT_RXUSRCLK[5],GT_RXUSRCLK[6],GT_RXUSRCLK[7],GT_RXUSRCLK[8],GT_RXUSRCLK[9],GT_RXUSRCLK[10],GT_RXUSRCLK[11],GT_RXUSRCLK[12],GT_RXUSRCLK[13],GT_RXUSRCLK[14],GT_RXUSRCLK[15]};
    assign txdeemph_in            = {GT_TXDEEMPH[1:0],GT_TXDEEMPH[3:2],GT_TXDEEMPH[5:4],GT_TXDEEMPH[7:6],GT_TXDEEMPH[9:8],GT_TXDEEMPH[11:10],GT_TXDEEMPH[13:12],GT_TXDEEMPH[15:14],GT_TXDEEMPH[17:16],GT_TXDEEMPH[19:18],GT_TXDEEMPH[21:20],GT_TXDEEMPH[23:22],GT_TXDEEMPH[25:24],GT_TXDEEMPH[27:26],GT_TXDEEMPH[29:28],GT_TXDEEMPH[31:30]};
    assign rxcdrhold_in           = {GT_RXCDRHOLD[0],GT_RXCDRHOLD[1],GT_RXCDRHOLD[2],GT_RXCDRHOLD[3],GT_RXCDRHOLD[4],GT_RXCDRHOLD[5],GT_RXCDRHOLD[6],GT_RXCDRHOLD[7],GT_RXCDRHOLD[8],GT_RXCDRHOLD[9],GT_RXCDRHOLD[10],GT_RXCDRHOLD[11],GT_RXCDRHOLD[12],GT_RXCDRHOLD[13],GT_RXCDRHOLD[14],GT_RXCDRHOLD[15]};
    assign txusrclk2_in           = {GT_TXUSRCLK2[0],GT_TXUSRCLK2[1],GT_TXUSRCLK2[2],GT_TXUSRCLK2[3],GT_TXUSRCLK2[4],GT_TXUSRCLK2[5],GT_TXUSRCLK2[6],GT_TXUSRCLK2[7],GT_TXUSRCLK2[8],GT_TXUSRCLK2[9],GT_TXUSRCLK2[10],GT_TXUSRCLK2[11],GT_TXUSRCLK2[12],GT_TXUSRCLK2[13],GT_TXUSRCLK2[14],GT_TXUSRCLK2[15]};
    assign rxusrclk2_in           = {GT_RXUSRCLK2[0],GT_RXUSRCLK2[1],GT_RXUSRCLK2[2],GT_RXUSRCLK2[3],GT_RXUSRCLK2[4],GT_RXUSRCLK2[5],GT_RXUSRCLK2[6],GT_RXUSRCLK2[7],GT_RXUSRCLK2[8],GT_RXUSRCLK2[9],GT_RXUSRCLK2[10],GT_RXUSRCLK2[11],GT_RXUSRCLK2[12],GT_RXUSRCLK2[13],GT_RXUSRCLK2[14],GT_RXUSRCLK2[15]};
    assign gttxreset_in           = {GT_GTTXRESET[0],GT_GTTXRESET[1],GT_GTTXRESET[2],GT_GTTXRESET[3],GT_GTTXRESET[4],GT_GTTXRESET[5],GT_GTTXRESET[6],GT_GTTXRESET[7],GT_GTTXRESET[8],GT_GTTXRESET[9],GT_GTTXRESET[10],GT_GTTXRESET[11],GT_GTTXRESET[12],GT_GTTXRESET[13],GT_GTTXRESET[14],GT_GTTXRESET[15]};
    assign gtrxreset_in           = {GT_GTRXRESET[0],GT_GTRXRESET[1],GT_GTRXRESET[2],GT_GTRXRESET[3],GT_GTRXRESET[4],GT_GTRXRESET[5],GT_GTRXRESET[6],GT_GTRXRESET[7],GT_GTRXRESET[8],GT_GTRXRESET[9],GT_GTRXRESET[10],GT_GTRXRESET[11],GT_GTRXRESET[12],GT_GTRXRESET[13],GT_GTRXRESET[14],GT_GTRXRESET[15]};
    assign txuserrdy_in           = {GT_TXUSERRDY[0],GT_TXUSERRDY[1],GT_TXUSERRDY[2],GT_TXUSERRDY[3],GT_TXUSERRDY[4],GT_TXUSERRDY[5],GT_TXUSERRDY[6],GT_TXUSERRDY[7],GT_TXUSERRDY[8],GT_TXUSERRDY[9],GT_TXUSERRDY[10],GT_TXUSERRDY[11],GT_TXUSERRDY[12],GT_TXUSERRDY[13],GT_TXUSERRDY[14],GT_TXUSERRDY[15]};
    assign rxuserrdy_in           = {GT_RXUSERRDY[0],GT_RXUSERRDY[1],GT_RXUSERRDY[2],GT_RXUSERRDY[3],GT_RXUSERRDY[4],GT_RXUSERRDY[5],GT_RXUSERRDY[6],GT_RXUSERRDY[7],GT_RXUSERRDY[8],GT_RXUSERRDY[9],GT_RXUSERRDY[10],GT_RXUSERRDY[11],GT_RXUSERRDY[12],GT_RXUSERRDY[13],GT_RXUSERRDY[14],GT_RXUSERRDY[15]};
    assign txdetectrx_in          = {GT_TXDETECTRX[0],GT_TXDETECTRX[1],GT_TXDETECTRX[2],GT_TXDETECTRX[3],GT_TXDETECTRX[4],GT_TXDETECTRX[5],GT_TXDETECTRX[6],GT_TXDETECTRX[7],GT_TXDETECTRX[8],GT_TXDETECTRX[9],GT_TXDETECTRX[10],GT_TXDETECTRX[11],GT_TXDETECTRX[12],GT_TXDETECTRX[13],GT_TXDETECTRX[14],GT_TXDETECTRX[15]};
    assign txelecidle_in          = {GT_TXELECIDLE[0],GT_TXELECIDLE[1],GT_TXELECIDLE[2],GT_TXELECIDLE[3],GT_TXELECIDLE[4],GT_TXELECIDLE[5],GT_TXELECIDLE[6],GT_TXELECIDLE[7],GT_TXELECIDLE[8],GT_TXELECIDLE[9],GT_TXELECIDLE[10],GT_TXELECIDLE[11],GT_TXELECIDLE[12],GT_TXELECIDLE[13],GT_TXELECIDLE[14],GT_TXELECIDLE[15]};
    assign rxpolarity_in          = {GT_RXPOLARITY[0],GT_RXPOLARITY[1],GT_RXPOLARITY[2],GT_RXPOLARITY[3],GT_RXPOLARITY[4],GT_RXPOLARITY[5],GT_RXPOLARITY[6],GT_RXPOLARITY[7],GT_RXPOLARITY[8],GT_RXPOLARITY[9],GT_RXPOLARITY[10],GT_RXPOLARITY[11],GT_RXPOLARITY[12],GT_RXPOLARITY[13],GT_RXPOLARITY[14],GT_RXPOLARITY[15]};
    assign txprogdivreset_in      = {GT_TXPROGDIVRESET[0],GT_TXPROGDIVRESET[1],GT_TXPROGDIVRESET[2],GT_TXPROGDIVRESET[3],GT_TXPROGDIVRESET[4],GT_TXPROGDIVRESET[5],GT_TXPROGDIVRESET[6],GT_TXPROGDIVRESET[7],GT_TXPROGDIVRESET[8],GT_TXPROGDIVRESET[9],GT_TXPROGDIVRESET[10],GT_TXPROGDIVRESET[11],GT_TXPROGDIVRESET[12],GT_TXPROGDIVRESET[13],GT_TXPROGDIVRESET[14],GT_TXPROGDIVRESET[15]};
    assign rxprogdivreset_in      = {GT_RXPROGDIVRESET[0],GT_RXPROGDIVRESET[1],GT_RXPROGDIVRESET[2],GT_RXPROGDIVRESET[3],GT_RXPROGDIVRESET[4],GT_RXPROGDIVRESET[5],GT_RXPROGDIVRESET[6],GT_RXPROGDIVRESET[7],GT_RXPROGDIVRESET[8],GT_RXPROGDIVRESET[9],GT_RXPROGDIVRESET[10],GT_RXPROGDIVRESET[11],GT_RXPROGDIVRESET[12],GT_RXPROGDIVRESET[13],GT_RXPROGDIVRESET[14],GT_RXPROGDIVRESET[15]};

    assign dmonitorclk_in         = {GT_DMONITORCLK[0],GT_DMONITORCLK[1],GT_DMONITORCLK[2],GT_DMONITORCLK[3],GT_DMONITORCLK[4],GT_DMONITORCLK[5],GT_DMONITORCLK[6],GT_DMONITORCLK[7],GT_DMONITORCLK[8],GT_DMONITORCLK[9],GT_DMONITORCLK[10],GT_DMONITORCLK[11],GT_DMONITORCLK[12],GT_DMONITORCLK[13],GT_DMONITORCLK[14],GT_DMONITORCLK[15]};
    assign dmonfiforeset_in       = {GT_DMONFIFORESET[0],GT_DMONFIFORESET[1],GT_DMONFIFORESET[2],GT_DMONFIFORESET[3],GT_DMONFIFORESET[4],GT_DMONFIFORESET[5],GT_DMONFIFORESET[6],GT_DMONFIFORESET[7],GT_DMONFIFORESET[8],GT_DMONFIFORESET[9],GT_DMONFIFORESET[10],GT_DMONFIFORESET[11],GT_DMONFIFORESET[12],GT_DMONFIFORESET[13],GT_DMONFIFORESET[14],GT_DMONFIFORESET[15]};
    assign GT_DMONITOROUT         = {dmonitorout_out[15:0],dmonitorout_out[31:16],dmonitorout_out[47:32],dmonitorout_out[63:48],dmonitorout_out[79:64],dmonitorout_out[95:80],dmonitorout_out[111:96],dmonitorout_out[127:112],dmonitorout_out[143:128],dmonitorout_out[159:144],dmonitorout_out[175:160],dmonitorout_out[191:176],dmonitorout_out[207:192],dmonitorout_out[223:208],dmonitorout_out[239:224],dmonitorout_out[255:240]};     

    assign GT_TXOUTCLK            = {txoutclk_out[0],txoutclk_out[1],txoutclk_out[2],txoutclk_out[3],txoutclk_out[4],txoutclk_out[5],txoutclk_out[6],txoutclk_out[7],txoutclk_out[8],txoutclk_out[9],txoutclk_out[10],txoutclk_out[11],txoutclk_out[12],txoutclk_out[13],txoutclk_out[14],txoutclk_out[15]};                                      
    assign GT_RXCOMMADET          = {rxcommadet_out[0],rxcommadet_out[1],rxcommadet_out[2],rxcommadet_out[3],rxcommadet_out[4],rxcommadet_out[5],rxcommadet_out[6],rxcommadet_out[7],rxcommadet_out[8],rxcommadet_out[9],rxcommadet_out[10],rxcommadet_out[11],rxcommadet_out[12],rxcommadet_out[13],rxcommadet_out[14],rxcommadet_out[15]};   
    assign GT_GTPOWERGOOD         = {gtpowergood_out[0],gtpowergood_out[1],gtpowergood_out[2],gtpowergood_out[3],gtpowergood_out[4],gtpowergood_out[5],gtpowergood_out[6],gtpowergood_out[7],gtpowergood_out[8],gtpowergood_out[9],gtpowergood_out[10],gtpowergood_out[11],gtpowergood_out[12],gtpowergood_out[13],gtpowergood_out[14],gtpowergood_out[15]}         ;                                      
    assign GT_TXRESETDONE         = {txresetdone_out[0],txresetdone_out[1],txresetdone_out[2],txresetdone_out[3],txresetdone_out[4],txresetdone_out[5],txresetdone_out[6],txresetdone_out[7],txresetdone_out[8],txresetdone_out[9],txresetdone_out[10],txresetdone_out[11],txresetdone_out[12],txresetdone_out[13],txresetdone_out[14],txresetdone_out[15]}         ;                                      
    assign GT_RXRESETDONE         = {rxresetdone_out[0],rxresetdone_out[1],rxresetdone_out[2],rxresetdone_out[3],rxresetdone_out[4],rxresetdone_out[5],rxresetdone_out[6],rxresetdone_out[7],rxresetdone_out[8],rxresetdone_out[9],rxresetdone_out[10],rxresetdone_out[11],rxresetdone_out[12],rxresetdone_out[13],rxresetdone_out[14],rxresetdone_out[15]}         ;                                      
    assign GT_TXPHINITDONE        = {txphinitdone_out[0],txphinitdone_out[1],txphinitdone_out[2],txphinitdone_out[3],txphinitdone_out[4],txphinitdone_out[5],txphinitdone_out[6],txphinitdone_out[7],txphinitdone_out[8],txphinitdone_out[9],txphinitdone_out[10],txphinitdone_out[11],txphinitdone_out[12],txphinitdone_out[13],txphinitdone_out[14],txphinitdone_out[15]}        ;    
    assign GT_TXPHALIGNDONE       = {txphaligndone_out[0],txphaligndone_out[1],txphaligndone_out[2],txphaligndone_out[3],txphaligndone_out[4],txphaligndone_out[5],txphaligndone_out[6],txphaligndone_out[7],txphaligndone_out[8],txphaligndone_out[9],txphaligndone_out[10],txphaligndone_out[11],txphaligndone_out[12],txphaligndone_out[13],txphaligndone_out[14],txphaligndone_out[15]};
    assign GT_RXPMARESETDONE      = {rxpmaresetdone_out[0],rxpmaresetdone_out[1],rxpmaresetdone_out[2],rxpmaresetdone_out[3],rxpmaresetdone_out[4],rxpmaresetdone_out[5],rxpmaresetdone_out[6],rxpmaresetdone_out[7],rxpmaresetdone_out[8],rxpmaresetdone_out[9],rxpmaresetdone_out[10],rxpmaresetdone_out[11],rxpmaresetdone_out[12],rxpmaresetdone_out[13],rxpmaresetdone_out[14],rxpmaresetdone_out[15]}      ; 
    assign GT_TXPROGDIVRESETDONE  = {txprgdivresetdone_out[0],txprgdivresetdone_out[1],txprgdivresetdone_out[2],txprgdivresetdone_out[3],txprgdivresetdone_out[4],txprgdivresetdone_out[5],txprgdivresetdone_out[6],txprgdivresetdone_out[7],txprgdivresetdone_out[8],txprgdivresetdone_out[9],txprgdivresetdone_out[10],txprgdivresetdone_out[11],txprgdivresetdone_out[12],txprgdivresetdone_out[13],txprgdivresetdone_out[14],txprgdivresetdone_out[15]}   ;                                      

    assign GT_RXVALID             = {rxvalid_out[0],rxvalid_out[1],rxvalid_out[2],rxvalid_out[3],rxvalid_out[4],rxvalid_out[5],rxvalid_out[6],rxvalid_out[7],rxvalid_out[8],rxvalid_out[9],rxvalid_out[10],rxvalid_out[11],rxvalid_out[12],rxvalid_out[13],rxvalid_out[14],rxvalid_out[15]};
    assign GT_RXPRBSERR           = {rxprbserr_out[0],rxprbserr_out[1],rxprbserr_out[2],rxprbserr_out[3],rxprbserr_out[4],rxprbserr_out[5],rxprbserr_out[6],rxprbserr_out[7],rxprbserr_out[8],rxprbserr_out[9],rxprbserr_out[10],rxprbserr_out[11],rxprbserr_out[12],rxprbserr_out[13],rxprbserr_out[14],rxprbserr_out[15]};                                      
    assign GT_PHYSTATUS           = {phystatus_out[0],phystatus_out[1],phystatus_out[2],phystatus_out[3],phystatus_out[4],phystatus_out[5],phystatus_out[6],phystatus_out[7],phystatus_out[8],phystatus_out[9],phystatus_out[10],phystatus_out[11],phystatus_out[12],phystatus_out[13],phystatus_out[14],phystatus_out[15]};                                      
    assign GT_RXCDRLOCK           = {rxcdrlock_out[0],rxcdrlock_out[1],rxcdrlock_out[2],rxcdrlock_out[3],rxcdrlock_out[4],rxcdrlock_out[5],rxcdrlock_out[6],rxcdrlock_out[7],rxcdrlock_out[8],rxcdrlock_out[9],rxcdrlock_out[10],rxcdrlock_out[11],rxcdrlock_out[12],rxcdrlock_out[13],rxcdrlock_out[14],rxcdrlock_out[15]};                                                                                               
    assign pcierstidle_in         = {GT_PCIERSTIDLE[0],GT_PCIERSTIDLE[1],GT_PCIERSTIDLE[2],GT_PCIERSTIDLE[3],GT_PCIERSTIDLE[4],GT_PCIERSTIDLE[5],GT_PCIERSTIDLE[6],GT_PCIERSTIDLE[7],GT_PCIERSTIDLE[8],GT_PCIERSTIDLE[9],GT_PCIERSTIDLE[10],GT_PCIERSTIDLE[11],GT_PCIERSTIDLE[12],GT_PCIERSTIDLE[13],GT_PCIERSTIDLE[14],GT_PCIERSTIDLE[15]};
    assign GT_RXELECIDLE          = {rxelecidle_out[0],rxelecidle_out[1],rxelecidle_out[2],rxelecidle_out[3],rxelecidle_out[4],rxelecidle_out[5],rxelecidle_out[6],rxelecidle_out[7],rxelecidle_out[8],rxelecidle_out[9],rxelecidle_out[10],rxelecidle_out[11],rxelecidle_out[12],rxelecidle_out[13],rxelecidle_out[14],rxelecidle_out[15]};                                      
    assign GT_RXSYNCDONE          = {rxsyncdone_out[0],rxsyncdone_out[1],rxsyncdone_out[2],rxsyncdone_out[3],rxsyncdone_out[4],rxsyncdone_out[5],rxsyncdone_out[6],rxsyncdone_out[7],rxsyncdone_out[8],rxsyncdone_out[9],rxsyncdone_out[10],rxsyncdone_out[11],rxsyncdone_out[12],rxsyncdone_out[13],rxsyncdone_out[14],rxsyncdone_out[15]};           
    assign GT_PCIERATEIDLE        = {pcierateidle_out[0],pcierateidle_out[1],pcierateidle_out[2],pcierateidle_out[3],pcierateidle_out[4],pcierateidle_out[5],pcierateidle_out[6],pcierateidle_out[7],pcierateidle_out[8],pcierateidle_out[9],pcierateidle_out[10],pcierateidle_out[11],pcierateidle_out[12],pcierateidle_out[13],pcierateidle_out[14],pcierateidle_out[15]};                                      
    assign GT_RXPRBSLOCKED        = {rxprbslocked_out[0],rxprbslocked_out[1],rxprbslocked_out[2],rxprbslocked_out[3],rxprbslocked_out[4],rxprbslocked_out[5],rxprbslocked_out[6],rxprbslocked_out[7],rxprbslocked_out[8],rxprbslocked_out[9],rxprbslocked_out[10],rxprbslocked_out[11],rxprbslocked_out[12],rxprbslocked_out[13],rxprbslocked_out[14],rxprbslocked_out[15]};                                      
    assign GT_PCIERATEGEN3        = {pcierategen3_out[0],pcierategen3_out[1],pcierategen3_out[2],pcierategen3_out[3],pcierategen3_out[4],pcierategen3_out[5],pcierategen3_out[6],pcierategen3_out[7],pcierategen3_out[8],pcierategen3_out[9],pcierategen3_out[10],pcierategen3_out[11],pcierategen3_out[12],pcierategen3_out[13],pcierategen3_out[14],pcierategen3_out[15]};
    assign GT_RXPHALIGNDONE       = {rxphaligndone_out[0],rxphaligndone_out[1],rxphaligndone_out[2],rxphaligndone_out[3],rxphaligndone_out[4],rxphaligndone_out[5],rxphaligndone_out[6],rxphaligndone_out[7],rxphaligndone_out[8],rxphaligndone_out[9],rxphaligndone_out[10],rxphaligndone_out[11],rxphaligndone_out[12],rxphaligndone_out[13],rxphaligndone_out[14],rxphaligndone_out[15]};          
    assign txprbsforceerr_in      = {GT_TXPRBSFORCEERR[0],GT_TXPRBSFORCEERR[1],GT_TXPRBSFORCEERR[2],GT_TXPRBSFORCEERR[3],GT_TXPRBSFORCEERR[4],GT_TXPRBSFORCEERR[5],GT_TXPRBSFORCEERR[6],GT_TXPRBSFORCEERR[7],GT_TXPRBSFORCEERR[8],GT_TXPRBSFORCEERR[9],GT_TXPRBSFORCEERR[10],GT_TXPRBSFORCEERR[11],GT_TXPRBSFORCEERR[12],GT_TXPRBSFORCEERR[13],GT_TXPRBSFORCEERR[14],GT_TXPRBSFORCEERR[15]};
    assign txinhibit_in           = {GT_TXINHIBIT[0],GT_TXINHIBIT[1],GT_TXINHIBIT[2],GT_TXINHIBIT[3],GT_TXINHIBIT[4],GT_TXINHIBIT[5],GT_TXINHIBIT[6],GT_TXINHIBIT[7],GT_TXINHIBIT[8],GT_TXINHIBIT[9],GT_TXINHIBIT[10],GT_TXINHIBIT[11],GT_TXINHIBIT[12],GT_TXINHIBIT[13],GT_TXINHIBIT[14],GT_TXINHIBIT[15]};
    assign rxprbscntreset_in      = {GT_RXPRBSCNTRESET[0],GT_RXPRBSCNTRESET[1],GT_RXPRBSCNTRESET[2],GT_RXPRBSCNTRESET[3],GT_RXPRBSCNTRESET[4],GT_RXPRBSCNTRESET[5],GT_RXPRBSCNTRESET[6],GT_RXPRBSCNTRESET[7],GT_RXPRBSCNTRESET[8],GT_RXPRBSCNTRESET[9],GT_RXPRBSCNTRESET[10],GT_RXPRBSCNTRESET[11],GT_RXPRBSCNTRESET[12],GT_RXPRBSCNTRESET[13],GT_RXPRBSCNTRESET[14],GT_RXPRBSCNTRESET[15]};
    assign GT_TXDLYSRESETDONE     = {txdlysresetdone_out[0],txdlysresetdone_out[1],txdlysresetdone_out[2],txdlysresetdone_out[3],txdlysresetdone_out[4],txdlysresetdone_out[5],txdlysresetdone_out[6],txdlysresetdone_out[7],txdlysresetdone_out[8],txdlysresetdone_out[9],txdlysresetdone_out[10],txdlysresetdone_out[11],txdlysresetdone_out[12],txdlysresetdone_out[13],txdlysresetdone_out[14],txdlysresetdone_out[15]};  
    assign GT_RXDLYSRESETDONE     = {rxdlysresetdone_out[0],rxdlysresetdone_out[1],rxdlysresetdone_out[2],rxdlysresetdone_out[3],rxdlysresetdone_out[4],rxdlysresetdone_out[5],rxdlysresetdone_out[6],rxdlysresetdone_out[7],rxdlysresetdone_out[8],rxdlysresetdone_out[9],rxdlysresetdone_out[10],rxdlysresetdone_out[11],rxdlysresetdone_out[12],rxdlysresetdone_out[13],rxdlysresetdone_out[14],rxdlysresetdone_out[15]};  
    assign GT_PCIEUSERGEN3RDY     = {pcieusergen3rdy_out[0],pcieusergen3rdy_out[1],pcieusergen3rdy_out[2],pcieusergen3rdy_out[3],pcieusergen3rdy_out[4],pcieusergen3rdy_out[5],pcieusergen3rdy_out[6],pcieusergen3rdy_out[7],pcieusergen3rdy_out[8],pcieusergen3rdy_out[9],pcieusergen3rdy_out[10],pcieusergen3rdy_out[11],pcieusergen3rdy_out[12],pcieusergen3rdy_out[13],pcieusergen3rdy_out[14],pcieusergen3rdy_out[15]};                                      
    assign pcieuserratedone_in    = {GT_PCIEUSERRATEDONE[0],GT_PCIEUSERRATEDONE[1],GT_PCIEUSERRATEDONE[2],GT_PCIEUSERRATEDONE[3],GT_PCIEUSERRATEDONE[4],GT_PCIEUSERRATEDONE[5],GT_PCIEUSERRATEDONE[6],GT_PCIEUSERRATEDONE[7],GT_PCIEUSERRATEDONE[8],GT_PCIEUSERRATEDONE[9],GT_PCIEUSERRATEDONE[10],GT_PCIEUSERRATEDONE[11],GT_PCIEUSERRATEDONE[12],GT_PCIEUSERRATEDONE[13],GT_PCIEUSERRATEDONE[14],GT_PCIEUSERRATEDONE[15]};
    assign GT_PCIEUSERRATESTART   = {pcieuserratestart_out[0],pcieuserratestart_out[1],pcieuserratestart_out[2],pcieuserratestart_out[3],pcieuserratestart_out[4],pcieuserratestart_out[5],pcieuserratestart_out[6],pcieuserratestart_out[7],pcieuserratestart_out[8],pcieuserratestart_out[9],pcieuserratestart_out[10],pcieuserratestart_out[11],pcieuserratestart_out[12],pcieuserratestart_out[13],pcieuserratestart_out[14],pcieuserratestart_out[15]};                                      
    assign GT_EYESCANDATAERROR    = {eyescandataerror_out[0],eyescandataerror_out[1],eyescandataerror_out[2],eyescandataerror_out[3],eyescandataerror_out[4],eyescandataerror_out[5],eyescandataerror_out[6],eyescandataerror_out[7],eyescandataerror_out[8],eyescandataerror_out[9],eyescandataerror_out[10],eyescandataerror_out[11],eyescandataerror_out[12],eyescandataerror_out[13],eyescandataerror_out[14],eyescandataerror_out[15]};            
    assign pciersttxsyncstart_in  = {GT_PCIERSTTXSYNCSTART[0],GT_PCIERSTTXSYNCSTART[1],GT_PCIERSTTXSYNCSTART[2],GT_PCIERSTTXSYNCSTART[3],GT_PCIERSTTXSYNCSTART[4],GT_PCIERSTTXSYNCSTART[5],GT_PCIERSTTXSYNCSTART[6],GT_PCIERSTTXSYNCSTART[7],GT_PCIERSTTXSYNCSTART[8],GT_PCIERSTTXSYNCSTART[9],GT_PCIERSTTXSYNCSTART[10],GT_PCIERSTTXSYNCSTART[11],GT_PCIERSTTXSYNCSTART[12],GT_PCIERSTTXSYNCSTART[13],GT_PCIERSTTXSYNCSTART[14],GT_PCIERSTTXSYNCSTART[15]};
    assign GT_PCIESYNCTXSYNCDONE  = {pciesynctxsyncdone_out[0],pciesynctxsyncdone_out[1],pciesynctxsyncdone_out[2],pciesynctxsyncdone_out[3],pciesynctxsyncdone_out[4],pciesynctxsyncdone_out[5],pciesynctxsyncdone_out[6],pciesynctxsyncdone_out[7],pciesynctxsyncdone_out[8],pciesynctxsyncdone_out[9],pciesynctxsyncdone_out[10],pciesynctxsyncdone_out[11],pciesynctxsyncdone_out[12],pciesynctxsyncdone_out[13],pciesynctxsyncdone_out[14],pciesynctxsyncdone_out[15]};                                      
    assign pcieeqrxeqadaptdone_in = {GT_PCIEEQRXEQADAPTDONE[0],GT_PCIEEQRXEQADAPTDONE[1],GT_PCIEEQRXEQADAPTDONE[2],GT_PCIEEQRXEQADAPTDONE[3],GT_PCIEEQRXEQADAPTDONE[4],GT_PCIEEQRXEQADAPTDONE[5],GT_PCIEEQRXEQADAPTDONE[6],GT_PCIEEQRXEQADAPTDONE[7],GT_PCIEEQRXEQADAPTDONE[8],GT_PCIEEQRXEQADAPTDONE[9],GT_PCIEEQRXEQADAPTDONE[10],GT_PCIEEQRXEQADAPTDONE[11],GT_PCIEEQRXEQADAPTDONE[12],GT_PCIEEQRXEQADAPTDONE[13],GT_PCIEEQRXEQADAPTDONE[14],GT_PCIEEQRXEQADAPTDONE[15]};
    assign GT_PCIEUSERPHYSTATUSRST= {pcieuserphystatusrst_out[0],pcieuserphystatusrst_out[1],pcieuserphystatusrst_out[2],pcieuserphystatusrst_out[3],pcieuserphystatusrst_out[4],pcieuserphystatusrst_out[5],pcieuserphystatusrst_out[6],pcieuserphystatusrst_out[7],pcieuserphystatusrst_out[8],pcieuserphystatusrst_out[9],pcieuserphystatusrst_out[10],pcieuserphystatusrst_out[11],pcieuserphystatusrst_out[12],pcieuserphystatusrst_out[13],pcieuserphystatusrst_out[14],pcieuserphystatusrst_out[15]};                                      

    assign GT_BUFGTCE             = {bufgtce_out[0],bufgtce_out[1],bufgtce_out[2],bufgtce_out[3],bufgtce_out[4],bufgtce_out[5],bufgtce_out[6],bufgtce_out[7],bufgtce_out[8],bufgtce_out[9],bufgtce_out[10],bufgtce_out[11],bufgtce_out[12],bufgtce_out[13],bufgtce_out[14],bufgtce_out[15]};                                          
    assign loopback_in            = {GT_LOOPBACK[2:0],GT_LOOPBACK[5:3],GT_LOOPBACK[8:6],GT_LOOPBACK[11:9],GT_LOOPBACK[14:12],GT_LOOPBACK[17:15],GT_LOOPBACK[20:18],GT_LOOPBACK[23:21],GT_LOOPBACK[26:24],GT_LOOPBACK[29:27],GT_LOOPBACK[32:30],GT_LOOPBACK[35:33],GT_LOOPBACK[38:36],GT_LOOPBACK[41:39],GT_LOOPBACK[44:42],GT_LOOPBACK[47:45]};
    assign txmargin_in            = {GT_TXMARGIN[2:0],GT_TXMARGIN[5:3],GT_TXMARGIN[8:6],GT_TXMARGIN[11:9],GT_TXMARGIN[14:12],GT_TXMARGIN[17:15],GT_TXMARGIN[20:18],GT_TXMARGIN[23:21],GT_TXMARGIN[26:24],GT_TXMARGIN[29:27],GT_TXMARGIN[32:30],GT_TXMARGIN[35:33],GT_TXMARGIN[38:36],GT_TXMARGIN[41:39],GT_TXMARGIN[44:42],GT_TXMARGIN[47:45]};
    assign txoutclksel_in         = {GT_TXOUTCLKSEL[2:0],GT_TXOUTCLKSEL[5:3],GT_TXOUTCLKSEL[8:6],GT_TXOUTCLKSEL[11:9],GT_TXOUTCLKSEL[14:12],GT_TXOUTCLKSEL[17:15],GT_TXOUTCLKSEL[20:18],GT_TXOUTCLKSEL[23:21],GT_TXOUTCLKSEL[26:24],GT_TXOUTCLKSEL[29:27],GT_TXOUTCLKSEL[32:30],GT_TXOUTCLKSEL[35:33],GT_TXOUTCLKSEL[38:36],GT_TXOUTCLKSEL[41:39],GT_TXOUTCLKSEL[44:42],GT_TXOUTCLKSEL[47:45]};
    assign GT_RXSTATUS            = {rxstatus_out[2:0],rxstatus_out[5:3],rxstatus_out[8:6],rxstatus_out[11:9],rxstatus_out[14:12],rxstatus_out[17:15],rxstatus_out[20:18],rxstatus_out[23:21],rxstatus_out[26:24],rxstatus_out[29:27],rxstatus_out[32:30],rxstatus_out[35:33],rxstatus_out[38:36],rxstatus_out[41:39],rxstatus_out[44:42],rxstatus_out[47:45]};                                      
    assign GT_BUFGTRESET          = {bufgtreset_out[0],bufgtreset_out[1],bufgtreset_out[2],bufgtreset_out[3],bufgtreset_out[4],bufgtreset_out[5],bufgtreset_out[6],bufgtreset_out[7],bufgtreset_out[8],bufgtreset_out[9],bufgtreset_out[10],bufgtreset_out[11],bufgtreset_out[12],bufgtreset_out[13],bufgtreset_out[14],bufgtreset_out[15]};                                      
    assign GT_RXBUFSTATUS         = {rxbufstatus_out[2:0],rxbufstatus_out[5:3],rxbufstatus_out[8:6],rxbufstatus_out[11:9],rxbufstatus_out[14:12],rxbufstatus_out[17:15],rxbufstatus_out[20:18],rxbufstatus_out[23:21],rxbufstatus_out[26:24],rxbufstatus_out[29:27],rxbufstatus_out[32:30],rxbufstatus_out[35:33],rxbufstatus_out[38:36],rxbufstatus_out[41:39],rxbufstatus_out[44:42],rxbufstatus_out[47:45]};                                                    
    assign GT_BUFGTCEMASK         = {bufgtcemask_out[2:0],bufgtcemask_out[5:3],bufgtcemask_out[8:6],bufgtcemask_out[11:9],bufgtcemask_out[14:12],bufgtcemask_out[17:15],bufgtcemask_out[20:18],bufgtcemask_out[23:21],bufgtcemask_out[26:24],bufgtcemask_out[29:27],bufgtcemask_out[32:30],bufgtcemask_out[35:33],bufgtcemask_out[38:36],bufgtcemask_out[41:39],bufgtcemask_out[44:42],bufgtcemask_out[47:45]};                                      
    assign GT_BUFGTRSTMASK        = {bufgtrstmask_out[2:0],bufgtrstmask_out[5:3],bufgtrstmask_out[8:6],bufgtrstmask_out[11:9],bufgtrstmask_out[14:12],bufgtrstmask_out[17:15],bufgtrstmask_out[20:18],bufgtrstmask_out[23:21],bufgtrstmask_out[26:24],bufgtrstmask_out[29:27],bufgtrstmask_out[32:30],bufgtrstmask_out[35:33],bufgtrstmask_out[38:36],bufgtrstmask_out[41:39],bufgtrstmask_out[44:42],bufgtrstmask_out[47:45]};                                      

    assign rxpd_in                = {GT_POWERDOWN[1:0],GT_POWERDOWN[3:2],GT_POWERDOWN[5:4],GT_POWERDOWN[7:6],GT_POWERDOWN[9:8],GT_POWERDOWN[11:10],GT_POWERDOWN[13:12],GT_POWERDOWN[15:14],GT_POWERDOWN[17:16],GT_POWERDOWN[19:18],GT_POWERDOWN[21:20],GT_POWERDOWN[23:22],GT_POWERDOWN[25:24],GT_POWERDOWN[27:26],GT_POWERDOWN[29:28],GT_POWERDOWN[31:30]};
    assign txpd_in                = {GT_POWERDOWN[1:0],GT_POWERDOWN[3:2],GT_POWERDOWN[5:4],GT_POWERDOWN[7:6],GT_POWERDOWN[9:8],GT_POWERDOWN[11:10],GT_POWERDOWN[13:12],GT_POWERDOWN[15:14],GT_POWERDOWN[17:16],GT_POWERDOWN[19:18],GT_POWERDOWN[21:20],GT_POWERDOWN[23:22],GT_POWERDOWN[25:24],GT_POWERDOWN[27:26],GT_POWERDOWN[29:28],GT_POWERDOWN[31:30]};

    assign rxprbssel_in           = {GT_PRBSSEL[3:0],GT_PRBSSEL[7:4],GT_PRBSSEL[11:8],GT_PRBSSEL[15:12],GT_PRBSSEL[19:16],GT_PRBSSEL[23:20],GT_PRBSSEL[27:24],GT_PRBSSEL[31:28],GT_PRBSSEL[35:32],GT_PRBSSEL[39:36],GT_PRBSSEL[43:40],GT_PRBSSEL[47:44],GT_PRBSSEL[51:48],GT_PRBSSEL[55:52],GT_PRBSSEL[59:56],GT_PRBSSEL[63:60]};
    assign txprbssel_in           = {GT_PRBSSEL[3:0],GT_PRBSSEL[7:4],GT_PRBSSEL[11:8],GT_PRBSSEL[15:12],GT_PRBSSEL[19:16],GT_PRBSSEL[23:20],GT_PRBSSEL[27:24],GT_PRBSSEL[31:28],GT_PRBSSEL[35:32],GT_PRBSSEL[39:36],GT_PRBSSEL[43:40],GT_PRBSSEL[47:44],GT_PRBSSEL[51:48],GT_PRBSSEL[55:52],GT_PRBSSEL[59:56],GT_PRBSSEL[63:60]};
    assign txprecursor_in         = {GT_TXPRECURSOR[4:0],GT_TXPRECURSOR[9:5],GT_TXPRECURSOR[14:10],GT_TXPRECURSOR[19:15],GT_TXPRECURSOR[24:20],GT_TXPRECURSOR[29:25],GT_TXPRECURSOR[34:30],GT_TXPRECURSOR[39:35],GT_TXPRECURSOR[44:40],GT_TXPRECURSOR[49:45],GT_TXPRECURSOR[54:50],GT_TXPRECURSOR[59:55],GT_TXPRECURSOR[64:60],GT_TXPRECURSOR[69:65],GT_TXPRECURSOR[74:70],GT_TXPRECURSOR[79:75]};
    assign txpostcursor_in        = {GT_TXPOSTCURSOR[4:0],GT_TXPOSTCURSOR[9:5],GT_TXPOSTCURSOR[14:10],GT_TXPOSTCURSOR[19:15],GT_TXPOSTCURSOR[24:20],GT_TXPOSTCURSOR[29:25],GT_TXPOSTCURSOR[34:30],GT_TXPOSTCURSOR[39:35],GT_TXPOSTCURSOR[44:40],GT_TXPOSTCURSOR[49:45],GT_TXPOSTCURSOR[54:50],GT_TXPOSTCURSOR[59:55],GT_TXPOSTCURSOR[64:60],GT_TXPOSTCURSOR[69:65],GT_TXPOSTCURSOR[74:70],GT_TXPOSTCURSOR[79:75]};
    assign txmaincursor_in        = {GT_TXMAINCURSOR[6:0],GT_TXMAINCURSOR[13:7],GT_TXMAINCURSOR[20:14],GT_TXMAINCURSOR[27:21],GT_TXMAINCURSOR[34:28],GT_TXMAINCURSOR[41:35],GT_TXMAINCURSOR[48:42],GT_TXMAINCURSOR[55:49],GT_TXMAINCURSOR[62:56],GT_TXMAINCURSOR[69:63],GT_TXMAINCURSOR[76:70],GT_TXMAINCURSOR[83:77],GT_TXMAINCURSOR[90:84],GT_TXMAINCURSOR[97:91],GT_TXMAINCURSOR[104:98],GT_TXMAINCURSOR[111:105]};

    assign GT_BUFGTDIV            = {bufgtdiv_out[8:0],bufgtdiv_out[17:9],bufgtdiv_out[26:18],bufgtdiv_out[35:27],bufgtdiv_out[44:36],bufgtdiv_out[53:45],bufgtdiv_out[62:54],bufgtdiv_out[71:63],bufgtdiv_out[80:72],bufgtdiv_out[89:81],bufgtdiv_out[98:90],bufgtdiv_out[107:99],bufgtdiv_out[116:108],bufgtdiv_out[125:117],bufgtdiv_out[134:126],bufgtdiv_out[143:135]};                                      

    assign GT_CPLLLOCK          = {cplllock_out[0],cplllock_out[1],cplllock_out[2],cplllock_out[3],cplllock_out[4],cplllock_out[5],cplllock_out[6],cplllock_out[7],cplllock_out[8],cplllock_out[9],cplllock_out[10],cplllock_out[11],cplllock_out[12],cplllock_out[13],cplllock_out[14],cplllock_out[15]};
    assign GT_PCIERATEQPLLPD    = {pcierateqpllpd_out[1:0],pcierateqpllpd_out[3:2],pcierateqpllpd_out[5:4],pcierateqpllpd_out[7:6],pcierateqpllpd_out[9:8],pcierateqpllpd_out[11:10],pcierateqpllpd_out[13:12],pcierateqpllpd_out[15:14],pcierateqpllpd_out[17:16],pcierateqpllpd_out[19:18],pcierateqpllpd_out[21:20],pcierateqpllpd_out[23:22],pcierateqpllpd_out[25:24],pcierateqpllpd_out[27:26],pcierateqpllpd_out[29:28],pcierateqpllpd_out[31:30]};              
    assign GT_PCIERATEQPLLRESET = {pcierateqpllreset_out[1:0],pcierateqpllreset_out[3:2],pcierateqpllreset_out[5:4],pcierateqpllreset_out[7:6],pcierateqpllreset_out[9:8],pcierateqpllreset_out[11:10],pcierateqpllreset_out[13:12],pcierateqpllreset_out[15:14],pcierateqpllreset_out[17:16],pcierateqpllreset_out[19:18],pcierateqpllreset_out[21:20],pcierateqpllreset_out[23:22],pcierateqpllreset_out[25:24],pcierateqpllreset_out[27:26],pcierateqpllreset_out[29:28],pcierateqpllreset_out[31:30]};    
//--------------------------------------------------------------------------------------------------       
//  Generate PHY Lane - Begin                                                                              
//--------------------------------------------------------------------------------------------------           
genvar i;                                                                                                      
                                                                                                               
generate for (i=0; i<PHY_LANE; i=i+1)                                                      
                                                                                                    
    begin : gtwizard_lane                                 
    
    //--------------------------------------------------------------------------
    //  Input Port Remapping                                                          
    //--------------------------------------------------------------------------                               
                                                                             
    assign txctrl0_in[(16*i)+1:(16*i)]        = 2'd0;                                      
    assign txctrl0_in[(16*i)+2]               = GT_TXDATA_VALID[((PHY_LANE-1)-i)];                                                                       
    assign txctrl0_in[(16*i)+3]               = GT_TXSTART_BLOCK[((PHY_LANE-1)-i)];                          
    assign txctrl0_in[(16*i)+ 5:(16*i)+ 4]    = GT_TXSYNC_HEADER[(2*((PHY_LANE-1)-i))+1:(2*((PHY_LANE-1)-i))];          
    assign txctrl0_in[(16*i)+15:(16*i)+ 6]    = 10'd0;                                         
                                                                                          
    assign txctrl1_in[(16*i)]                 = GT_TXCOMPLIANCE[((PHY_LANE-1)-i)];                            
    assign txctrl1_in[(16*i)+15:(16*i)+ 1]    = 15'd0;                                         
                                           
    assign txctrl2_in[(8*i)+1:(8*i)]          = GT_TXDATAK[(2*((PHY_LANE-1)-i))+1:(2*((PHY_LANE-1)-i))];
    assign txctrl2_in[(8*i)+7:(8*i)+2]        = 6'd0;
    
    assign txdata_in[(128*i)+63:(128*i)]      = GT_TXDATA[(64*((PHY_LANE-1)-i))+63:(64*((PHY_LANE-1)-i))];                                        
    assign txdata_in[(128*i)+127:(128*i)+64]  = 64'd0;                                         
   
    assign rate[(3*i)+1:(3*i)]             = GT_RATE[(2*((PHY_LANE-1)-i))+1:(2*((PHY_LANE-1)-i))];
    assign rate[(3*i)+2]                   = 1'd0;

    //--------------------------------------------------------------------------
    //  GT Wizard Outputs
    //--------------------------------------------------------------------------       
    assign GT_RXDATA[(64*i)+63:(64*i)]     = rxdata_out[(128*((PHY_LANE-1)-i))+63:(128*((PHY_LANE-1)-i))];  
    assign GT_RXDATAK[(2*i)+1:(2*i)]       = rxctrl0_out[(16*((PHY_LANE-1)-i))+1:(16*((PHY_LANE-1)-i))];
    assign GT_RXDATA_VALID[i]              = rxctrl0_out[(16*((PHY_LANE-1)-i))+2];
    assign GT_RXSTART_BLOCK[(2*i)+1:(2*i)] = {rxctrl0_out[(16*((PHY_LANE-1)-i))+6],rxctrl0_out[(16*((PHY_LANE-1)-i))+3]};
    assign GT_RXSYNC_HEADER[(2*i)+1:(2*i)] = rxctrl0_out[(16*((PHY_LANE-1)-i))+5:(16*((PHY_LANE-1)-i))+4];
    assign GT_GEN34_EIOS_DET[i]            = rxctrl0_out[(16*((PHY_LANE-1)-i))+7];
    
    //----------------------------------------------------------------------------------------------
    //  PHY Quad - Generate one Quad for every four Lanes
    //----------------------------------------------------------------------------------------------
    if ((i%4)==0) 
                       
        begin : gtwizard_quad   
            
        //----------------------------------------------------------------------
        //  Generate QPLL Powerdown and Reset
        //----------------------------------------------------------------------
        //  * QPLL reset and powerdown for Quad 1 driven by       Master Lane 0
        //  * QPLL reset and powerdown for Quad 2 driven by Local Master Lane 4
        //----------------------------------------------------------------------        
        assign qpll1pd_in[i>>2]    = (PHY_MAX_SPEED != 3) ? 1'd1 : (i > 3) ? (GTCOM_QPLLPD    || pcierateqpllpd_out[(((PHY_LANE-1)-i)*2)+1]) :
                                                                             (GTCOM_QPLLPD    || pcierateqpllpd_out[1]);
                                             
        assign qpll1reset_in[i>>2] = (PHY_MAX_SPEED != 3) ? 1'd1 : (i > 3) ? (GTCOM_QPLLRESET || pcierateqpllreset_out[(((PHY_LANE-1)-i)*2)+1]) :
                                                                             (GTCOM_QPLLRESET || pcierateqpllreset_out[1]);   
        
        assign qpll0pd_in[i>>2]    = (PHY_MAX_SPEED != 4) ? 1'd1 : (i > 3) ? (GTCOM_QPLLPD    || pcierateqpllpd_out[(((PHY_LANE-1)-i)*2)+0]) :
                                                                             (GTCOM_QPLLPD    || pcierateqpllpd_out[0]);  
                                                         
        assign qpll0reset_in[i>>2] = (PHY_MAX_SPEED != 4) ? 1'd1 : (i > 3) ? (GTCOM_QPLLRESET || pcierateqpllreset_out[(((PHY_LANE-1)-i)*2)+0]) : 
                                                                             (GTCOM_QPLLRESET || pcierateqpllreset_out[0]);                                                                  
        
        
        end   
        
    end
endgenerate

//---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    assign GTCOM_QPLL0LOCK      = qpll0lock_out;
    assign GTCOM_QPLL0OUTCLK    = qpll0outclk_out;
    assign GTCOM_QPLL0OUTREFCLK = qpll0outrefclk_out;
    assign GTCOM_QPLL1LOCK      = qpll1lock_out;
    assign GTCOM_QPLL1OUTCLK    = qpll1outclk_out;
    assign GTCOM_QPLL1OUTREFCLK = qpll1outrefclk_out;

genvar k;                                                                                                      
                                                                                                               
generate for (k=0; k<PHY_LANE; k=k+1)                                                      
                                                                                                    
   begin : new_sigs
                                 
   assign GT_TXOUTCLKFABRIC[k] = txoutclkfabric_out[((PHY_LANE-1)-k)]; 
   assign GT_RXOUTCLKFABRIC[k] = rxoutclkfabric_out[((PHY_LANE-1)-k)]; 
   assign GT_TXOUTCLKPCS[k]    = txoutclkpcs_out[((PHY_LANE-1)-k)]; 
   assign GT_RXOUTCLKPCS[k]    = rxoutclkpcs_out[((PHY_LANE-1)-k)];  
   assign GT_RXRECCLKOUT[k]    = rxrecclkout_out[((PHY_LANE-1)-k)];  
   assign GT_TXPMARESETDONE[k] = txpmaresetdone_out[((PHY_LANE-1)-k)];   
   assign GT_RXRATEDONE[k]     = rxratedone_out[((PHY_LANE-1)-k)];
   assign GT_RXOUTCLK[k]       = rxoutclk_out[((PHY_LANE-1)-k)];
   end
endgenerate

   assign rxdfeagchold_in = rxcdrhold_in;  
   assign rxdfecfokhold_in = rxcdrhold_in; 
   assign rxdfelfhold_in = rxcdrhold_in;   
   assign rxdfekhhold_in = rxcdrhold_in;             
   assign rxdfetap2hold_in = rxcdrhold_in;        
   assign rxdfetap3hold_in = rxcdrhold_in;        
   assign rxdfetap4hold_in = rxcdrhold_in;       
   assign rxdfetap5hold_in = rxcdrhold_in;           
   assign rxdfetap6hold_in = rxcdrhold_in;       
   assign rxdfetap7hold_in = rxcdrhold_in;        
   assign rxdfetap8hold_in = rxcdrhold_in;       
   assign rxdfetap9hold_in = rxcdrhold_in;       
   assign rxdfetap10hold_in = rxcdrhold_in;       
   assign rxdfetap11hold_in = rxcdrhold_in;       
   assign rxdfetap12hold_in = rxcdrhold_in;        
   assign rxdfetap13hold_in = rxcdrhold_in;       
   assign rxdfetap14hold_in = rxcdrhold_in;       
   assign rxdfetap15hold_in = rxcdrhold_in;       
   assign rxdfeuthold_in = rxcdrhold_in;             
   assign rxdfevphold_in = rxcdrhold_in;             
   assign rxoshold_in = rxcdrhold_in;                  
   assign rxlpmgchold_in = rxcdrhold_in;              
   assign rxlpmhfhold_in = rxcdrhold_in;            
   assign rxlpmlfhold_in = rxcdrhold_in;              
   assign rxlpmoshold_in = rxcdrhold_in;  
 
endmodule

