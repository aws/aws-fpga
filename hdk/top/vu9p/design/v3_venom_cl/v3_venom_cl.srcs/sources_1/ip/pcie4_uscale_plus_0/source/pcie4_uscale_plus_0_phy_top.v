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
// File       : pcie4_uscale_plus_0_phy_top.v
// Version    : 1.1 
//-----------------------------------------------------------------------------
/*****************************************************************************
** Description:
**    PCIe Gen4 PHY supports:
**       - Gen1: per-lane 16b @ 125MHz
**       - Gen2: per-lane 16b @ 250MHz
**       - Gen3: per-lane 32b @ 250Mhz
**       - Gen4: per-lane 64b @ 250MHz
**
******************************************************************************/
//--------------------------------------------------------------------------------------------------
//  Design :  PHY Wrapper
//  Module :  PHY Wrapper
//--------------------------------------------------------------------------------------------------

`timescale 1ps/1ps

`define AS_PHYREG(clk, reset, q, d, rstval)  \
   always @(posedge clk or posedge reset) begin \
      if (reset) \
         q  <= #(TCQ)   rstval;  \
      else  \
         q  <= #(TCQ)   d; \
   end

`define PHYREG(clk, reset, q, d, rstval)  \
   always @(posedge clk) begin \
      if (reset) \
         q  <= #(TCQ)   rstval;  \
      else  \
         q  <= #(TCQ)   d; \
   end

`define AS_FAST2SLOW(bit_width, rst_val, mod_name, fast_input, fast_clk, enable_input, mask_input, slow_reset, fast_reset, slow_clk, slow_output1, slow_output2)   \
   pcie4_uscale_plus_0_gen4_fast2slow #(.WIDTH(bit_width), .ASYNC("TRUE"), .RST_1(rst_val), .TCQ(TCQ)) mod_name (.fast_bits(fast_input),  \
                                                                                             .fast_clk_i(fast_clk),   \
                                                                                             .enable_i(enable_input), \
                                                                                             .mask_bits(mask_input),  \
                                                                                             .mgmt_reset_fast_i(fast_reset),  \
                                                                                             .mgmt_reset_slow_i(slow_reset),  \
                                                                                             .slow_clk_i(slow_clk),   \
                                                                                             .slow_bits_ns(slow_output1),   \
                                                                                             .slow_bits_r(slow_output2));

`define FAST2SLOW(bit_width, rst_val, mod_name, fast_input, fast_clk, enable_input, mask_input, slow_reset, fast_reset, slow_clk, slow_output1, slow_output2)   \
   pcie4_uscale_plus_0_gen4_fast2slow #(.WIDTH(bit_width), .ASYNC("FALSE"), .RST_1(rst_val), .TCQ(TCQ)) mod_name (.fast_bits(fast_input),  \
                                                                                              .fast_clk_i(fast_clk),   \
                                                                                              .enable_i(enable_input), \
                                                                                              .mask_bits(mask_input),  \
                                                                                              .mgmt_reset_fast_i(fast_reset),  \
                                                                                              .mgmt_reset_slow_i(slow_reset),  \
                                                                                              .slow_clk_i(slow_clk),   \
                                                                                              .slow_bits_ns(slow_output1),   \
                                                                                              .slow_bits_r(slow_output2));


(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie4_uscale_plus_0_phy_top #(
   // Parameters
   parameter         FPGA_FAMILY       = "US",     // "US" = UltraScale; "USM" = Diablo
   parameter         FPGA_XCVR         = "H",      // "H" = GTH; "Y" = GTY; "Y64" = GTY-64b
   parameter integer PIPELINE_STAGES   = 0,        // 0 = no pipeline; 1 = 1 stage; 2 = 2 stages; 3 = 3 stages
   parameter         PHY_SIM_EN        = "FALSE",  // "FALSE" = Normal; "TRUE"  = Simulation
   parameter integer PHY_LANE          = 1,        // Valid settings: 1, 2, 4, 8, 16(only for Gen1/2/3)
   parameter integer PHY_MAX_SPEED     = 3,        // 1 = Gen1 Capable; 2 = Gen2 Capable; 3 = Gen3 Capable; 4 = Gen4 Capable   
   parameter         PHY_ASYNC_EN      = "FALSE",  // "FALSE" = Sync Clocking; "TRUE"  = Async Clocking
   parameter         PHY_REFCLK_FREQ   = 0,        // 0 = 100 MHz; 1 = 125 MHz; 2 = 250 MHz
   parameter integer PHY_CORECLK_FREQ  = 2,        // 1 = 250 MHz; 2 = 500 MHz
   parameter integer PHY_USERCLK_FREQ  = 3,        // 1 = 62.5 MHz; 2 = 125 MHz; 3 = 250 MHz; 4 = 500 MHz
   parameter integer PHY_MCAPCLK_FREQ  = 2,        // 1 = 62.5 MHz; 2 = 125 MHz
   parameter integer PHY_GT_TXPRESET   = 0,        // Valid settings: 0 to 10
   parameter integer PHY_LP_TXPRESET   = 5         // Valid settings: 5
)  (                                                         


   // Clock & Reset
   input  wire                         PHY_REFCLK,          
   input  wire                         PHY_GTREFCLK,     
   input  wire                         PHY_RST_N,           
   
   output wire                         PHY_CORECLK, 
   output wire                         PHY_USERCLK,                          
   output wire                         PHY_MCAPCLK,                          
   output wire                         PHY_PCLK,  
   //--------------------------------------------------------------------------   
   //  IBERT ports 
   //--------------------------------------------------------------------------                   
   input [(PHY_LANE * 5) -1:0]         ibert_txprecursor_in, 
   input [(PHY_LANE * 5) -1:0]         ibert_txpostcursor_in, 
   input [PHY_LANE-1:0]                ibert_eyescanreset_in, 
   input [(PHY_LANE * 5) -1:0]         ibert_txdiffctrl_in, 
   input [PHY_LANE-1:0]                ibert_rxlpmen_in, 

   output        [(PHY_LANE*5)-1:0]    txeq_precursor_o, 
   output        [(PHY_LANE*5)-1:0]    txeq_postcursor_o, 
   output        [PHY_LANE-1:0]        gt_pcierategen3_o,  
   //--------------------------------------------------------------------------                   
   // GT Channel DRP Port
   //--------------------------------------------------------------------------                   
   output                              gt_drpclk, 
   input        [(PHY_LANE*10)-1:0]    gt_drpaddr,
   input        [PHY_LANE-1:0]         gt_drpen,
   input        [PHY_LANE-1:0]         gt_drpwe,
   input        [(PHY_LANE*16)-1:0]    gt_drpdi,

   output        [PHY_LANE-1:0]        gt_drprdy,
   output        [(PHY_LANE*16)-1:0]   gt_drpdo,  
   //--------------------------------------------------------------------------                   
   // GT Common DRP Port
   //--------------------------------------------------------------------------                   
   input       [((((PHY_LANE-1)>>2)+1)*16)-1:0] gtcom_drpaddr,                                          
   input       [   (PHY_LANE-1)>>2          :0] gtcom_drpen,                                                
   input       [   (PHY_LANE-1)>>2          :0] gtcom_drpwe,        
   input       [((((PHY_LANE-1)>>2)+1)*16)-1:0] gtcom_drpdi,                                         
                                                                        
   output      [   (PHY_LANE-1)>>2          :0] gtcom_drprdy,       
   output      [((((PHY_LANE-1)>>2)+1)*16)-1:0] gtcom_drpdo,          
   //--------------------------------------------------------------------------                   
   // TX Data 
   //--------------------------------------------------------------------------                   
   input  wire [(PHY_LANE*64)-1:0]     PHY_TXDATA,            
   input  wire [(PHY_LANE* 2)-1:0]     PHY_TXDATAK,    
   input  wire [PHY_LANE-1:0]          PHY_TXDATA_VALID,
   input  wire [PHY_LANE-1:0]          PHY_TXSTART_BLOCK,      
   input  wire [(PHY_LANE* 2)-1:0]     PHY_TXSYNC_HEADER,                    

   output wire [PHY_LANE-1:0]          PHY_TXP,    // Serial Line      
   output wire [PHY_LANE-1:0]          PHY_TXN,    // Serial Line  
   //--------------------------------------------------------------------------                   
   // RX Data
   //--------------------------------------------------------------------------                   
   input  wire [PHY_LANE-1:0]          PHY_RXP,    // Serial Line           
   input  wire [PHY_LANE-1:0]          PHY_RXN,    // Serial Line

   output wire [(PHY_LANE*64)-1:0]     PHY_RXDATA,            
   output wire [(PHY_LANE* 2)-1:0]     PHY_RXDATAK,       
   output wire [PHY_LANE-1:0]          PHY_RXDATA_VALID,         
   output wire [(PHY_LANE* 2)-1:0]     PHY_RXSTART_BLOCK,        
   output wire [(PHY_LANE* 2)-1:0]     PHY_RXSYNC_HEADER,        
   //--------------------------------------------------------------------------                   
   // PHY Command
   //--------------------------------------------------------------------------                   
   input  wire                         PHY_TXDETECTRX,        
   input  wire [PHY_LANE-1:0]          PHY_TXELECIDLE,        
   input  wire [PHY_LANE-1:0]          PHY_TXCOMPLIANCE,      
   input  wire [PHY_LANE-1:0]          PHY_RXPOLARITY,        
   input  wire [1:0]                   PHY_POWERDOWN,         
   input  wire [1:0]                   PHY_RATE,              
   //--------------------------------------------------------------------------                   
   // PHY Status
   //--------------------------------------------------------------------------                   
   output wire [PHY_LANE-1:0]          PHY_RXVALID,               
   output wire [PHY_LANE-1:0]          PHY_PHYSTATUS,          
   output wire                         PHY_PHYSTATUS_RST,         
   output wire [PHY_LANE-1:0]          PHY_RXELECIDLE,                       
   output wire [(PHY_LANE*3)-1:0]      PHY_RXSTATUS,                       
   //--------------------------------------------------------------------------                   
   // TX Driver
   //--------------------------------------------------------------------------                   
   input  wire [ 2:0]                  PHY_TXMARGIN,          
   input  wire                         PHY_TXSWING,           
   input  wire                         PHY_TXDEEMPH,    
   //--------------------------------------------------------------------------                   
   // TX Equalization (Gen3/4)
   //--------------------------------------------------------------------------                   
   input  wire [(PHY_LANE*2)-1:0]      PHY_TXEQ_CTRL,      
   input  wire [(PHY_LANE*4)-1:0]      PHY_TXEQ_PRESET,       
   input  wire [(PHY_LANE*6)-1:0]      PHY_TXEQ_COEFF,                                                            

   output wire [ 5:0]                  PHY_TXEQ_FS,           
   output wire [ 5:0]                  PHY_TXEQ_LF,           
   output wire [(PHY_LANE*18)-1:0]     PHY_TXEQ_NEW_COEFF,        
   output wire [PHY_LANE-1:0]          PHY_TXEQ_DONE,         
   //--------------------------------------------------------------------------                   
   // RX Equalization (Gen3/4)
   //--------------------------------------------------------------------------                   
   input  wire [(PHY_LANE*2)-1:0]      PHY_RXEQ_CTRL,     
   input  wire [(PHY_LANE*4)-1:0]      PHY_RXEQ_TXPRESET,      

   output wire [PHY_LANE-1:0]          PHY_RXEQ_PRESET_SEL,    
   output wire [(PHY_LANE*18)-1:0]     PHY_RXEQ_NEW_TXCOEFF,   
   output wire [PHY_LANE-1:0]          PHY_RXEQ_ADAPT_DONE,     
   output wire [PHY_LANE-1:0]          PHY_RXEQ_DONE,
    //--------------------------------------------------------------------------
    //  Transceiver Debug And Status Ports
    //--------------------------------------------------------------------------
    input       [PHY_LANE-1:0]          GT_PCIEUSERRATEDONE,
    input       [(PHY_LANE*3)-1:0]      GT_LOOPBACK        ,             
    input       [PHY_LANE-1:0]          GT_TXPRBSFORCEERR  ,            
    input       [PHY_LANE-1:0]          GT_TXINHIBIT       ,            
    input       [PHY_LANE*4-1:0]        GT_TXPRBSSEL       ,            
    input       [PHY_LANE*4-1:0]        GT_RXPRBSSEL       ,          
    input       [PHY_LANE-1:0]          GT_RXPRBSCNTRESET  ,             

    output      [PHY_LANE-1:0]          GT_TXELECIDLE      ,             
    output      [PHY_LANE-1:0]          GT_TXRESETDONE     ,    
    output      [PHY_LANE-1:0]          GT_RXRESETDONE     ,        
    output      [PHY_LANE-1:0]          GT_RXPMARESETDONE  ,      
    output      [PHY_LANE-1:0]          GT_TXPHALIGNDONE   ,            
    output      [PHY_LANE-1:0]          GT_TXPHINITDONE    ,         
    output      [PHY_LANE-1:0]          GT_TXDLYSRESETDONE ,         
    output      [PHY_LANE-1:0]          GT_RXPHALIGNDONE   ,        
    output      [PHY_LANE-1:0]          GT_RXDLYSRESETDONE ,          
    output      [PHY_LANE-1:0]          GT_RXSYNCDONE      ,        
    output      [PHY_LANE-1:0]          GT_EYESCANDATAERROR,               
    output      [PHY_LANE-1:0]          GT_RXPRBSERR       ,           
    output      [PHY_LANE-1:0]          GT_RXCOMMADET      ,                   
    output      [PHY_LANE-1:0]          GT_PHYSTATUS       ,                   
    output      [PHY_LANE-1:0]          GT_RXVALID         ,              
    output      [PHY_LANE-1:0]          GT_RXCDRLOCK, 
    output      [PHY_LANE-1:0]          GT_PCIERATEIDLE,
    output      [PHY_LANE-1:0]          GT_PCIEUSERRATESTART,
    output      [PHY_LANE-1:0]          GT_GTPOWERGOOD,  
    output      [PHY_LANE-1:0]          GT_CPLLLOCK,          
    output      [PHY_LANE-1:0]          GT_RXOUTCLK, 
    output      [PHY_LANE-1:0]          GT_RXRECCLKOUT, 
    
    input       [PHY_LANE-1:0]          GT_DMONFIFORESET,
    input       [PHY_LANE-1:0]          GT_DMONITORCLK,
    output      [(PHY_LANE*16)-1:0]     GT_DMONITOROUT,           
    output      [(PHY_LANE-1)>>2:0]     GT_QPLL1LOCK,               
    output      [(PHY_LANE-1)>>2:0]     GT_QPLL0LOCK,               
    output      [(PHY_LANE*3)-1:0]      GT_RXSTATUS,            
    output      [(PHY_LANE*3)-1:0]      GT_RXBUFSTATUS,            
    output      [8:0]                   GT_BUFGTDIV,                 
    output      [(PHY_LANE*2)-1:0]      TXEQ_CTRL,                  
    output      [(PHY_LANE*4)-1:0]      TXEQ_PRESET,                   
    output      [3:0]                   PHY_RST_FSM,                 
    output      [(PHY_LANE*3)-1:0]      PHY_TXEQ_FSM,                  
    output      [(PHY_LANE*3)-1:0]      PHY_RXEQ_FSM,                 
    output                              PHY_RST_IDLE,                 
    output                              PHY_RRST_N,
    output                              PHY_PRST_N,

    output      [PHY_LANE-1:0]          GT_GEN34_EIOS_DET,    
    output      [PHY_LANE-1:0]          GT_TXOUTCLK,          
    output      [PHY_LANE-1:0]          GT_TXOUTCLKFABRIC,    
    output      [PHY_LANE-1:0]          GT_RXOUTCLKFABRIC,    
    output      [PHY_LANE-1:0]          GT_TXOUTCLKPCS,       
    output      [PHY_LANE-1:0]          GT_RXOUTCLKPCS,       
    input       [PHY_LANE-1:0]          GT_TXPMARESET,        
    input       [PHY_LANE-1:0]          GT_RXPMARESET,        
    input       [PHY_LANE-1:0]          GT_TXPCSRESET,        
    input       [PHY_LANE-1:0]          GT_RXPCSRESET,        
    input       [PHY_LANE-1:0]          GT_RXBUFRESET,        
    input       [PHY_LANE-1:0]          GT_RXCDRRESET,        
    input       [PHY_LANE-1:0]          GT_RXDFELPMRESET,     
    output      [PHY_LANE-1:0]          GT_TXPROGDIVRESETDONE,
    output      [PHY_LANE-1:0]          GT_TXPMARESETDONE,    
    output      [PHY_LANE-1:0]          GT_TXSYNCDONE,        
    output      [PHY_LANE-1:0]          GT_RXPRBSLOCKED,      
   //--------------------------------------------------------------------------                   
   // Assist Signals
   //--------------------------------------------------------------------------                   
   input  wire                         AS_MAC_IN_DETECT,
   input  wire                         AS_CDR_HOLD_REQ
   );

   localparam  TCQ   = 1;

   wire                 phy_userclk_int;
   wire                 phy_mcapclk_int;
   wire                 phy_pclk;
   wire                 phy_pclk2;
   wire  [PHY_LANE-1:0]          phy_rxvalid_pclk2;
   wire  [PHY_LANE-1:0]          phy_phystatus_pclk2;
   wire                 phy_phystatus_rst_pclk2;
   wire  [(PHY_LANE* 3)-1:0]     phy_rxstatus_pclk2;
   wire  [5:0]          phy_txeq_fs_pclk2;
   wire  [5:0]          phy_txeq_lf_pclk2;
   wire  [(PHY_LANE* 18)-1:0]    phy_txeq_new_coeff_pclk2;
   wire  [PHY_LANE-1:0]          phy_txeq_done_pclk2;
   wire  [PHY_LANE-1:0]          phy_rxeq_preset_sel_pclk2;
   wire  [(PHY_LANE* 18)-1:0]    phy_rxeq_new_txcoeff_pclk2;
   wire  [PHY_LANE-1:0]          phy_rxeq_done_pclk2;
   wire  [PHY_LANE-1:0]          phy_rxeq_adapt_done_pclk2;

   wire                 phy_txdetectrx_32b;
   wire  [PHY_LANE-1:0]          phy_txelecidle_32b;
   wire  [PHY_LANE-1:0]          phy_txcompliance_32b;
   wire  [PHY_LANE-1:0]          phy_rxpolarity_32b;
   wire  [1:0]          phy_powerdown_32b;
   wire  [1:0]          phy_rate_32b;

   wire  [(PHY_LANE*32)-1:0]     phy_txdata_32b;            
   wire  [(PHY_LANE* 2)-1:0]     phy_txdatak_32b;            
   wire  [PHY_LANE-1:0]          phy_txdata_valid_32b;
   wire  [PHY_LANE-1:0]          phy_txstart_block_32b;      
   wire  [(PHY_LANE* 2)-1:0]     phy_txsync_header_32b;  
   wire  [(PHY_LANE*2)-1:0]      phy_txeq_ctrl_pclk2;            
   wire  [(PHY_LANE*4)-1:0]      phy_txeq_preset_pclk2;            
   wire  [(PHY_LANE*6)-1:0]      phy_txeq_coeff_pclk2;

   wire  [(PHY_LANE*64)-1:0]     phy_txdata_64b;            

   wire  [(PHY_LANE*32)-1:0]     phy_rxdata_32b;            
   wire  [(PHY_LANE* 2)-1:0]     phy_rxdatak_32b;            
   wire  [PHY_LANE-1:0]          phy_rxdata_valid_32b;
   wire  [PHY_LANE-1:0]          phy_rxstart_block_32b;      
   wire  [(PHY_LANE* 2)-1:0]     phy_rxsync_header_32b; 

   wire  [(PHY_LANE*64)-1:0]     phy_rxdata_64b;            
   wire  [(PHY_LANE* 2)-1:0]     phy_rxstart_block_64b;      

   wire  [(PHY_LANE*64)-1:0]     phy_txdata_pl;            
   wire  [(PHY_LANE* 2)-1:0]     phy_txdatak_pl;            
   wire  [PHY_LANE-1:0]          phy_txdata_valid_pl;
   wire  [PHY_LANE-1:0]          phy_txstart_block_pl;      
   wire  [(PHY_LANE* 2)-1:0]     phy_txsync_header_pl;  

   wire  [(PHY_LANE*64)-1:0]     phy_rxdata_pl;            
   wire  [(PHY_LANE* 2)-1:0]     phy_rxdatak_pl;            
   wire  [PHY_LANE-1:0]          phy_rxdata_valid_pl;
   wire  [(PHY_LANE* 2)-1:0]     phy_rxstart_block_pl;      
   wire  [(PHY_LANE* 2)-1:0]     phy_rxsync_header_pl; 

   wire                 phy_txdetectrx_pl;        
   wire  [PHY_LANE-1:0]          phy_txelecidle_pl;        
   wire  [PHY_LANE-1:0]          phy_txcompliance_pl;      
   wire  [PHY_LANE-1:0]          phy_rxpolarity_pl;        
   wire  [1:0]          phy_powerdown_pl;         
   wire  [1:0]          phy_rate_pl;   

   wire  [PHY_LANE-1:0]          phy_rxvalid_pl;               
   wire  [PHY_LANE-1:0]          phy_phystatus_pl;          
   wire  [PHY_LANE-1:0]          phy_rxelecidle_pl;         
   wire  [(PHY_LANE*3)-1:0]      phy_rxstatus_pl;          

   wire  [ 2:0]         phy_txmargin_pl;          
   wire                 phy_txswing_pl;           
   wire                 phy_txdeemph_pl;  

   wire  [(PHY_LANE*2)-1:0]      phy_txeq_ctrl_pl;      
   wire  [(PHY_LANE*4)-1:0]      phy_txeq_preset_pl;       
   wire  [(PHY_LANE*6)-1:0]      phy_txeq_coeff_pl;                                                            

   wire  [ 5:0]         phy_txeq_fs_pl;           
   wire  [ 5:0]         phy_txeq_lf_pl;           
   wire  [(PHY_LANE*18)-1:0]     phy_txeq_new_coeff_pl;        
   wire  [PHY_LANE-1:0]          phy_txeq_done_pl;         

   wire  [(PHY_LANE*2)-1:0]      phy_rxeq_ctrl_pl;     
   wire  [(PHY_LANE*4)-1:0]      phy_rxeq_txpreset_pl;      

   wire  [PHY_LANE-1:0]          phy_rxeq_preset_sel_pl;    
   wire  [(PHY_LANE*18)-1:0]     phy_rxeq_new_txcoeff_pl;   
   wire  [PHY_LANE-1:0]          phy_rxeq_adapt_done_pl;     
   wire  [PHY_LANE-1:0]          phy_rxeq_done_pl;

   wire                 as_mac_in_detect_pl;
   wire                 as_cdr_hold_req_pl;

   wire  [PHY_LANE-1:0]          com_det_lower;
   wire  [PHY_LANE-1:0]          com_det_upper;
   wire  [PHY_LANE-1:0]          idl_det_lower;
   wire  [PHY_LANE-1:0]          idl_det_upper;
   wire  [PHY_LANE-1:0]          eios_det_c0;
   wire  [PHY_LANE-1:0]          eios_det_c1;
   wire  [PHY_LANE-1:0]          eios_det_c2;
   wire  [PHY_LANE-1:0]          eios_det_c3;
   wire  [(PHY_LANE* 3)-1:0]     phy_rxstatus_raw;

   reg                  phy_rxelecidle_ff;
   reg                  phy_rxelecidle_ff2;
   reg                  phy_rxcdrhold_wire;
   reg                  phy_rxcdrhold_pclk2;

   reg   [PHY_LANE-1:0]          phy_rxstatus_mask_wire, phy_rxstatus_mask;
   reg   [PHY_LANE-1:0]          saved_com_det_lower_wire, saved_com_det_lower;
   reg   [PHY_LANE-1:0]          saved_com_det_upper_wire, saved_com_det_upper;
   reg   [PHY_LANE-1:0]          start_mask_mon_wire;
   reg   [PHY_LANE-1:0]          start_mask_mon;

   //--------------------------------------------------------------------------
   //  Pipeline Stages
   //--------------------------------------------------------------------------        
   //(* keep = "true", max_fanout = 500 *) wire   phy_phystatus_rst_int;
   (* max_fanout = 500 *) wire   phy_phystatus_rst_int;
   assign phy_phystatus_rst_int  = PHY_PHYSTATUS_RST;

      // Programmable stages to ease GT lane routing
      pcie4_uscale_plus_0_phy_pipeline #(
         //  Parameters
         .PIPELINE_STAGES  ( PIPELINE_STAGES ),
         .PHY_LANE         ( PHY_LANE ),
         .TCQ              ( TCQ )
      ) phy_pipeline (                                         
         // Clock & Reset Ports
         .phy_pclk               ( PHY_PCLK ),  
         .phy_rst                ( phy_phystatus_rst_int ),  

         // TX Data
         .phy_txdata_i           ( PHY_TXDATA ),
         .phy_txdatak_i          ( PHY_TXDATAK ),
         .phy_txdata_valid_i     ( PHY_TXDATA_VALID ),
         .phy_txstart_block_i    ( PHY_TXSTART_BLOCK ),
         .phy_txsync_header_i    ( PHY_TXSYNC_HEADER ),

         .phy_txdata_o           ( phy_txdata_pl ),
         .phy_txdatak_o          ( phy_txdatak_pl ),
         .phy_txdata_valid_o     ( phy_txdata_valid_pl ),
         .phy_txstart_block_o    ( phy_txstart_block_pl ),
         .phy_txsync_header_o    ( phy_txsync_header_pl ),

         // RX Data
         .phy_rxdata_i           ( phy_rxdata_pl ),            
         .phy_rxdatak_i          ( phy_rxdatak_pl ),       
         .phy_rxdata_valid_i     ( phy_rxdata_valid_pl ),         
         .phy_rxstart_block_i    ( phy_rxstart_block_pl ),        
         .phy_rxsync_header_i    ( phy_rxsync_header_pl ),   

         .phy_rxdata_o           ( PHY_RXDATA ),            
         .phy_rxdatak_o          ( PHY_RXDATAK ),       
         .phy_rxdata_valid_o     ( PHY_RXDATA_VALID ),         
         .phy_rxstart_block_o    ( PHY_RXSTART_BLOCK ),        
         .phy_rxsync_header_o    ( PHY_RXSYNC_HEADER ),   

         //  PHY Command
         .phy_txdetectrx_i       ( PHY_TXDETECTRX ),  
         .phy_txelecidle_i       ( PHY_TXELECIDLE ),                    
         .phy_txcompliance_i     ( PHY_TXCOMPLIANCE ), 
         .phy_rxpolarity_i       ( PHY_RXPOLARITY ),
         .phy_powerdown_i        ( PHY_POWERDOWN ), 
         .phy_rate_i             ( PHY_RATE ),

         .phy_txdetectrx_o       ( phy_txdetectrx_pl ),  
         .phy_txelecidle_o       ( phy_txelecidle_pl ),                    
         .phy_txcompliance_o     ( phy_txcompliance_pl ), 
         .phy_rxpolarity_o       ( phy_rxpolarity_pl ),
         .phy_powerdown_o        ( phy_powerdown_pl ), 
         .phy_rate_o             ( phy_rate_pl ),    

         //  PHY Status
         .phy_rxvalid_i          ( phy_rxvalid_pl ),
         .phy_phystatus_i        ( phy_phystatus_pl ),
         .phy_rxelecidle_i       ( phy_rxelecidle_pl ), 
         .phy_rxstatus_i         ( phy_rxstatus_pl ),

         .phy_rxvalid_o          ( PHY_RXVALID ),
         .phy_phystatus_o        ( PHY_PHYSTATUS ),
         .phy_rxelecidle_o       ( PHY_RXELECIDLE ), 
         .phy_rxstatus_o         ( PHY_RXSTATUS ),
        
         //  TX Driver
         .phy_txmargin_i         ( PHY_TXMARGIN ),          
         .phy_txswing_i          ( PHY_TXSWING ),           
         .phy_txdeemph_i         ( PHY_TXDEEMPH ),   

         .phy_txmargin_o         ( phy_txmargin_pl ),          
         .phy_txswing_o          ( phy_txswing_pl ),           
         .phy_txdeemph_o         ( phy_txdeemph_pl ),        

         //  TX Equalization (Gen3/4)
         .phy_txeq_ctrl_i        ( PHY_TXEQ_CTRL ),
         .phy_txeq_preset_i      ( PHY_TXEQ_PRESET ),
         .phy_txeq_coeff_i       ( PHY_TXEQ_COEFF ), 

         .phy_txeq_ctrl_o        ( phy_txeq_ctrl_pl ),
         .phy_txeq_preset_o      ( phy_txeq_preset_pl ),
         .phy_txeq_coeff_o       ( phy_txeq_coeff_pl ), 

         .phy_txeq_fs_i          ( phy_txeq_fs_pl ),           
         .phy_txeq_lf_i          ( phy_txeq_lf_pl ),           
         .phy_txeq_new_coeff_i   ( phy_txeq_new_coeff_pl ),
         .phy_txeq_done_i        ( phy_txeq_done_pl ),

         .phy_txeq_fs_o          ( PHY_TXEQ_FS ),           
         .phy_txeq_lf_o          ( PHY_TXEQ_LF ),           
         .phy_txeq_new_coeff_o   ( PHY_TXEQ_NEW_COEFF ),
         .phy_txeq_done_o        ( PHY_TXEQ_DONE ),   

         //  RX Equalization (Gen3/4)
         .phy_rxeq_ctrl_i        ( PHY_RXEQ_CTRL ), 
         .phy_rxeq_txpreset_i    ( PHY_RXEQ_TXPRESET ),

         .phy_rxeq_ctrl_o        ( phy_rxeq_ctrl_pl ), 
         .phy_rxeq_txpreset_o    ( phy_rxeq_txpreset_pl ),

         .phy_rxeq_preset_sel_i  ( phy_rxeq_preset_sel_pl ),
         .phy_rxeq_new_txcoeff_i ( phy_rxeq_new_txcoeff_pl ),
         .phy_rxeq_adapt_done_i  ( phy_rxeq_adapt_done_pl ),
         .phy_rxeq_done_i        ( phy_rxeq_done_pl ),

         .phy_rxeq_preset_sel_o  ( PHY_RXEQ_PRESET_SEL ),
         .phy_rxeq_new_txcoeff_o ( PHY_RXEQ_NEW_TXCOEFF ),
         .phy_rxeq_adapt_done_o  ( PHY_RXEQ_ADAPT_DONE ),
         .phy_rxeq_done_o        ( PHY_RXEQ_DONE ),

         // Assist Signals
         .as_mac_in_detect_i     ( AS_MAC_IN_DETECT ),
         .as_cdr_hold_req_i      ( AS_CDR_HOLD_REQ ),

         .as_mac_in_detect_o     ( as_mac_in_detect_pl ),
         .as_cdr_hold_req_o      ( as_cdr_hold_req_pl )
      );


         assign phy_txdetectrx_32b     = phy_txdetectrx_pl;
         assign phy_txelecidle_32b     = phy_txelecidle_pl;
         assign phy_txcompliance_32b   = phy_txcompliance_pl;
         assign phy_rxpolarity_32b     = phy_rxpolarity_pl;
         assign phy_powerdown_32b      = phy_powerdown_pl;
         assign phy_rate_32b           = phy_rate_pl;
         assign phy_txdata_64b         = phy_txdata_pl;
         assign phy_txdatak_32b        = phy_txdatak_pl;
         assign phy_txdata_valid_32b   = phy_txdata_valid_pl;
         assign phy_txstart_block_32b  = phy_txstart_block_pl;
         assign phy_txsync_header_32b  = phy_txsync_header_pl;
         assign phy_txeq_ctrl_pclk2    = phy_txeq_ctrl_pl;
         assign phy_txeq_preset_pclk2  = phy_txeq_preset_pl;
         assign phy_txeq_coeff_pclk2   = phy_txeq_coeff_pl;
         assign PHY_PCLK               = phy_pclk2;
         assign phy_rxdata_pl          = phy_rxdata_64b;          // 64b
         assign phy_rxdatak_pl         = phy_rxdatak_32b;
         assign phy_rxdata_valid_pl    = phy_rxdata_valid_32b;
         assign phy_rxstart_block_pl   = phy_rxstart_block_64b;   // 2b
         assign phy_rxsync_header_pl   = phy_rxsync_header_32b;
         assign phy_rxvalid_pl         = phy_rxvalid_pclk2;
         assign phy_phystatus_pl       = phy_phystatus_pclk2;
         assign PHY_PHYSTATUS_RST      = phy_phystatus_rst_pclk2;
         assign phy_rxstatus_raw       = phy_rxstatus_pclk2;
         assign phy_txeq_fs_pl         = phy_txeq_fs_pclk2;
         assign phy_txeq_lf_pl         = phy_txeq_lf_pclk2;
         assign phy_txeq_new_coeff_pl  = phy_txeq_new_coeff_pclk2;
         assign phy_txeq_done_pl       = phy_txeq_done_pclk2;
         assign phy_rxeq_preset_sel_pl = phy_rxeq_preset_sel_pclk2;
         assign phy_rxeq_new_txcoeff_pl= phy_rxeq_new_txcoeff_pclk2;
         assign phy_rxeq_done_pl       = phy_rxeq_done_pclk2;
         assign phy_rxeq_adapt_done_pl = phy_rxeq_adapt_done_pclk2;

 
   //--------------------------------------------------------------------------
   //  CDRHOLD Logic
   //--------------------------------------------------------------------------  

   `PHYREG(phy_pclk2, phy_phystatus_rst_pclk2, phy_rxelecidle_ff, phy_rxelecidle_pl[0], 'd1)
   `PHYREG(phy_pclk2, phy_phystatus_rst_pclk2, phy_rxelecidle_ff2, phy_rxelecidle_ff, 'd1)

   always @(*) begin 
      if (as_cdr_hold_req_pl & phy_rxelecidle_pl[0]) begin
         phy_rxcdrhold_wire   = 1'b1;
      end else if (phy_rxelecidle_ff2 & ~phy_rxelecidle_pl[0]) begin
         phy_rxcdrhold_wire   = 1'b0;
      end else begin
         phy_rxcdrhold_wire   = phy_rxcdrhold_pclk2;
      end
   end

   `PHYREG(phy_pclk2, phy_phystatus_rst_pclk2, phy_rxcdrhold_pclk2, phy_rxcdrhold_wire, 'd0)

   //--------------------------------------------------------------------------
   // Mask invalid RXSTATUS for Gen1/2 after EIOS, can be removed once GT fixes it
   //--------------------------------------------------------------------------

   assign phy_rxstatus_pl = phy_rxstatus_raw;


   //--------------------------------------------------------------------------
   //  UltraScale GTH PHY Wrapper
   //--------------------------------------------------------------------------   

   wire [((((PHY_LANE-1)>>2)+1)*16)-1:0]  gtcom_drpaddr_tie_off   = 'd0;
   wire [(PHY_LANE-1)>>2:0]               gtcom_drpen_tie_off     = 'd0;
   wire [(PHY_LANE-1)>>2:0]               gtcom_drpwe_tie_off     = 'd0;
   wire [((((PHY_LANE-1)>>2)+1)*16)-1:0]  gtcom_drpdi_tie_off     = 'd0;

   assign PHY_USERCLK   = ((PHY_USERCLK_FREQ == 3 && PHY_CORECLK_FREQ == 1) ||
                           (PHY_USERCLK_FREQ == 4 && PHY_CORECLK_FREQ == 2))  ? PHY_CORECLK : phy_userclk_int;

   assign PHY_MCAPCLK   = ((PHY_MCAPCLK_FREQ == 1 && PHY_USERCLK_FREQ == 1) ||
                           (PHY_MCAPCLK_FREQ == 2 && PHY_USERCLK_FREQ == 2))  ? phy_userclk_int : phy_mcapclk_int;

   generate
      if (FPGA_FAMILY == "USM") begin: diablo_gt
         pcie4_uscale_plus_0_gt_phy_wrapper #(
            // Parameters
            .PHY_SIM_EN       ( PHY_SIM_EN ),     
            .PHY_GT_XCVR      ( (FPGA_XCVR == "Y")? "GTY": "GTH" ),
            .PHY_REFCLK_MODE  ( (PHY_ASYNC_EN == "FALSE")? 0: 1 ),
            .PHY_LANE         ( PHY_LANE ),   
            .PHY_MAX_SPEED    ( PHY_MAX_SPEED ),                    
            .PHY_REFCLK_FREQ  ( PHY_REFCLK_FREQ ),           
            .PHY_CORECLK_FREQ ( PHY_CORECLK_FREQ ),       
            .PHY_USERCLK_FREQ ( PHY_USERCLK_FREQ ),   
            .PHY_MCAPCLK_FREQ ( PHY_MCAPCLK_FREQ ),
            .PHY_GT_TXPRESET  ( PHY_GT_TXPRESET ),
            .PHY_LP_TXPRESET  ( PHY_LP_TXPRESET )
         ) diablo_gt_phy_wrapper (                                         


            // Clock & Reset Ports
            .PHY_REFCLK             ( PHY_REFCLK ),      
            .PHY_GTREFCLK           ( PHY_GTREFCLK ),               
            .PHY_RST_N              ( PHY_RST_N ),  
      
            .PHY_PCLK               ( phy_pclk2 ),  
            .PHY_PCLK2              ( phy_pclk ),  
            .PHY_CORECLK            ( PHY_CORECLK ), 
            .PHY_USERCLK            ( phy_userclk_int ),                          
            .PHY_MCAPCLK            ( phy_mcapclk_int ), // New in Diablo
                                                     
            // Serial Line Ports
            .PHY_RXP                ( PHY_RXP ),               
            .PHY_RXN                ( PHY_RXN ),               
                               
            .PHY_TXP                ( PHY_TXP ),               
            .PHY_TXN                ( PHY_TXN ),   
                                                                             
            // TX Data Ports 
            .PHY_TXDATA             ( phy_txdata_64b ),            
            .PHY_TXDATAK            ( phy_txdatak_32b ),                
            .PHY_TXDATA_VALID       ( phy_txdata_valid_32b ),                
            .PHY_TXSTART_BLOCK      ( phy_txstart_block_32b ),                      
            .PHY_TXSYNC_HEADER      ( phy_txsync_header_32b ),                                          
      
            // RX Data Ports 
            .PHY_RXDATA             ( phy_rxdata_64b ),            
            .PHY_RXDATAK            ( phy_rxdatak_32b ),                
            .PHY_RXDATA_VALID       ( phy_rxdata_valid_32b ),                
            .PHY_RXSTART_BLOCK      ( phy_rxstart_block_64b ),                      
            .PHY_RXSYNC_HEADER      ( phy_rxsync_header_32b ),                                          
      
            // PHY Command Port
            .PHY_TXDETECTRX         ( phy_txdetectrx_32b ),
            .PHY_TXELECIDLE         ( phy_txelecidle_32b ),                    
            .PHY_TXCOMPLIANCE       ( phy_txcompliance_32b ),                          
            .PHY_RXPOLARITY         ( phy_rxpolarity_32b ),            
            .PHY_POWERDOWN          ( phy_powerdown_32b ),
            .PHY_RATE               ( phy_rate_32b ),  
            .PHY_RXCDRHOLD          ( phy_rxcdrhold_pclk2 ),
          
            // PHY Status Ports
            .PHY_RXVALID            ( phy_rxvalid_pclk2 ),            
            .PHY_PHYSTATUS          ( phy_phystatus_pclk2 ),            
      
            .PHY_PHYSTATUS_RST      ( phy_phystatus_rst_pclk2 ),
            .PHY_RXELECIDLE         ( phy_rxelecidle_pl ),                    
            .PHY_RXSTATUS           ( phy_rxstatus_pclk2 ),                                            
          
            // TX Driver Ports
            .PHY_TXMARGIN           ( phy_txmargin_pl ),          
            .PHY_TXSWING            ( phy_txswing_pl ),   
            .PHY_TXDEEMPH           ( {1'b0, phy_txdeemph_pl} ),  // 2b in Diablo   
      
            // TX Equalization Ports for Gen3
            .PHY_TXEQ_CTRL          ( phy_txeq_ctrl_pclk2 ),
            .PHY_TXEQ_PRESET        ( phy_txeq_preset_pclk2 ),
            .PHY_TXEQ_COEFF         ( phy_txeq_coeff_pclk2 ),
      
            .PHY_TXEQ_FS            ( phy_txeq_fs_pclk2 ),           
            .PHY_TXEQ_LF            ( phy_txeq_lf_pclk2 ),           
            .PHY_TXEQ_NEW_COEFF     ( phy_txeq_new_coeff_pclk2 ),
            .PHY_TXEQ_DONE          ( phy_txeq_done_pclk2 ),
                                                                       
            // RX Equalization Ports for Gen3
            .PHY_RXEQ_CTRL          ( phy_rxeq_ctrl_pl ), 
            .PHY_RXEQ_PRESET        ( {PHY_LANE{3'b0}} ), 
            .PHY_RXEQ_LFFS          ( {PHY_LANE{6'b0}} ),         
            .PHY_RXEQ_TXPRESET      ( phy_rxeq_txpreset_pl ),
      
            .PHY_RXEQ_LFFS_SEL      ( phy_rxeq_preset_sel_pclk2 ),      
            .PHY_RXEQ_NEW_TXCOEFF   ( phy_rxeq_new_txcoeff_pclk2 ),   
            .PHY_RXEQ_DONE          ( phy_rxeq_done_pclk2 ),        
            .PHY_RXEQ_ADAPT_DONE    ( phy_rxeq_adapt_done_pclk2 ),
      
            // USB Ports
            .USB_TXONESZEROS        ( {PHY_LANE{1'b0}} ),   // New in Diablo
            .USB_RXEQTRAINING       ( {PHY_LANE{1'b0}} ),   // New in Diablo
            .USB_RXTERMINATION      ( {PHY_LANE{1'b0}} ),   // New in Diablo
            .USB_POWERPRESENT       ( ),  // New in Diablo
      
            //--------------------------------------------------------------------------   
            //  IBERT ports 
            //--------------------------------------------------------------------------                   
            .ibert_txprecursor_in   (ibert_txprecursor_in), 
            .ibert_txpostcursor_in  (ibert_txpostcursor_in), 
            .ibert_eyescanreset_in  (ibert_eyescanreset_in), 
            .ibert_txdiffctrl_in    (ibert_txdiffctrl_in), 
            .ibert_rxlpmen_in       (ibert_rxlpmen_in), 

            .txeq_precursor         (txeq_precursor_o), 
            .txeq_postcursor        (txeq_postcursor_o), 
            .gt_pcierategen3        (gt_pcierategen3_o),  
            //--------------------------------------------------------------------------                   
            // GT Channel DRP Port
            //--------------------------------------------------------------------------                   
            .GT_DRPCLK              ( gt_drpclk ),
            .GT_DRPADDR             ( gt_drpaddr ), 
            .GT_DRPEN               ( gt_drpen ), 
            .GT_DRPWE               ( gt_drpwe ),
            .GT_DRPDI               ( gt_drpdi ),  
                               
            .GT_DRPRDY              ( gt_drprdy ),  
            .GT_DRPDO               ( gt_drpdo ), 
            //--------------------- -----------------------------------------------------                   
            // GT Common DRP Port
            //--------------------------------------------------------------------------                   
            .GTCOM_DRPADDR          ( gtcom_drpaddr ), 
            .GTCOM_DRPEN            ( gtcom_drpen ), 
            .GTCOM_DRPWE            ( gtcom_drpwe ),
            .GTCOM_DRPDI            ( gtcom_drpdi ),  
                                  
            .GTCOM_DRPRDY           ( gtcom_drprdy ),  
            .GTCOM_DRPDO            ( gtcom_drpdo ), 
            //--------------------------------------------------------------------------                   

            // Debug Ports   // Not used
            .DBG_RATE_DONE          ( GT_PCIEUSERRATEDONE ),
            .GT_LOOPBACK            ( GT_LOOPBACK ),   // New in Diablo
            .DBG_PRBSSEL            ( GT_TXPRBSSEL ),   // New in Diablo
            .DBG_TXPRBSFORCEERR     ( GT_TXPRBSFORCEERR ),   // New in Diablo
            .DBG_RXPRBSCNTRESET     ( GT_RXPRBSCNTRESET ),   // New in Diablo
            .DBG_RXPRBSERR          ( GT_RXPRBSERR ),  // New in Diablo
            .DBG_RATE_IDLE          ( GT_PCIERATEIDLE ),  // New in Diablo
            .DBG_RATE_START         ( GT_PCIEUSERRATESTART ),  // New in Diablo
            .DBG_RXCDRLOCK          ( GT_RXCDRLOCK ),  // New in Diablo
            .DBG_RXOUTCLK           ( GT_RXOUTCLK ),  // New in Diablo
            .DBG_RST_IDLE           ( PHY_RST_IDLE ),  // New in Diablo
            .DBG_RRST_N             ( PHY_RRST_N ),  // New in Diablo
            .DBG_PRST_N             ( PHY_PRST_N ),  // New in Diablo
            .DBG_TXRESETDONE        ( GT_TXRESETDONE ),  // New in Diablo
            .DBG_RXRESETDONE        ( GT_RXRESETDONE ),  // New in Diablo
            .DBG_CPLLLOCK           ( GT_CPLLLOCK ),  // New in Diablo
            .DBG_QPLL0LOCK          ( GT_QPLL0LOCK ),  // New in Diablo
            .DBG_QPLL1LOCK          ( GT_QPLL1LOCK ),  // New in Diablo
            .GT_RXSYNCDONE          ( GT_RXSYNCDONE ),
            .GT_EYESCANDATAERROR    ( GT_EYESCANDATAERROR ),
            .GT_TXINHIBIT           ( GT_TXINHIBIT ),
            .DBG_RXPMARESETDONE     ( GT_RXPMARESETDONE ),  // New in Diablo
            .GT_RXPHALIGNDONE       ( GT_RXPHALIGNDONE ), 
            .GT_TXPHALIGNDONE       ( GT_TXPHALIGNDONE ), 
            .GT_TXPHINITDONE        ( GT_TXPHINITDONE ),
            .GT_RXDLYSRESETDONE     ( GT_RXDLYSRESETDONE ),    
            .GT_TXDLYSRESETDONE     ( GT_TXDLYSRESETDONE ),    
            .GT_RXCOMMADET          ( GT_RXCOMMADET ),
            .GT_RXBUFSTATUS         ( GT_RXBUFSTATUS ),
            .DBG_GTPOWERGOOD        ( GT_GTPOWERGOOD ),  // New in Diablo
            .DBG_RXRECCLKOUT        ( GT_RXRECCLKOUT ),  // New in Diablo
            .GT_DMONITOROUT         ( GT_DMONITOROUT ),
            .GT_DMONFIFORESET       ( GT_DMONFIFORESET ),
            .GT_DMONITORCLK         ( GT_DMONITORCLK ),
            .GT_BUFGTDIV            ( GT_BUFGTDIV ),
            .PHY_RST_FSM            ( PHY_RST_FSM ),
            .PHY_TXEQ_FSM           ( PHY_TXEQ_FSM ),
            .PHY_RXEQ_FSM           ( PHY_RXEQ_FSM ),


            .DBG_GEN34_EIOS_DET     ( GT_GEN34_EIOS_DET    ),  // New in Diablo
            .DBG_TXOUTCLK           ( GT_TXOUTCLK          ),  // New in Diablo
            .DBG_TXOUTCLKFABRIC     ( GT_TXOUTCLKFABRIC    ),  // New in Diablo
            .DBG_RXOUTCLKFABRIC     ( GT_RXOUTCLKFABRIC    ),  // New in Diablo
            .DBG_TXOUTCLKPCS        ( GT_TXOUTCLKPCS       ),  // New in Diablo
            .DBG_RXOUTCLKPCS        ( GT_RXOUTCLKPCS       ),  // New in Diablo
            .DBG_TXPMARESET         ( GT_TXPMARESET        ),  //{PHY_LANE{1'b0}} ),   // New in Diablo
            .DBG_RXPMARESET         ( GT_RXPMARESET        ),  //{PHY_LANE{1'b0}} ),   // New in Diablo
            .DBG_TXPCSRESET         ( GT_TXPCSRESET        ),  //{PHY_LANE{1'b0}} ),   // New in Diablo
            .DBG_RXPCSRESET         ( GT_RXPCSRESET        ),  //{PHY_LANE{1'b0}} ),   // New in Diablo
            .DBG_RXBUFRESET         ( GT_RXBUFRESET        ),  //{PHY_LANE{1'b0}} ),   // New in Diablo
            .DBG_RXCDRRESET         ( GT_RXCDRRESET        ),  //{PHY_LANE{1'b0}} ),   // New in Diablo
            .DBG_RXDFELPMRESET      ( GT_RXDFELPMRESET     ),  //{PHY_LANE{1'b0}} ),   // New in Diablo
            .DBG_TXPROGDIVRESETDONE ( GT_TXPROGDIVRESETDONE),  // New in Diablo
            .DBG_TXPMARESETDONE     ( GT_TXPMARESETDONE    ),  // New in Diablo
            .DBG_TXSYNCDONE         ( GT_TXSYNCDONE        ),  // New in Diablo
      
            // PRBS Debug Ports
            .DBG_RXPRBSLOCKED       ( GT_RXPRBSLOCKED ),  // New in Diablo
            .PHY_PCIE_MAC_IN_DETECT ( as_mac_in_detect_pl ) // New in Diablo
         );
      end 
   endgenerate

 assign GT_TXELECIDLE = phy_txelecidle_32b;
 assign GT_RXVALID = phy_rxvalid_pclk2;
 assign GT_PHYSTATUS = phy_phystatus_pclk2;
 assign GT_RXSTATUS = phy_rxstatus_pclk2;
 assign TXEQ_CTRL = phy_txeq_ctrl_pclk2;
 assign TXEQ_PRESET = phy_txeq_preset_pclk2;


endmodule

