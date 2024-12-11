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
// File       : pcie_bridge_rc_pcie4c_ip_gen4_perlane_64b_bridge.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
/*****************************************************************************
** Description:
**    Covert Gen4 Data I/F between
**       - 32b at PCLK2 (500MHz)
**       - 64b at PCLK  (250MHz)
**
******************************************************************************/

`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_rc_pcie4c_ip_gen4_perlane_64b_bridge #(
   // Parameters
   parameter integer PHY_LANE = 1,  // Valid settings: 1, 2, 4, 8, 16(only for Gen1/2/3)
   parameter integer TCQ      = 1
)  (                                                         
   // Clock & Reset Ports
   input  wire                         phy_pclk,  
   input  wire                         phy_pclk2,  
   input  wire                         phy_rst,           
   input  wire                         phy_rst2,           

   // Enable Ports
   input  wire                         bridge_enable,

   // 64b TX Data Ports
   input  wire [PHY_LANE-1:0]          phy_txelecidle_64b,
   input  wire [(PHY_LANE*64)-1:0]     phy_txdata_64b,            
   input  wire [(PHY_LANE* 2)-1:0]     phy_txdatak_64b,            
   input  wire [PHY_LANE-1:0]          phy_txdata_valid_64b,
   input  wire [PHY_LANE-1:0]          phy_txstart_block_64b,      
   input  wire [(PHY_LANE* 2)-1:0]     phy_txsync_header_64b,                    

   // 64b RX Data Ports
   output wire [(PHY_LANE*64)-1:0]     phy_rxdata_64b,            
   output wire [(PHY_LANE* 2)-1:0]     phy_rxdatak_64b,            
   output wire [PHY_LANE-1:0]          phy_rxdata_valid_64b,         
   output wire [(PHY_LANE* 2)-1:0]     phy_rxstart_block_64b,        
   output wire [(PHY_LANE* 2)-1:0]     phy_rxsync_header_64b,

   // 32b TX Data Ports
   output wire [PHY_LANE-1:0]          phy_txelecidle_32b,
   output wire [(PHY_LANE*32)-1:0]     phy_txdata_32b,            
   output wire [(PHY_LANE* 2)-1:0]     phy_txdatak_32b,            
   output wire [PHY_LANE-1:0]          phy_txdata_valid_32b,
   output wire [PHY_LANE-1:0]          phy_txstart_block_32b,      
   output wire [(PHY_LANE* 2)-1:0]     phy_txsync_header_32b,                    

   // 32b RX Data Ports
   input  wire [(PHY_LANE*32)-1:0]     phy_rxdata_32b,            
   input  wire [(PHY_LANE* 2)-1:0]     phy_rxdatak_32b,            
   input  wire [PHY_LANE-1:0]          phy_rxdata_valid_32b,         
   input  wire [PHY_LANE-1:0]          phy_rxstart_block_32b,        
   input  wire [(PHY_LANE* 2)-1:0]     phy_rxsync_header_32b
   );

   genvar         lane;

   generate
      for (lane = 0; lane < PHY_LANE; lane = lane + 1) begin: per_lane_bridge
         //--------------------------------------------------------------------------
         // Gen4 TX 64b Bridge
         //--------------------------------------------------------------------------          
         pcie_bridge_rc_pcie4c_ip_gen4_tx_64b_bridge #(
            .TCQ              ( TCQ )
         ) gen4_tx_64b_bridge (                                         
            // Clock & Reset Ports
            .phy_pclk               ( phy_pclk ),  
            .phy_pclk2              ( phy_pclk2 ),  
            .phy_rst2               ( phy_rst2 ),  
      
            // Enable Ports
            .bridge_enable          ( bridge_enable ),
                                                     
            // 64b TX Data Ports 
            .phy_txelecidle_64b     ( phy_txelecidle_64b[lane] ),
            .phy_txdata_64b         ( phy_txdata_64b[(lane* 64)+:64] ),            
            .phy_txdatak_64b        ( phy_txdatak_64b[(lane* 2)+:2] ),            
            .phy_txdata_valid_64b   ( phy_txdata_valid_64b[lane] ),                
            .phy_txstart_block_64b  ( phy_txstart_block_64b[lane] ),                      
            .phy_txsync_header_64b  ( phy_txsync_header_64b[(lane* 2)+:2] ),                                          
      
            // 32b TX Data Ports 
            .phy_txelecidle_32b     ( phy_txelecidle_32b[lane] ),
            .phy_txdata_32b         ( phy_txdata_32b[(lane* 32)+:32] ),            
            .phy_txdatak_32b        ( phy_txdatak_32b[(lane* 2)+:2] ),            
            .phy_txdata_valid_32b   ( phy_txdata_valid_32b[lane] ),                
            .phy_txstart_block_32b  ( phy_txstart_block_32b[lane] ),                      
            .phy_txsync_header_32b  ( phy_txsync_header_32b[(lane* 2)+:2] )
         );
      
         //--------------------------------------------------------------------------
         // Gen4 RX 64b Bridge
         //--------------------------------------------------------------------------
      
         pcie_bridge_rc_pcie4c_ip_gen4_rx_64b_bridge #(
            .TCQ              ( TCQ )
         ) gen4_rx_64b_bridge (                                         
            // Clock & Reset Ports
            .phy_pclk               ( phy_pclk ),  
            .phy_pclk2              ( phy_pclk2 ),  
            .phy_rst                ( phy_rst ),  
            .phy_rst2               ( phy_rst2 ),  
      
            // Enable Ports
            .bridge_enable          ( bridge_enable ),

            // 32b RX Data Ports 
            .phy_rxdata_32b         ( phy_rxdata_32b[(lane* 32)+:32] ),            
            .phy_rxdatak_32b        ( phy_rxdatak_32b[(lane* 2)+:2] ),            
            .phy_rxdata_valid_32b   ( phy_rxdata_valid_32b[lane] ),                
            .phy_rxstart_block_32b  ( phy_rxstart_block_32b[lane] ),                      
            .phy_rxsync_header_32b  ( phy_rxsync_header_32b[(lane* 2)+:2] ),

            // 64b RX Data Ports 
            .phy_rxdata_64b         ( phy_rxdata_64b[(lane* 64)+:64] ),            
            .phy_rxdatak_64b        ( phy_rxdatak_64b[(lane* 2)+:2] ),            
            .phy_rxdata_valid_64b   ( phy_rxdata_valid_64b[lane] ),                
            .phy_rxstart_block_64b  ( phy_rxstart_block_64b[(lane* 2)+:2] ),                      
            .phy_rxsync_header_64b  ( phy_rxsync_header_64b[(lane* 2)+:2] )                                          
         );
      end
   endgenerate

endmodule
