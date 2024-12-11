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
// File       : pcie_bridge_rc_pcie4c_ip_gen4_perlane_eq_bridge.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
/*****************************************************************************
** Description:
**    Convert Gen4 Equalization I/F between
**       - PCLK2 (500MHz)
**       - PCLK (250MHz)
**    Only work in 1:2 clock ratio
**
******************************************************************************/

`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_rc_pcie4c_ip_gen4_perlane_eq_bridge #(
   // Parameters
   parameter integer PHY_LANE = 1,  // Valid settings: 1, 2, 4, 8, 16(only for Gen1/2/3)
   parameter integer TCQ      = 1
)  (                                                         
   // Clock & Reset Ports
   input  wire                         phy_pclk2,  
   input  wire                         phy_rst2,           

   // Enable Ports
   input  wire                         bridge_enable,

   // TX EQ Ports at PCLK
   input  wire [(PHY_LANE*2)-1:0]      phy_txeq_ctrl_pclk,            
   input  wire [(PHY_LANE*4)-1:0]      phy_txeq_preset_pclk,            
   input  wire [(PHY_LANE*6)-1:0]      phy_txeq_coeff_pclk,            

   // TX EQ Ports at PCLK2
   output wire [(PHY_LANE*2)-1:0]      phy_txeq_ctrl_pclk2,            
   output wire [(PHY_LANE*4)-1:0]      phy_txeq_preset_pclk2,            
   output wire [(PHY_LANE*6)-1:0]      phy_txeq_coeff_pclk2
   );

   genvar         lane;

   generate
      for (lane = 0; lane < PHY_LANE; lane = lane + 1) begin: per_lane_bridge
         //--------------------------------------------------------------------------
         // Gen4 TX EQ Bridge
         //--------------------------------------------------------------------------          
         pcie_bridge_rc_pcie4c_ip_gen4_tx_eq_bridge #(
            .TCQ              ( TCQ )
         ) gen4_tx_eq_bridge (                                         
            // Clock & Reset Ports
            .phy_pclk2              ( phy_pclk2 ),  
            .phy_rst2               ( phy_rst2 ),  
      
            // Enable Ports
            .bridge_enable          ( bridge_enable ),
                                                     
            // TX EQ Ports at PCLK
            .phy_txeq_ctrl_pclk     ( phy_txeq_ctrl_pclk[(lane* 2)+:2] ),            
            .phy_txeq_preset_pclk   ( phy_txeq_preset_pclk[(lane* 4)+:4] ),            
            .phy_txeq_coeff_pclk    ( phy_txeq_coeff_pclk[(lane* 6)+:6] ),                                          
      
            // TX EQ Ports at PCLK2
            .phy_txeq_ctrl_pclk2    ( phy_txeq_ctrl_pclk2[(lane* 2)+:2] ),            
            .phy_txeq_preset_pclk2  ( phy_txeq_preset_pclk2[(lane* 4)+:4] ),            
            .phy_txeq_coeff_pclk2   ( phy_txeq_coeff_pclk2[(lane* 6)+:6] )                                  
         );
      end
   endgenerate

endmodule
