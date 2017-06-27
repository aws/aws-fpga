//*****************************************************************************
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
//
//*****************************************************************************
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor             : Xilinx
// \   \   \/     Version            : 1.1
//  \   \         Application        : MIG
//  /   /         Filename           : ddr4_phy_v2_2_0_xiphy_riuor_wrapper.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR3 SDRAM & DDR4 SDRAM
// Purpose          :
//                   ddr4_phy_v2_2_0_xiphy_riuor_wrapper module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ps / 1ps

module ddr4_phy_v2_2_0_xiphy_riuor_wrapper # (
   parameter           SIM_DEVICE            = "ULTRASCALE"
) (
  input  [15:0]  riu_rd_data_low,    // Lower nibble RIU rd_data 
  input  [15:0]  riu_rd_data_upp,    // Upper nibble RIU rd_data 
  input          riu_valid_low,      // Lower nibble RIU riu2clb_valid 
  input          riu_valid_upp,      // Upper nibble RIU riu2clb_valid
  output [15:0]  riu_rd_data,        // ORed lower and upper RIU rd_data      
  output         riu_valid           // ORed lower and upper RIU write valid      
);

`ifdef ULTRASCALE_PHY_BLH
B_RIU_OR
`else
RIU_OR  # (
   .SIM_DEVICE   (SIM_DEVICE)
) 
`endif
  xiphy_riu_or
(
   .RIU_RD_DATA_LOW         (riu_rd_data_low),
   .RIU_RD_DATA_UPP         (riu_rd_data_upp),
   .RIU_RD_VALID_LOW        (riu_valid_low),
   .RIU_RD_VALID_UPP        (riu_valid_upp),
   .RIU_RD_DATA             (riu_rd_data),
   .RIU_RD_VALID            (riu_valid)
);

endmodule

