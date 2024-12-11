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
// File       : pcie_bridge_rc_pcie4c_ip_phy_pipeline.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
/*****************************************************************************
** Description:
**    Programmable stages for routing to PHY Lanes
**
******************************************************************************/

`timescale 1ps/1ps

`define FF_CHAIN(chain_length, chain_width, rst_value, mod_name, clk_i, rst_i, ff_out, ff_in)   \
   pcie_bridge_rc_pcie4c_ip_phy_ff_chain #(.PIPELINE_STAGES(chain_length), .ASYNC("FALSE"), .FF_WIDTH(chain_width), .RST_VAL(rst_value), .TCQ(TCQ))   \
      mod_name (.clock_i(clk_i), \
                .reset_i(rst_i),   \
                .ff_i(ff_in), \
                .ff_o(ff_out));

`define AS_FF_CHAIN(chain_length, chain_width, rst_value, mod_name, clk_i, rst_i, ff_out, ff_in)   \
   pcie_bridge_rc_pcie4c_ip_phy_ff_chain #(.PIPELINE_STAGES(chain_length), .ASYNC("TRUE"), .FF_WIDTH(chain_width), .RST_VAL(rst_value), .TCQ(TCQ))   \
      mod_name (.clock_i(clk_i), \
                .reset_i(rst_i),   \
                .ff_i(ff_in), \
                .ff_o(ff_out));

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_rc_pcie4c_ip_phy_pipeline #(
   // Parameters
   parameter integer PIPELINE_STAGES   = 0,        // 0 = no pipeline; 1 = 1 stage; 2 = 2 stages; 3 = 3 stages
   parameter integer PHY_LANE          = 1,        // Valid settings: 1, 2, 4, 8, 16(only for Gen1/2/3)
   parameter integer TCQ               = 1
)  (   
   // Clock & Reset
   input  wire                         phy_pclk,          
   input  wire                         phy_rst,           
  
   // TX Data 
   input  wire [(PHY_LANE*64)-1:0]     phy_txdata_i,            
   input  wire [(PHY_LANE* 2)-1:0]     phy_txdatak_i,    
   input  wire [PHY_LANE-1:0]          phy_txdata_valid_i,
   input  wire [PHY_LANE-1:0]          phy_txstart_block_i,      
   input  wire [(PHY_LANE* 2)-1:0]     phy_txsync_header_i,      

   output wire [(PHY_LANE*64)-1:0]     phy_txdata_o,            
   output wire [(PHY_LANE* 2)-1:0]     phy_txdatak_o,    
   output wire [PHY_LANE-1:0]          phy_txdata_valid_o,
   output wire [PHY_LANE-1:0]          phy_txstart_block_o,      
   output wire [(PHY_LANE* 2)-1:0]     phy_txsync_header_o,     

   // RX Data
   input  wire [(PHY_LANE*64)-1:0]     phy_rxdata_i,            
   input  wire [(PHY_LANE* 2)-1:0]     phy_rxdatak_i,       
   input  wire [PHY_LANE-1:0]          phy_rxdata_valid_i,         
   input  wire [(PHY_LANE* 2)-1:0]     phy_rxstart_block_i,        
   input  wire [(PHY_LANE* 2)-1:0]     phy_rxsync_header_i,        

   output wire [(PHY_LANE*64)-1:0]     phy_rxdata_o,            
   output wire [(PHY_LANE* 2)-1:0]     phy_rxdatak_o,       
   output wire [PHY_LANE-1:0]          phy_rxdata_valid_o,         
   output wire [(PHY_LANE* 2)-1:0]     phy_rxstart_block_o,        
   output wire [(PHY_LANE* 2)-1:0]     phy_rxsync_header_o,        

   // PHY Command
   input  wire                         phy_txdetectrx_i,        
   input  wire [PHY_LANE-1:0]          phy_txelecidle_i,        
   input  wire [PHY_LANE-1:0]          phy_txcompliance_i,      
   input  wire [PHY_LANE-1:0]          phy_rxpolarity_i,        
   input  wire [1:0]                   phy_powerdown_i,         
   input  wire [1:0]                   phy_rate_i,  

   output wire                         phy_txdetectrx_o,        
   output wire [PHY_LANE-1:0]          phy_txelecidle_o,        
   output wire [PHY_LANE-1:0]          phy_txcompliance_o,      
   output wire [PHY_LANE-1:0]          phy_rxpolarity_o,        
   output wire [1:0]                   phy_powerdown_o,         
   output wire [1:0]                   phy_rate_o,              
   output wire                         phy_rate_is_gen4_o,
    
   // PHY Status
   input  wire [PHY_LANE-1:0]          phy_rxvalid_i,               
   input  wire [PHY_LANE-1:0]          phy_phystatus_i,          
   input  wire [PHY_LANE-1:0]          phy_rxelecidle_i,         
   input  wire [(PHY_LANE*3)-1:0]      phy_rxstatus_i,   

   output wire [PHY_LANE-1:0]          phy_rxvalid_o,               
   output wire [PHY_LANE-1:0]          phy_phystatus_o,          
   output wire [PHY_LANE-1:0]          phy_rxelecidle_o,         
   output wire [(PHY_LANE*3)-1:0]      phy_rxstatus_o,   

   // TX Driver
   input  wire [ 2:0]                  phy_txmargin_i,          
   input  wire                         phy_txswing_i,           
   input  wire                         phy_txdeemph_i,  

   output wire [ 2:0]                  phy_txmargin_o,          
   output wire                         phy_txswing_o,           
   output wire                         phy_txdeemph_o,    
    
   // TX Equalization (Gen3/4)
   input  wire [(PHY_LANE*2)-1:0]      phy_txeq_ctrl_i,      
   input  wire [(PHY_LANE*4)-1:0]      phy_txeq_preset_i,       
   input  wire [(PHY_LANE*6)-1:0]      phy_txeq_coeff_i,   

   output wire [(PHY_LANE*2)-1:0]      phy_txeq_ctrl_o,      
   output wire [(PHY_LANE*4)-1:0]      phy_txeq_preset_o,       
   output wire [(PHY_LANE*6)-1:0]      phy_txeq_coeff_o,    

   input  wire [ 5:0]                  phy_txeq_fs_i,           
   input  wire [ 5:0]                  phy_txeq_lf_i,           
   input  wire [(PHY_LANE*18)-1:0]     phy_txeq_new_coeff_i,        
   input  wire [PHY_LANE-1:0]          phy_txeq_done_i,         

   output wire [ 5:0]                  phy_txeq_fs_o,           
   output wire [ 5:0]                  phy_txeq_lf_o,           
   output wire [(PHY_LANE*18)-1:0]     phy_txeq_new_coeff_o,        
   output wire [PHY_LANE-1:0]          phy_txeq_done_o,         

   // RX Equalization (Gen3/4)
   input  wire [(PHY_LANE*2)-1:0]      phy_rxeq_ctrl_i,     
   input  wire [(PHY_LANE*4)-1:0]      phy_rxeq_txpreset_i,   

   output wire [(PHY_LANE*2)-1:0]      phy_rxeq_ctrl_o,     
   output wire [(PHY_LANE*4)-1:0]      phy_rxeq_txpreset_o,      

   input  wire [PHY_LANE-1:0]          phy_rxeq_preset_sel_i,    
   input  wire [(PHY_LANE*18)-1:0]     phy_rxeq_new_txcoeff_i,   
   input  wire [PHY_LANE-1:0]          phy_rxeq_adapt_done_i,     
   input  wire [PHY_LANE-1:0]          phy_rxeq_done_i,

   output wire [PHY_LANE-1:0]          phy_rxeq_preset_sel_o,    
   output wire [(PHY_LANE*18)-1:0]     phy_rxeq_new_txcoeff_o,   
   output wire [PHY_LANE-1:0]          phy_rxeq_adapt_done_o,     
   output wire [PHY_LANE-1:0]          phy_rxeq_done_o,

   // Assist Signals
   input  wire                         as_mac_in_detect_i,
   input  wire                         as_cdr_hold_req_i,

   output wire                         as_mac_in_detect_o,
   output wire                         as_cdr_hold_req_o
   );

   genvar         lane;

generate
   for (lane = 0; lane < PHY_LANE; lane = lane + 1) begin: per_lane_ff_chain

      `FF_CHAIN(PIPELINE_STAGES, 64, 64'd0, phy_txdata_chain, phy_pclk, phy_rst, phy_txdata_o[(lane* 64)+:64], phy_txdata_i[(lane* 64)+:64])
      `FF_CHAIN(PIPELINE_STAGES, 64, 64'd0, phy_rxdata_chain, phy_pclk, phy_rst, phy_rxdata_o[(lane* 64)+:64], phy_rxdata_i[(lane* 64)+:64])

      `FF_CHAIN(PIPELINE_STAGES, 2, 2'd0, phy_txdatak_chain, phy_pclk, phy_rst, phy_txdatak_o[(lane* 2)+:2], phy_txdatak_i[(lane* 2)+:2])
      `FF_CHAIN(PIPELINE_STAGES, 1, 1'd0, phy_txdata_valid_chain, phy_pclk, phy_rst, phy_txdata_valid_o[lane], phy_txdata_valid_i[lane])
      `FF_CHAIN(PIPELINE_STAGES, 1, 1'd0, phy_txstart_block_chain, phy_pclk, phy_rst, phy_txstart_block_o[lane], phy_txstart_block_i[lane])
      `FF_CHAIN(PIPELINE_STAGES, 2, 2'd0, phy_txsync_header_chain, phy_pclk, phy_rst, phy_txsync_header_o[(lane* 2)+:2], phy_txsync_header_i[(lane* 2)+:2])

      `FF_CHAIN(PIPELINE_STAGES, 2, 2'd0, phy_rxdatak_chain, phy_pclk, phy_rst, phy_rxdatak_o[(lane* 2)+:2], phy_rxdatak_i[(lane* 2)+:2])
      `FF_CHAIN(PIPELINE_STAGES, 1, 1'd0, phy_rxdata_valid_chain, phy_pclk, phy_rst, phy_rxdata_valid_o[lane], phy_rxdata_valid_i[lane])
      `FF_CHAIN(PIPELINE_STAGES, 2, 2'd0, phy_rxstart_block_chain, phy_pclk, phy_rst, phy_rxstart_block_o[(lane* 2)+:2], phy_rxstart_block_i[(lane* 2)+:2])
      `FF_CHAIN(PIPELINE_STAGES, 2, 2'd0, phy_rxsync_header_chain, phy_pclk, phy_rst, phy_rxsync_header_o[(lane* 2)+:2], phy_rxsync_header_i[(lane* 2)+:2])

      `FF_CHAIN(PIPELINE_STAGES, 1, 1'd1, phy_txelecidle_chain, phy_pclk, phy_rst, phy_txelecidle_o[lane], phy_txelecidle_i[lane])
      `FF_CHAIN(PIPELINE_STAGES, 1, 1'd0, phy_txcompliance_chain, phy_pclk, phy_rst, phy_txcompliance_o[lane], phy_txcompliance_i[lane])
      `FF_CHAIN(PIPELINE_STAGES, 1, 1'd0, phy_rxpolarity_chain, phy_pclk, phy_rst, phy_rxpolarity_o[lane], phy_rxpolarity_i[lane])

      `FF_CHAIN(PIPELINE_STAGES, 1, 1'd0, phy_rxvalid_chain, phy_pclk, phy_rst, phy_rxvalid_o[lane], phy_rxvalid_i[lane])
      `AS_FF_CHAIN(PIPELINE_STAGES, 1, 1'd1, phy_phystatus_chain, phy_pclk, phy_rst, phy_phystatus_o[lane], phy_phystatus_i[lane])
      `AS_FF_CHAIN(PIPELINE_STAGES, 1, 1'd1, phy_rxelecidle_chain, phy_pclk, phy_rst, phy_rxelecidle_o[lane], phy_rxelecidle_i[lane])
      `FF_CHAIN(PIPELINE_STAGES, 3, 3'd0, phy_rxstatus_chain, phy_pclk, phy_rst, phy_rxstatus_o[(lane* 3)+:3], phy_rxstatus_i[(lane* 3)+:3])

      `FF_CHAIN(PIPELINE_STAGES, 2, 2'd0, phy_txeq_ctrl_chain, phy_pclk, phy_rst, phy_txeq_ctrl_o[(lane* 2)+:2], phy_txeq_ctrl_i[(lane* 2)+:2])
      `FF_CHAIN(PIPELINE_STAGES, 4, 6'd0, phy_txeq_preset_chain, phy_pclk, phy_rst, phy_txeq_preset_o[(lane* 4)+:4], phy_txeq_preset_i[(lane* 4)+:4])
      `FF_CHAIN(PIPELINE_STAGES, 6, 6'd0, phy_txeq_coeff_chain, phy_pclk, phy_rst, phy_txeq_coeff_o[(lane* 6)+:6], phy_txeq_coeff_i[(lane* 6)+:6])

      `FF_CHAIN(PIPELINE_STAGES,18,18'd0, phy_txeq_new_coeff_chain, phy_pclk, phy_rst, phy_txeq_new_coeff_o[(lane* 18)+:18], phy_txeq_new_coeff_i[(lane* 18)+:18])
      `FF_CHAIN(PIPELINE_STAGES, 1, 1'd0, phy_txeq_done_chain, phy_pclk, phy_rst, phy_txeq_done_o[lane], phy_txeq_done_i[lane])

      `FF_CHAIN(PIPELINE_STAGES, 2, 2'd0, phy_rxeq_ctrl_chain, phy_pclk, phy_rst, phy_rxeq_ctrl_o[(lane* 2)+:2], phy_rxeq_ctrl_i[(lane* 2)+:2])
      `FF_CHAIN(PIPELINE_STAGES, 4, 6'd0, phy_rxeq_txpreset_chain, phy_pclk, phy_rst, phy_rxeq_txpreset_o[(lane* 4)+:4], phy_rxeq_txpreset_i[(lane* 4)+:4])

      `FF_CHAIN(PIPELINE_STAGES, 1, 1'd0, phy_rxeq_preset_sel_chain, phy_pclk, phy_rst, phy_rxeq_preset_sel_o[lane], phy_rxeq_preset_sel_i[lane])
      `FF_CHAIN(PIPELINE_STAGES,18,18'd0, phy_rxeq_new_txcoeff_chain, phy_pclk, phy_rst, phy_rxeq_new_txcoeff_o[(lane* 18)+:18], phy_rxeq_new_txcoeff_i[(lane* 18)+:18])
      `FF_CHAIN(PIPELINE_STAGES, 1, 1'd0, phy_rxeq_adapt_done_chain, phy_pclk, phy_rst, phy_rxeq_adapt_done_o[lane], phy_rxeq_adapt_done_i[lane])
      `FF_CHAIN(PIPELINE_STAGES, 1, 1'd0, phy_rxeq_done_chain, phy_pclk, phy_rst, phy_rxeq_done_o[lane], phy_rxeq_done_i[lane])
   end
endgenerate

   `FF_CHAIN(PIPELINE_STAGES, 1, 1'd0, phy_txdetectrx_chain, phy_pclk, phy_rst, phy_txdetectrx_o, phy_txdetectrx_i)
   `FF_CHAIN(PIPELINE_STAGES, 2, 2'd2, phy_powerdown_chain, phy_pclk, phy_rst, phy_powerdown_o, phy_powerdown_i)
   `FF_CHAIN(PIPELINE_STAGES, 2, 2'd0, phy_rate_chain, phy_pclk, phy_rst, phy_rate_o, phy_rate_i)
   `FF_CHAIN(PIPELINE_STAGES, 1, 1'd0, phy_rate_g4_chain, phy_pclk, phy_rst, phy_rate_is_gen4_o, &phy_rate_i)
   `FF_CHAIN(PIPELINE_STAGES, 3, 3'd0, phy_txmargin_chain, phy_pclk, phy_rst, phy_txmargin_o, phy_txmargin_i)
   `FF_CHAIN(PIPELINE_STAGES, 1, 1'd0, phy_txswing_chain, phy_pclk, phy_rst, phy_txswing_o, phy_txswing_i)
   `FF_CHAIN(PIPELINE_STAGES, 1, 1'd1, phy_txdeemph_chain, phy_pclk, phy_rst, phy_txdeemph_o, phy_txdeemph_i)
   `FF_CHAIN(PIPELINE_STAGES, 6, 6'd0, phy_txeq_fs_chain, phy_pclk, phy_rst, phy_txeq_fs_o, phy_txeq_fs_i) 
   `FF_CHAIN(PIPELINE_STAGES, 6, 6'd0, phy_txeq_lf_chain, phy_pclk, phy_rst, phy_txeq_lf_o, phy_txeq_lf_i)
   `FF_CHAIN(PIPELINE_STAGES, 1, 1'd1, as_mac_in_detect_chain, phy_pclk, phy_rst, as_mac_in_detect_o, as_mac_in_detect_i)
   `FF_CHAIN(PIPELINE_STAGES, 1, 1'd0, as_cdr_hold_req_chain, phy_pclk, phy_rst, as_cdr_hold_req_o, as_cdr_hold_req_i)

endmodule
