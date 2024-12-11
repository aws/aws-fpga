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
// File       : pcie_bridge_ep_pcie4c_ip_pl_eq.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_ep_pcie4c_ip_pl_eq #(
    parameter             TCQ = 100
   ,parameter             IMPL_TARGET = "SOFT"
   ,parameter             PL_UPSTREAM_FACING="TRUE"
  ) (
   
    input  wire           clk_i
   ,input  wire           reset_i
   ,input  wire           link_down_reset_i

   ,input  wire [5:0]     cfg_ltssm_state_i
   ,input  wire           pl_redo_eq_i
   ,input  wire           pl_redo_eq_speed_i
   ,output reg            pl_eq_mismatch_o
   ,output reg            pl_redo_eq_pending_o
   
   ,output wire           pl_gen34_redo_equalization_o
   ,output wire           pl_gen34_redo_eq_speed_o
   ,input  wire           pl_gen34_eq_mismatch_i
   );

   reg                    pl_eq_mismatch_w;
   reg                    pl_redo_eq_pending_w;

   generate  
  
     if (PL_UPSTREAM_FACING == "TRUE") begin 

       always @(*) begin

         pl_eq_mismatch_w = pl_eq_mismatch_o;
         pl_redo_eq_pending_w = pl_redo_eq_pending_o;
    
         if (!pl_eq_mismatch_o && (cfg_ltssm_state_i[5:0] == 6'h0B) && pl_gen34_eq_mismatch_i) begin
    
           pl_eq_mismatch_w = 1'b1;
    
         end else if (!pl_redo_eq_pending_o && (cfg_ltssm_state_i[5:0] == 6'h0D) && pl_gen34_eq_mismatch_i) begin
    
           pl_redo_eq_pending_w = 1'b1;
      
         end else if (pl_redo_eq_pending_o && pl_redo_eq_i) begin
    
           pl_redo_eq_pending_w = 1'b0;
    
         end
    
       end

     end else begin // PL_UPSTREAM_FACING == FALSE
 
       always @(*) begin

         pl_eq_mismatch_w = pl_gen34_eq_mismatch_i;
         pl_redo_eq_pending_w = 1'b0;

       end

     end

   endgenerate
   
   always @(posedge clk_i) begin

     if (reset_i) begin

       pl_eq_mismatch_o <= #(TCQ) 1'b0;
       pl_redo_eq_pending_o <= #(TCQ) 1'b0;

     end else if (link_down_reset_i) begin   

       pl_eq_mismatch_o <= #(TCQ) 1'b0;
       pl_redo_eq_pending_o <= #(TCQ) 1'b0;

     end else begin
     
       pl_eq_mismatch_o <= #(TCQ) pl_eq_mismatch_w;
       pl_redo_eq_pending_o <= #(TCQ) pl_redo_eq_pending_w;

     end

   end

   assign pl_gen34_redo_equalization_o = pl_redo_eq_i;
   assign pl_gen34_redo_eq_speed_o = pl_redo_eq_speed_i;

endmodule // pcie_4_0_pl_eq
