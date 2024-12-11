
// file: clk_mmcm_a.v
// (c) Copyright 2017-2018, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
//----------------------------------------------------------------------------
// User entered comments
//----------------------------------------------------------------------------
// None
//
//----------------------------------------------------------------------------
//  Output     Output      Phase    Duty Cycle   Pk-to-Pk     Phase
//   Clock     Freq (MHz)  (degrees)    (%)     Jitter (ps)  Error (ps)
//----------------------------------------------------------------------------
// clk_out1__125.00000______0.000______50.0_______92.548_____76.967
// clk_out2__375.00000______0.000______50.0_______76.316_____76.967
// clk_out3__500.00000______0.000______50.0_______72.605_____76.967
//
//----------------------------------------------------------------------------
// Input Clock   Freq (MHz)    Input Jitter (UI)
//----------------------------------------------------------------------------
// __primary_________100.000____________0.010

`timescale 1ps/1ps

(* CORE_GENERATION_INFO = "clk_mmcm_a,clk_wiz_v6_0_14_0_0,{component_name=clk_mmcm_a,use_phase_alignment=false,use_min_o_jitter=false,use_max_i_jitter=false,use_dyn_phase_shift=false,use_inclk_switchover=false,use_dyn_reconfig=true,enable_axi=1,feedback_source=FDBK_AUTO,PRIMITIVE=MMCM,num_out_clk=3,clkin1_period=10.000,clkin2_period=10.000,use_power_down=false,use_reset=true,use_locked=true,use_inclk_stopped=false,feedback_type=SINGLE,CLOCK_MGR_TYPE=NA,manual_override=false}" *)

module clk_mmcm_a 
 (
  input s_axi_aclk,
  input s_axi_aresetn,
  input [10 : 0] s_axi_awaddr,
  input s_axi_awvalid,
  output s_axi_awready,
  input [31 : 0] s_axi_wdata,
  input [3 : 0] s_axi_wstrb,
  input s_axi_wvalid,
  output s_axi_wready,
  output [1 : 0] s_axi_bresp,
  output s_axi_bvalid,
  input s_axi_bready,
  input [10 : 0] s_axi_araddr,
  input s_axi_arvalid,
  output s_axi_arready,
  output [31 : 0] s_axi_rdata,
  output [1 : 0] s_axi_rresp,
  output s_axi_rvalid,
  input s_axi_rready,
  // Clock out ports
  output        clk_out1,
  output        clk_out2,
  output        clk_out3,
  // Status and control signals
  output        locked,
 // Clock in ports
  input         clk_in1
 );

  clk_mmcm_a_axi_clk_config #(
  .C_S_AXI_ADDR_WIDTH(11),
  .C_S_AXI_DATA_WIDTH(32)
  ) inst
  (
  .s_axi_aclk      (s_axi_aclk),                    
  .s_axi_aresetn   (s_axi_aresetn),                    
  .s_axi_awaddr    (s_axi_awaddr),                    
  .s_axi_awvalid   (s_axi_awvalid),                    
  .s_axi_awready   (s_axi_awready),                    
  .s_axi_wdata     (s_axi_wdata),                    
  .s_axi_wstrb     (s_axi_wstrb),                    
  .s_axi_wvalid    (s_axi_wvalid),                    
  .s_axi_wready    (s_axi_wready),                    
  .s_axi_bresp     (s_axi_bresp),                    
  .s_axi_bvalid    (s_axi_bvalid),                    
  .s_axi_bready    (s_axi_bready),                    
  .s_axi_araddr    (s_axi_araddr),                    
  .s_axi_arvalid   (s_axi_arvalid),                    
  .s_axi_arready   (s_axi_arready),                    
  .s_axi_rdata     (s_axi_rdata),                    
  .s_axi_rresp     (s_axi_rresp),                    
  .s_axi_rvalid    (s_axi_rvalid),                    
  .s_axi_rready    (s_axi_rready),                    
  // Clock out ports  
  .clk_out1(clk_out1),
  .clk_out2(clk_out2),
  .clk_out3(clk_out3),
  // Status and control signals               
  .locked(locked),
 // Clock in ports
  .clk_in1(clk_in1)
  );

endmodule
