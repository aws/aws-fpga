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
// File       : pcie_bridge_ep_pcie4c_ip_vf_decode.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_ep_pcie4c_ip_vf_decode #(

  parameter           TCQ = 100
 ,parameter           NUM_VFS = 252
 ,parameter [1:0]     TL_PF_ENABLE_REG=2'h0
 ,parameter [15:0]    PF0_SRIOV_CAP_TOTAL_VF=16'h0
 ,parameter [15:0]    PF1_SRIOV_CAP_TOTAL_VF=16'h0
 ,parameter [15:0]    PF2_SRIOV_CAP_TOTAL_VF=16'h0
 ,parameter [15:0]    PF3_SRIOV_CAP_TOTAL_VF=16'h0
 ,parameter [15:0]    PF0_SRIOV_FIRST_VF_OFFSET=16'h0
 ,parameter [15:0]    PF1_SRIOV_FIRST_VF_OFFSET=16'h0
 ,parameter [15:0]    PF2_SRIOV_FIRST_VF_OFFSET=16'h0
 ,parameter [15:0]    PF3_SRIOV_FIRST_VF_OFFSET=16'h0
 ,parameter [3:0]     SRIOV_CAP_ENABLE=4'h0
 ,parameter           ARI_CAP_ENABLE="FALSE"
 ,parameter           PF0_PRI_CAP_ON="FALSE"
 ,parameter           PF1_PRI_CAP_ON="FALSE"
 ,parameter           PF2_PRI_CAP_ON="FALSE"
 ,parameter           PF3_PRI_CAP_ON="FALSE"
 ,parameter           PF0_ATS_CAP_ON="FALSE"
 ,parameter           PF1_ATS_CAP_ON="FALSE"
 ,parameter           PF2_ATS_CAP_ON="FALSE"
 ,parameter           PF3_ATS_CAP_ON="FALSE"
 ,parameter           VFG0_ATS_CAP_ON="FALSE"
 ,parameter           VFG1_ATS_CAP_ON="FALSE"
 ,parameter           VFG2_ATS_CAP_ON="FALSE"
 ,parameter           VFG3_ATS_CAP_ON="FALSE"
 ,parameter           PF0_PASID_CAP_ON="FALSE"

  ) (

  input wire          clk_i
 ,input wire          reset_i
 ,input wire          link_down_i
 ,input wire          cfg_ext_write_received_i
 ,input wire [9:0]    cfg_ext_register_number_i
 ,input wire [7:0]    cfg_ext_function_number_i
 ,input wire [31:0]   cfg_ext_write_data_i
 ,input wire [3:0]    cfg_ext_write_byte_enable_i
 ,input wire [3:0]    cfg_flr_in_process_i
 ,input wire [7:0]    cfg_vf_flr_func_num_i
 ,input wire          cfg_vf_flr_done_i

 ,output wire [NUM_VFS-1:0]   cfg_vf_flr_in_process_o
 ,output wire [2*NUM_VFS-1:0] cfg_vf_status_o          // Bit 0: Memory Space Enable; Bit 1: Bus Master Enable
 ,output wire [3*NUM_VFS-1:0] cfg_vf_power_state_o     // 000b - D0-Uninitialized; 001b - D0-Active; 010b - D1; 100b - D3hot
 ,output wire [NUM_VFS-1:0]   cfg_vf_tph_requester_enable_o
 ,output wire [3*NUM_VFS-1:0] cfg_vf_tph_st_mode_o     
 ,output wire [NUM_VFS-1:0]   cfg_interrupt_msix_vf_enable_o
 ,output wire [NUM_VFS-1:0]   cfg_interrupt_msix_vf_mask_o

 ,output wire [2*4-1:0]       cfg_pri_control_o             // 2 bits per PF
 ,output wire [4-1:0]         cfg_ats_control_enable_o      // 1 bit (E) per PF
 ,output wire [NUM_VFS-1:0]   cfg_vf_ats_control_enable_o   // 1 bit (E) per VF
 ,output wire [3*4-1:0]       cfg_pasid_control_o           // 3 bits per PF
 ,output wire [5*4-1:0]       cfg_max_pasid_width_control_o // 5 bits per PF

  );

 wire [1:0]     attr_tl_pf_enable_reg_i = TL_PF_ENABLE_REG[1:0];
 wire [15:0]    attr_pf0_sriov_cap_total_vf_i = PF0_SRIOV_CAP_TOTAL_VF[15:0];
 wire [15:0]    attr_pf1_sriov_cap_total_vf_i = PF1_SRIOV_CAP_TOTAL_VF[15:0];
 wire [15:0]    attr_pf2_sriov_cap_total_vf_i = PF2_SRIOV_CAP_TOTAL_VF[15:0];
 wire [15:0]    attr_pf3_sriov_cap_total_vf_i = PF3_SRIOV_CAP_TOTAL_VF[15:0];

 wire [15:0]    attr_pf0_sriov_first_vf_offset_i = PF0_SRIOV_FIRST_VF_OFFSET[15:0];
 wire [15:0]    attr_pf1_sriov_first_vf_offset_i = PF1_SRIOV_FIRST_VF_OFFSET[15:0];
 wire [15:0]    attr_pf2_sriov_first_vf_offset_i = PF2_SRIOV_FIRST_VF_OFFSET[15:0];
 wire [15:0]    attr_pf3_sriov_first_vf_offset_i = PF3_SRIOV_FIRST_VF_OFFSET[15:0];

 wire  [3:0]    attr_sriov_cap_enable_i = SRIOV_CAP_ENABLE[3:0];
 wire           attr_ari_cap_enable_i = (ARI_CAP_ENABLE == "TRUE") ? 1'b1 : 1'b0;

 wire           attr_pf0_pri_cap_on_i   = (PF0_PRI_CAP_ON   == "TRUE") ? 1'b1 : 1'b0;
 wire           attr_pf1_pri_cap_on_i   = (PF1_PRI_CAP_ON   == "TRUE") ? 1'b1 : 1'b0;
 wire           attr_pf2_pri_cap_on_i   = (PF2_PRI_CAP_ON   == "TRUE") ? 1'b1 : 1'b0;
 wire           attr_pf3_pri_cap_on_i   = (PF3_PRI_CAP_ON   == "TRUE") ? 1'b1 : 1'b0;
 wire           attr_pf0_ats_cap_on_i   = (PF0_ATS_CAP_ON   == "TRUE") ? 1'b1 : 1'b0;
 wire           attr_pf1_ats_cap_on_i   = (PF1_ATS_CAP_ON   == "TRUE") ? 1'b1 : 1'b0;
 wire           attr_pf2_ats_cap_on_i   = (PF2_ATS_CAP_ON   == "TRUE") ? 1'b1 : 1'b0;
 wire           attr_pf3_ats_cap_on_i   = (PF3_ATS_CAP_ON   == "TRUE") ? 1'b1 : 1'b0;
 wire           attr_vfg0_ats_cap_on_i  = (VFG0_ATS_CAP_ON  == "TRUE") ? 1'b1 : 1'b0;
 wire           attr_vfg1_ats_cap_on_i  = (VFG1_ATS_CAP_ON  == "TRUE") ? 1'b1 : 1'b0;
 wire           attr_vfg2_ats_cap_on_i  = (VFG2_ATS_CAP_ON  == "TRUE") ? 1'b1 : 1'b0;
 wire           attr_vfg3_ats_cap_on_i  = (VFG3_ATS_CAP_ON  == "TRUE") ? 1'b1 : 1'b0;
 wire           attr_pf0_pasid_cap_on_i = (PF0_PASID_CAP_ON == "TRUE") ? 1'b1 : 1'b0;

pcie_bridge_ep_pcie4c_ip_vf_decode_attr #(

    .TCQ(TCQ)

  ) pcie_4_0_vf_decode_inst (

     .clk_i(clk_i)
    ,.reset_i(reset_i)
    ,.link_down_i(link_down_i)
    ,.cfg_ext_write_received_i(cfg_ext_write_received_i)
    ,.cfg_ext_register_number_i(cfg_ext_register_number_i[9:0])
    ,.cfg_ext_function_number_i(cfg_ext_function_number_i[7:0])
    ,.cfg_ext_write_data_i(cfg_ext_write_data_i[31:0])
    ,.cfg_ext_write_byte_enable_i(cfg_ext_write_byte_enable_i[3:0])
    ,.cfg_flr_in_process_i(cfg_flr_in_process_i[3:0])
    ,.cfg_vf_flr_done_i (cfg_vf_flr_done_i)
    ,.cfg_vf_flr_func_num_i (cfg_vf_flr_func_num_i)

    ,.cfg_vf_flr_in_process_o(cfg_vf_flr_in_process_o[251:0])
    ,.cfg_vf_status_o(cfg_vf_status_o[503:0])
    ,.cfg_vf_power_state_o(cfg_vf_power_state_o[755:0])
    ,.cfg_vf_tph_requester_enable_o(cfg_vf_tph_requester_enable_o[251:0])
    ,.cfg_vf_tph_st_mode_o(cfg_vf_tph_st_mode_o[755:0])
    ,.cfg_interrupt_msix_vf_enable_o(cfg_interrupt_msix_vf_enable_o[251:0])
    ,.cfg_interrupt_msix_vf_mask_o(cfg_interrupt_msix_vf_mask_o[251:0])

    ,.cfg_pri_control_o(cfg_pri_control_o)                         // 2 bits per PF
    ,.cfg_ats_control_enable_o(cfg_ats_control_enable_o)           // 1 bit (E) per 
    ,.cfg_vf_ats_control_enable_o(cfg_vf_ats_control_enable_o)     // 1 bit (E) per 
    ,.cfg_pasid_control_o(cfg_pasid_control_o)                     // 3 bits per PF
    ,.cfg_max_pasid_width_control_o(cfg_max_pasid_width_control_o) // 5 bits per PF

    ,.attr_tl_pf_enable_reg_i(attr_tl_pf_enable_reg_i)
    ,.attr_pf0_sriov_cap_total_vf_i(attr_pf0_sriov_cap_total_vf_i)
    ,.attr_pf1_sriov_cap_total_vf_i(attr_pf1_sriov_cap_total_vf_i)
    ,.attr_pf2_sriov_cap_total_vf_i(attr_pf2_sriov_cap_total_vf_i)
    ,.attr_pf3_sriov_cap_total_vf_i(attr_pf3_sriov_cap_total_vf_i)

    ,.attr_pf0_sriov_first_vf_offset_i(attr_pf0_sriov_first_vf_offset_i)
    ,.attr_pf1_sriov_first_vf_offset_i(attr_pf1_sriov_first_vf_offset_i)
    ,.attr_pf2_sriov_first_vf_offset_i(attr_pf2_sriov_first_vf_offset_i)
    ,.attr_pf3_sriov_first_vf_offset_i(attr_pf3_sriov_first_vf_offset_i)

    ,.attr_sriov_cap_enable_i(attr_sriov_cap_enable_i)
    ,.attr_ari_cap_enable_i(attr_ari_cap_enable_i)

    ,.attr_pf0_pri_cap_on_i(attr_pf0_pri_cap_on_i)
    ,.attr_pf1_pri_cap_on_i(attr_pf1_pri_cap_on_i)
    ,.attr_pf2_pri_cap_on_i(attr_pf2_pri_cap_on_i)
    ,.attr_pf3_pri_cap_on_i(attr_pf3_pri_cap_on_i)
    ,.attr_pf0_ats_cap_on_i(attr_pf0_ats_cap_on_i)
    ,.attr_pf1_ats_cap_on_i(attr_pf1_ats_cap_on_i)
    ,.attr_pf2_ats_cap_on_i(attr_pf2_ats_cap_on_i)
    ,.attr_pf3_ats_cap_on_i(attr_pf3_ats_cap_on_i)
    ,.attr_vfg0_ats_cap_on_i(attr_vfg0_ats_cap_on_i)
    ,.attr_vfg1_ats_cap_on_i(attr_vfg1_ats_cap_on_i)
    ,.attr_vfg2_ats_cap_on_i(attr_vfg2_ats_cap_on_i)
    ,.attr_vfg3_ats_cap_on_i(attr_vfg3_ats_cap_on_i)
    ,.attr_pf0_pasid_cap_on_i(attr_pf0_pasid_cap_on_i)

  );


endmodule




