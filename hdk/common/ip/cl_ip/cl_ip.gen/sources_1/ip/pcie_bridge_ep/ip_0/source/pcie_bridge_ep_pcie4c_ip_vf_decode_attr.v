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
// File       : pcie_bridge_ep_pcie4c_ip_vf_decode_attr.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------

`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_ep_pcie4c_ip_vf_decode_attr #(

  parameter           TCQ = 100
 ,parameter           NUM_VFS = 252

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

 ,output reg [NUM_VFS-1:0]   cfg_vf_flr_in_process_o
 ,output reg [2*NUM_VFS-1:0] cfg_vf_status_o          // Bit 0: Memory Space Enable; Bit 1: Bus Master Enable
 ,output reg [3*NUM_VFS-1:0] cfg_vf_power_state_o     // 000b - D0-Uninitialized; 001b - D0-Active; 010b - D1; 100b - D3hot
 ,output reg [NUM_VFS-1:0]   cfg_vf_tph_requester_enable_o
 ,output reg [3*NUM_VFS-1:0] cfg_vf_tph_st_mode_o     
 ,output reg [NUM_VFS-1:0]   cfg_interrupt_msix_vf_enable_o
 ,output reg [NUM_VFS-1:0]   cfg_interrupt_msix_vf_mask_o

 ,output reg [2*4-1:0]       cfg_pri_control_o             // 2 bits per PF
 ,output reg [4-1:0]         cfg_ats_control_enable_o      // 1 bit (E) per PF
 ,output reg [NUM_VFS-1:0]   cfg_vf_ats_control_enable_o   // 1 bit (E) per VF
 ,output reg [3*4-1:0]       cfg_pasid_control_o           // 3 bits per PF
 ,output reg [5*4-1:0]       cfg_max_pasid_width_control_o // 5 bits per PF


 ,input wire [1:0]     attr_tl_pf_enable_reg_i
 ,input wire [15:0]    attr_pf0_sriov_cap_total_vf_i
 ,input wire [15:0]    attr_pf1_sriov_cap_total_vf_i
 ,input wire [15:0]    attr_pf2_sriov_cap_total_vf_i
 ,input wire [15:0]    attr_pf3_sriov_cap_total_vf_i

 ,input wire [15:0]    attr_pf0_sriov_first_vf_offset_i
 ,input wire [15:0]    attr_pf1_sriov_first_vf_offset_i
 ,input wire [15:0]    attr_pf2_sriov_first_vf_offset_i
 ,input wire [15:0]    attr_pf3_sriov_first_vf_offset_i

 ,input wire  [3:0]    attr_sriov_cap_enable_i
 ,input wire           attr_ari_cap_enable_i

 ,input  wire          attr_pf0_pri_cap_on_i
 ,input  wire          attr_pf1_pri_cap_on_i
 ,input  wire          attr_pf2_pri_cap_on_i
 ,input  wire          attr_pf3_pri_cap_on_i
 ,input  wire          attr_pf0_ats_cap_on_i
 ,input  wire          attr_pf1_ats_cap_on_i
 ,input  wire          attr_pf2_ats_cap_on_i
 ,input  wire          attr_pf3_ats_cap_on_i
 ,input  wire          attr_vfg0_ats_cap_on_i
 ,input  wire          attr_vfg1_ats_cap_on_i
 ,input  wire          attr_vfg2_ats_cap_on_i
 ,input  wire          attr_vfg3_ats_cap_on_i

 ,input  wire          attr_pf0_pasid_cap_on_i

  );

  localparam [9:0]   REG_DEV_CTRL=10'h1E;
  localparam         REG_DEV_CTRL__FLR_SIZE=1;
  localparam         REG_DEV_CTRL__FLR=15;

  localparam [9:0]   REG_PCI_CMD=10'h1;
  localparam         REG_PCI_CMD__BME_SIZE=1;  
  localparam         REG_PCI_CMD__BME=2;
  localparam         REG_PCI_CMD__MSE_SIZE=1;  
  localparam         REG_PCI_CMD__MSE=1;  

  localparam [9:0]   REG_PM_CSR=10'h11;
  localparam         REG_PM_CSR__PS_SIZE=2;
  localparam         REG_PM_CSR__PS=0;

  localparam [9:0]   REG_TPH_CR=10'h8A;
  localparam         REG_TPH_CR__RQE_SIZE=1;  
  localparam         REG_TPH_CR__RQE=8;  
  localparam         REG_TPH_CR__STMS_SIZE=3;
  localparam         REG_TPH_CR__STMS=0;

  localparam [9:0]   REG_MSIX_CR=10'h18;
  localparam         REG_MSIX_CR__EN_SIZE=1;  
  localparam         REG_MSIX_CR__EN=31;  
  localparam         REG_MSIX_CR__MSK_SIZE=1;
  localparam         REG_MSIX_CR__MSK=30;
  localparam         PF_VF_MAP_WIDTH=256;

  localparam [9:0]   REG_ATS_CR=10'hE1;  // 380
  localparam         REG_ATS_CR__EN_SIZE=1;
  localparam         REG_ATS_CR__EN=31;

  localparam [9:0]   REG_PRI_CR=10'hE5 ;  // 390
  localparam         REG_PRI_CR__EN_SIZE=2;
  localparam         REG_PRI_CR__EN=0;

  localparam [9:0]   REG_PASID_CR=10'h17D ;  // 5F0
  localparam         REG_PASID_CR__EN_SIZE=2;
  localparam         REG_PASID_CR__EN=17;

  localparam         REG_PASID_CR__PASID_SIZE_SIZE=2;
  localparam         REG_PASID_CR__PASID_SIZE=5;

  reg                 cfg_ext_write_received;
  reg [9:0]           cfg_ext_register_number;
  reg [7:0]           cfg_ext_function_number;
  reg [31:0]          cfg_ext_write_data;
  reg [3:0]           cfg_ext_write_byte_enable;

  reg [NUM_VFS-1:0]   cfg_vf_flr_in_process_w;
  reg [2*NUM_VFS-1:0] cfg_vf_status_w;
  reg [3*NUM_VFS-1:0] cfg_vf_power_state_w;
  reg [NUM_VFS-1:0]   cfg_vf_tph_requester_enable_w;
  reg [3*NUM_VFS-1:0] cfg_vf_tph_st_mode_w;
  reg [NUM_VFS-1:0]   cfg_interrupt_msix_vf_enable_w;
  reg [NUM_VFS-1:0]   cfg_interrupt_msix_vf_mask_w;
  reg [NUM_VFS-1:0]   cfg_interrupt_msix_vf_flr_msk_w;
  reg [NUM_VFS-1:0]   reg_cfg_interrupt_msix_vf_flr_msk;

  wire [NUM_VFS-1:0]  cfg_vf_active_w;
  reg [NUM_VFS-1:0]   reg_cfg_vf_active;
  reg [NUM_VFS-1:0]   cfg_vf_active;

  wire [7:0]          cfg_ext_function_number_w;
  wire [9:0]          cfg_ext_function_number_w_2_b0;
  wire [9:0]          cfg_ext_function_number_w_2_b1;
  wire [10:0]         cfg_ext_function_number_w_3_b0;
  wire [10:0]         cfg_ext_function_number_w_3_b1;
  wire [10:0]         cfg_ext_function_number_w_3_b2;
  wire [3:0]          pf_mapenable;
  wire                pf_as_vf;
  wire [2:0]          pf_as_vf_mapd;

  // Only use attributes in these static assignments for PF_VF_MAP
  wire [(PF_VF_MAP_WIDTH-1):0] pf0_vf_size;
  wire [(PF_VF_MAP_WIDTH-1):0] pf1_vf_size;
  wire [(PF_VF_MAP_WIDTH-1):0] pf2_vf_size;
  wire [(PF_VF_MAP_WIDTH-1):0] pf3_vf_size;
  wire [(PF_VF_MAP_WIDTH-1):0] pf0_vf_mapd;
  wire [(PF_VF_MAP_WIDTH-1):0] pf1_vf_mapd;
  wire [(PF_VF_MAP_WIDTH-1):0] pf2_vf_mapd;
  wire [(PF_VF_MAP_WIDTH-1):0] pf3_vf_mapd;

  wire [(PF_VF_MAP_WIDTH-1):0] pf0_vf_map_w;
  wire [(PF_VF_MAP_WIDTH-1):0] pf1_vf_map_w;
  wire [(PF_VF_MAP_WIDTH-1):0] pf2_vf_map_w;
  wire [(PF_VF_MAP_WIDTH-1):0] pf3_vf_map_w;

  reg [2*4-1:0]                cfg_pri_control_w;
  reg [4-1:0]                  cfg_ats_control_enable_w;
  reg [NUM_VFS-1:0]            cfg_vf_ats_control_enable_w;
  reg [3*4-1:0]                cfg_pasid_control_w;
  reg [5*4-1:0]                cfg_max_pasid_width_control_w;

  integer                      i;

  always @(posedge clk_i) begin
  
    if (reset_i) begin

      cfg_ext_write_received <= #(TCQ) 1'b0;
      cfg_ext_register_number <= #(TCQ) 10'b0;
      cfg_ext_function_number <= #(TCQ) 8'b0;
      cfg_ext_write_data <= #(TCQ) 32'b0;
      cfg_ext_write_byte_enable <= #(TCQ) 4'b0;

      cfg_vf_flr_in_process_o <= #(TCQ) {NUM_VFS{1'b0}};
      cfg_vf_status_o <= #(TCQ) {2*NUM_VFS{1'b0}};
      cfg_vf_power_state_o <= #(TCQ) {3*NUM_VFS{1'b0}};
      cfg_vf_tph_requester_enable_o <= #(TCQ) {2*NUM_VFS{1'b0}};
      cfg_vf_tph_st_mode_o <= #(TCQ) {3*NUM_VFS{1'b0}};
      cfg_interrupt_msix_vf_enable_o <= #(TCQ) {NUM_VFS{1'b0}};
      cfg_interrupt_msix_vf_mask_o <= #(TCQ) {NUM_VFS{1'b0}};

      reg_cfg_vf_active <= #(TCQ) {NUM_VFS{1'b0}};
      reg_cfg_interrupt_msix_vf_flr_msk <= #(TCQ) {NUM_VFS{1'b1}};   

      cfg_pri_control_o <= #(TCQ) {2*4{1'b0}};
      cfg_ats_control_enable_o <= #(TCQ) {4{1'b0}};
      cfg_vf_ats_control_enable_o <= #(TCQ) {NUM_VFS{1'b0}};
      cfg_pasid_control_o <= #(TCQ) {3*4{1'b0}};
      cfg_max_pasid_width_control_o <= #(TCQ) {5*4{1'b0}};

    end else if (link_down_i) begin

      cfg_ext_write_received <= #(TCQ) 1'b0;
      cfg_ext_register_number <= #(TCQ) 10'b0;
      cfg_ext_function_number <= #(TCQ) 8'b0;
      cfg_ext_write_data <= #(TCQ) 32'b0;
      cfg_ext_write_byte_enable <= #(TCQ) 4'b0;

      cfg_vf_flr_in_process_o <= #(TCQ) {NUM_VFS{1'b0}};
      cfg_vf_status_o <= #(TCQ) {2*NUM_VFS{1'b0}};
      cfg_vf_power_state_o <= #(TCQ) {3*NUM_VFS{1'b0}};
      cfg_vf_tph_requester_enable_o <= #(TCQ) {2*NUM_VFS{1'b0}};
      cfg_vf_tph_st_mode_o <= #(TCQ) {3*NUM_VFS{1'b0}};
      cfg_interrupt_msix_vf_enable_o <= #(TCQ) {NUM_VFS{1'b0}};
      cfg_interrupt_msix_vf_mask_o <= #(TCQ) {NUM_VFS{1'b0}};

      reg_cfg_vf_active <= #(TCQ) {NUM_VFS{1'b0}};
      reg_cfg_interrupt_msix_vf_flr_msk <= #(TCQ) {NUM_VFS{1'b1}};   

      cfg_pri_control_o <= #(TCQ) {2*4{1'b0}};
      cfg_ats_control_enable_o <= #(TCQ) {4{1'b0}};
      cfg_vf_ats_control_enable_o <= #(TCQ) {NUM_VFS{1'b0}};
      cfg_pasid_control_o <= #(TCQ) {3*4{1'b0}};
      cfg_max_pasid_width_control_o <= #(TCQ) {5*4{1'b0}};

    end else begin

      cfg_ext_write_received <= #(TCQ) cfg_ext_write_received_i;
      cfg_ext_register_number <= #(TCQ) cfg_ext_register_number_i;
      cfg_ext_function_number <= #(TCQ) cfg_ext_function_number_i; 
      cfg_ext_write_data <= #(TCQ) cfg_ext_write_data_i;
      cfg_ext_write_byte_enable <= #(TCQ) cfg_ext_write_byte_enable_i;

      cfg_vf_flr_in_process_o <= #(TCQ) cfg_vf_flr_in_process_w;
      cfg_vf_status_o <= #(TCQ) cfg_vf_status_w;
      cfg_vf_power_state_o <= #(TCQ) cfg_vf_power_state_w;
      cfg_vf_tph_requester_enable_o <= #(TCQ) cfg_vf_tph_requester_enable_w;
      cfg_vf_tph_st_mode_o <= #(TCQ) cfg_vf_tph_st_mode_w;
      cfg_interrupt_msix_vf_enable_o <= #(TCQ) cfg_interrupt_msix_vf_enable_w & cfg_interrupt_msix_vf_flr_msk_w;
      cfg_interrupt_msix_vf_mask_o <= #(TCQ) cfg_interrupt_msix_vf_mask_w & cfg_interrupt_msix_vf_flr_msk_w;

      reg_cfg_vf_active <= #(TCQ) cfg_vf_active_w;
      reg_cfg_interrupt_msix_vf_flr_msk <= #(TCQ) cfg_interrupt_msix_vf_flr_msk_w;

      cfg_pri_control_o <= #(TCQ) cfg_pri_control_w;
      cfg_ats_control_enable_o <= #(TCQ) cfg_ats_control_enable_w;
      cfg_vf_ats_control_enable_o <= #(TCQ) cfg_vf_ats_control_enable_w;
      cfg_pasid_control_o <= #(TCQ) cfg_pasid_control_w;
      cfg_max_pasid_width_control_o <= cfg_max_pasid_width_control_o;

    end

  end

  /*
  *  1)
  *  if any of the PF sees a FLR (cfg_flr_in_process_i bits set to 1b),
  *  then, corresponding VF bits in cfg_interrupt_msix_vf_enable_o and
  *  cfg_interrupt_msix_vf_mask_o must be reset.
  *  2)
  *  if any of the VF sees a FLR (cfg_vf_flr_in_process_w bits set to 1b),
  *  then, corresponding VF bits in cfg_interrupt_msix_vf_enable_o and
  *  cfg_interrupt_msix_vf_mask_o must be reset.
  */

  always @ (*) begin

    for (i = 0; i < 252; i = i + 1) begin

      if (cfg_flr_in_process_i[0] & pf0_vf_map_w[i+4])
        cfg_interrupt_msix_vf_flr_msk_w[i] = 1'b0;
      else if (!cfg_flr_in_process_i[0] & pf0_vf_map_w[i+4])
        cfg_interrupt_msix_vf_flr_msk_w[i] = 1'b1;
      else
	cfg_interrupt_msix_vf_flr_msk_w[i] = reg_cfg_interrupt_msix_vf_flr_msk[i];

    end

    for (i = 0; i < 252; i = i + 1) begin

      if (cfg_flr_in_process_i[1] & pf1_vf_map_w[i+4])
        cfg_interrupt_msix_vf_flr_msk_w[i] = 1'b0; 
      else if (!cfg_flr_in_process_i[1] & pf1_vf_map_w[i+4])
        cfg_interrupt_msix_vf_flr_msk_w[i] = 1'b1; 
      else
	cfg_interrupt_msix_vf_flr_msk_w[i] = reg_cfg_interrupt_msix_vf_flr_msk[i];

    end

    for (i = 0; i < 252; i = i + 1) begin

      if (cfg_flr_in_process_i[2] & pf2_vf_map_w[i+4])
        cfg_interrupt_msix_vf_flr_msk_w[i] = 1'b0; 
      else if (!cfg_flr_in_process_i[2] & pf2_vf_map_w[i+4])
        cfg_interrupt_msix_vf_flr_msk_w[i] = 1'b1; 
      else
	cfg_interrupt_msix_vf_flr_msk_w[i] = reg_cfg_interrupt_msix_vf_flr_msk[i];

    end

    for (i = 0; i < 252; i = i + 1) begin

      if (cfg_flr_in_process_i[3] & pf3_vf_map_w[i+4])
        cfg_interrupt_msix_vf_flr_msk_w[i] = 1'b0; 
      else if (!cfg_flr_in_process_i[3] & pf3_vf_map_w[i+4])
        cfg_interrupt_msix_vf_flr_msk_w[i] = 1'b1; 
      else
	cfg_interrupt_msix_vf_flr_msk_w[i] = reg_cfg_interrupt_msix_vf_flr_msk[i];

    end

    for (i = 0; i < 252; i = i + 1) begin

      if (cfg_vf_flr_in_process_w[i])
        cfg_interrupt_msix_vf_flr_msk_w[i] = 1'b0;
      else
        cfg_interrupt_msix_vf_flr_msk_w[i] = 1'b1;

    end

  end

  always @(*) begin

    cfg_vf_flr_in_process_w = cfg_vf_flr_in_process_o;
    cfg_vf_status_w = cfg_vf_status_o;
    cfg_vf_power_state_w = cfg_vf_power_state_o;
    cfg_vf_tph_requester_enable_w = cfg_vf_tph_requester_enable_o;
    cfg_vf_tph_st_mode_w = cfg_vf_tph_st_mode_o;
    cfg_interrupt_msix_vf_enable_w = cfg_interrupt_msix_vf_enable_o; 
    cfg_interrupt_msix_vf_mask_w = cfg_interrupt_msix_vf_mask_o;
    cfg_vf_active = cfg_vf_active_w;

    if (cfg_ext_write_received && (cfg_ext_function_number > 3)) begin

      if (cfg_ext_register_number == REG_DEV_CTRL) begin

        if (cfg_ext_write_byte_enable[1])
          cfg_vf_flr_in_process_w[cfg_ext_function_number_w] = cfg_ext_write_data[REG_DEV_CTRL__FLR];

      end else if (cfg_ext_register_number == REG_PCI_CMD) begin

        if (cfg_ext_write_byte_enable[0]) begin

          cfg_vf_status_w[cfg_ext_function_number_w_2_b0] = cfg_ext_write_data[REG_PCI_CMD__MSE]; 
          cfg_vf_status_w[cfg_ext_function_number_w_2_b1] = cfg_ext_write_data[REG_PCI_CMD__BME]; 
          cfg_vf_active[cfg_ext_function_number_w] = cfg_ext_write_data[REG_PCI_CMD__BME] | cfg_ext_write_data[REG_PCI_CMD__MSE];
          // if Function in D0-Uninit then transtion to D0-Active
          if ((!cfg_vf_power_state_w[cfg_ext_function_number_w_3_b0]) &&
              (!cfg_vf_power_state_w[cfg_ext_function_number_w_3_b1]) &&
              (!cfg_vf_power_state_w[cfg_ext_function_number_w_3_b2]))
            cfg_vf_power_state_w[cfg_ext_function_number_w_3_b0] = cfg_vf_active_w[cfg_ext_function_number_w];

        end

      end else if (cfg_ext_register_number == REG_PM_CSR) begin

        if (cfg_ext_write_byte_enable[0]) begin

          cfg_vf_power_state_w[cfg_ext_function_number_w_3_b0] = cfg_vf_active[cfg_ext_function_number_w] && 
					                           (!cfg_ext_write_data[REG_PM_CSR__PS] || 
					                            !cfg_ext_write_data[REG_PM_CSR__PS+REG_PM_CSR__PS_SIZE-1]);
          cfg_vf_power_state_w[cfg_ext_function_number_w_3_b1] = (cfg_ext_write_data[REG_PM_CSR__PS] && 
		                                                  !cfg_ext_write_data[REG_PM_CSR__PS+REG_PM_CSR__PS_SIZE-1]); 
          cfg_vf_power_state_w[cfg_ext_function_number_w_3_b2] = (cfg_ext_write_data[REG_PM_CSR__PS] && 
		                                                  cfg_ext_write_data[REG_PM_CSR__PS+REG_PM_CSR__PS_SIZE-1]); 

        end

      end else if (cfg_ext_register_number == REG_TPH_CR) begin

        if (cfg_ext_write_byte_enable[0]) begin

          cfg_vf_tph_st_mode_w[cfg_ext_function_number_w_3_b0] = cfg_ext_write_data[REG_TPH_CR__STMS];
          cfg_vf_tph_st_mode_w[cfg_ext_function_number_w_3_b1] = cfg_ext_write_data[REG_TPH_CR__STMS+1]; 
          cfg_vf_tph_st_mode_w[cfg_ext_function_number_w_3_b2] = cfg_ext_write_data[REG_TPH_CR__STMS+2]; 

        end

        if (cfg_ext_write_byte_enable[1])
          cfg_vf_tph_requester_enable_w[cfg_ext_function_number_w] = cfg_ext_write_data[REG_TPH_CR__RQE]; 

      end else if (cfg_ext_register_number == REG_MSIX_CR) begin

        if (cfg_ext_write_byte_enable[3]) begin
          cfg_interrupt_msix_vf_enable_w[cfg_ext_function_number_w] = cfg_ext_write_data[REG_MSIX_CR__EN];
          cfg_interrupt_msix_vf_mask_w[cfg_ext_function_number_w] = cfg_ext_write_data[REG_MSIX_CR__MSK];
        end

      end

    end

    if (cfg_vf_flr_done_i) begin
      for (i = 0; i < 252; i = i + 1) begin
        if (cfg_vf_flr_func_num_i == (i+4))
          cfg_vf_flr_in_process_w[i] = 1'b0;
      end
    end

  end

  //
  // ATS, PRI, PASID Signals
  // 

  always @(*) begin

    cfg_pri_control_w = cfg_pri_control_o;
    cfg_ats_control_enable_w = cfg_ats_control_enable_o;
    cfg_vf_ats_control_enable_w = cfg_vf_ats_control_enable_o;
    cfg_pasid_control_w = cfg_pasid_control_o;
    cfg_max_pasid_width_control_w = cfg_max_pasid_width_control_o;

    // Handle PF outputs
    if (cfg_ext_write_received && (cfg_ext_function_number < 4)) begin

      if (cfg_ext_register_number == REG_ATS_CR) begin

        if (cfg_ext_write_byte_enable[3])
          cfg_ats_control_enable_w[cfg_ext_function_number] = cfg_ext_write_data[REG_ATS_CR__EN];

      end else if (cfg_ext_register_number == REG_PRI_CR) begin

        if (cfg_ext_write_byte_enable[0]) begin
          if(cfg_ext_function_number == 0)
            cfg_pri_control_w[1:0] = cfg_ext_write_data[(REG_PRI_CR__EN+REG_PRI_CR__EN_SIZE-1):REG_PRI_CR__EN];
          else if(cfg_ext_function_number == 1)
            cfg_pri_control_w[3:2] = cfg_ext_write_data[(REG_PRI_CR__EN+REG_PRI_CR__EN_SIZE-1):REG_PRI_CR__EN];
          else if(cfg_ext_function_number == 2)
            cfg_pri_control_w[5:4] = cfg_ext_write_data[(REG_PRI_CR__EN+REG_PRI_CR__EN_SIZE-1):REG_PRI_CR__EN];
          else
            cfg_pri_control_w[7:6] = cfg_ext_write_data[(REG_PRI_CR__EN+REG_PRI_CR__EN_SIZE-1):REG_PRI_CR__EN];
        end

      end else if (cfg_ext_register_number == REG_PASID_CR) begin

        if (cfg_ext_write_byte_enable[2])
          cfg_pasid_control_w[cfg_ext_function_number] = cfg_ext_write_data[(REG_PASID_CR__EN+REG_PASID_CR__EN_SIZE):REG_PASID_CR__EN];

        for (i = 0; i < 4; i = i + 1) begin

          if (cfg_ext_register_number == REG_PASID_CR)
            if (i == (cfg_ext_function_number-4))
              cfg_max_pasid_width_control_w[(5*i)+:5] = cfg_ext_write_data[(REG_PASID_CR__EN+REG_PASID_CR__EN_SIZE):REG_PASID_CR__EN];

        end

      end else begin

	//       

      end    

    // Handle VF outputs
    end else if (cfg_ext_write_received && (cfg_ext_function_number > 3)) begin

      for (i = 0; i < 252; i = i + 1) begin
  
        if (cfg_ext_register_number == REG_ATS_CR)
          if (cfg_ext_write_byte_enable[3])
            if (i == (cfg_ext_function_number-4))
              cfg_vf_ats_control_enable_w[i] = cfg_ext_write_data[REG_ATS_CR__EN];
  
       end

    end else begin

    end

  end

  assign cfg_ext_function_number_w = cfg_ext_function_number - 4;
  assign cfg_ext_function_number_w_2_b0 = 2*(cfg_ext_function_number_w)+0;
  assign cfg_ext_function_number_w_2_b1 = 2*(cfg_ext_function_number_w)+1;
  assign cfg_ext_function_number_w_3_b0 = 3*(cfg_ext_function_number_w)+0;
  assign cfg_ext_function_number_w_3_b1 = 3*(cfg_ext_function_number_w)+1;
  assign cfg_ext_function_number_w_3_b2 = 3*(cfg_ext_function_number_w)+2;
  assign cfg_vf_active_w = reg_cfg_vf_active;

  // Decoded number of pfs
  assign pf_mapenable[0] = 1'b1;
  assign pf_mapenable[1] = (attr_tl_pf_enable_reg_i == 2'h1) | (attr_tl_pf_enable_reg_i == 2'h2) | (attr_tl_pf_enable_reg_i == 2'h3) ;
  assign pf_mapenable[2] = (attr_tl_pf_enable_reg_i == 2'h2) | (attr_tl_pf_enable_reg_i == 2'h3) ;
  assign pf_mapenable[3] = (attr_tl_pf_enable_reg_i == 2'h3) ;
  
  // These bit-widths are sized for max. 256 functions and single bus no.
  assign pf0_vf_size = {PF_VF_MAP_WIDTH{pf_mapenable[0]}} << attr_pf0_sriov_first_vf_offset_i[7:0];
  assign pf1_vf_size = {PF_VF_MAP_WIDTH{pf_mapenable[1]}} << attr_pf1_sriov_first_vf_offset_i[7:0];
  assign pf2_vf_size = {PF_VF_MAP_WIDTH{pf_mapenable[2]}} << attr_pf2_sriov_first_vf_offset_i[7:0];
  assign pf3_vf_size = {PF_VF_MAP_WIDTH{pf_mapenable[3]}} << attr_pf3_sriov_cap_total_vf_i[7:0];
  
  // Make sure to disable the VFs based on the individual PF enables
  assign pf0_vf_mapd = pf_mapenable[0] ? (~pf0_vf_size << (        attr_pf0_sriov_first_vf_offset_i[7:0])) : 'b0;
  assign pf1_vf_mapd = pf_mapenable[1] ? (~pf1_vf_size << (8'h01 + attr_pf1_sriov_first_vf_offset_i[7:0])) : 'b0;
  assign pf2_vf_mapd = pf_mapenable[2] ? (~pf2_vf_size << (8'h02 + attr_pf2_sriov_first_vf_offset_i[7:0])) : 'b0;
  assign pf3_vf_mapd = pf_mapenable[3] ? (~pf3_vf_size << (8'h03 + attr_pf3_sriov_first_vf_offset_i[7:0])) : 'b0;
  
  assign pf_as_vf = ((attr_sriov_cap_enable_i[0] == 1'b1) && (attr_ari_cap_enable_i == 1'b1)) ;
  assign pf_as_vf_mapd = pf_as_vf ? pf0_vf_mapd[3:1] : 3'h0;
  
  assign pf0_vf_map_w = {pf0_vf_mapd[(PF_VF_MAP_WIDTH-1):4],{pf_as_vf_mapd,pf_mapenable[0]}};
  assign pf1_vf_map_w = {pf1_vf_mapd[(PF_VF_MAP_WIDTH-1):4],{2'h0,pf_mapenable[1],1'h0}};
  assign pf2_vf_map_w = {pf2_vf_mapd[(PF_VF_MAP_WIDTH-1):4],{1'h0,pf_mapenable[2],2'h0}};
  assign pf3_vf_map_w = {pf3_vf_mapd[(PF_VF_MAP_WIDTH-1):4],{pf_mapenable[3], 3'h0}};

endmodule



