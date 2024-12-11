// (c) Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
// (c) Copyright 2022-2024 Advanced Micro Devices, Inc. All rights reserved.
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
// 
// DO NOT MODIFY THIS FILE.


#include "dest_register_slice_sc.h"

#include "axi_register_slice.h"

#include <map>
#include <string>

dest_register_slice_sc::dest_register_slice_sc(const sc_core::sc_module_name& nm) : sc_core::sc_module(nm), mp_impl(NULL)
{
  // configure connectivity manager
  xsc::utils::xsc_sim_manager::addInstance("dest_register_slice", this);

  // initialize module
    xsc::common_cpp::properties model_param_props;
    model_param_props.addLong("C_AXI_PROTOCOL", "0");
    model_param_props.addLong("C_AXI_ID_WIDTH", "16");
    model_param_props.addLong("C_AXI_ADDR_WIDTH", "64");
    model_param_props.addLong("C_AXI_DATA_WIDTH", "512");
    model_param_props.addLong("C_AXI_SUPPORTS_USER_SIGNALS", "0");
    model_param_props.addLong("C_AXI_AWUSER_WIDTH", "1");
    model_param_props.addLong("C_AXI_ARUSER_WIDTH", "1");
    model_param_props.addLong("C_AXI_WUSER_WIDTH", "1");
    model_param_props.addLong("C_AXI_RUSER_WIDTH", "1");
    model_param_props.addLong("C_AXI_BUSER_WIDTH", "1");
    model_param_props.addLong("C_REG_CONFIG_AW", "9");
    model_param_props.addLong("C_REG_CONFIG_W", "9");
    model_param_props.addLong("C_REG_CONFIG_B", "1");
    model_param_props.addLong("C_REG_CONFIG_AR", "9");
    model_param_props.addLong("C_REG_CONFIG_R", "1");
    model_param_props.addLong("C_RESERVE_MODE", "0");
    model_param_props.addLong("C_NUM_SLR_CROSSINGS", "0");
    model_param_props.addLong("C_PIPELINES_MASTER_AW", "0");
    model_param_props.addLong("C_PIPELINES_MASTER_W", "0");
    model_param_props.addLong("C_PIPELINES_MASTER_B", "0");
    model_param_props.addLong("C_PIPELINES_MASTER_AR", "0");
    model_param_props.addLong("C_PIPELINES_MASTER_R", "0");
    model_param_props.addLong("C_PIPELINES_SLAVE_AW", "0");
    model_param_props.addLong("C_PIPELINES_SLAVE_W", "0");
    model_param_props.addLong("C_PIPELINES_SLAVE_B", "0");
    model_param_props.addLong("C_PIPELINES_SLAVE_AR", "0");
    model_param_props.addLong("C_PIPELINES_SLAVE_R", "0");
    model_param_props.addLong("C_PIPELINES_MIDDLE_AW", "0");
    model_param_props.addLong("C_PIPELINES_MIDDLE_W", "0");
    model_param_props.addLong("C_PIPELINES_MIDDLE_B", "0");
    model_param_props.addLong("C_PIPELINES_MIDDLE_AR", "0");
    model_param_props.addLong("C_PIPELINES_MIDDLE_R", "0");
    model_param_props.addString("C_FAMILY", "virtexuplusHBM");
    model_param_props.addString("COMPONENT_NAME", "dest_register_slice");

  mp_impl = new axi_register_slice("inst", model_param_props);

  // initialize AXI sockets
  M_INITIATOR_rd_socket = mp_impl->M_INITIATOR_rd_socket;
  M_INITIATOR_wr_socket = mp_impl->M_INITIATOR_wr_socket;
  S_TARGET_rd_socket = mp_impl->S_TARGET_rd_socket;
  S_TARGET_wr_socket = mp_impl->S_TARGET_wr_socket;
}

dest_register_slice_sc::~dest_register_slice_sc()
{
  xsc::utils::xsc_sim_manager::clean();

  delete mp_impl;
}

