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


#include "cl_axi4_to_axi3_conv_sc.h"

#include "axi_protocol_converter.h"

#include <map>
#include <string>

cl_axi4_to_axi3_conv_sc::cl_axi4_to_axi3_conv_sc(const sc_core::sc_module_name& nm) : sc_core::sc_module(nm), mp_impl(NULL)
{
  // configure connectivity manager
  xsc::utils::xsc_sim_manager::addInstance("cl_axi4_to_axi3_conv", this);

  // initialize module
    xsc::common_cpp::properties model_param_props;
    model_param_props.addLong("C_M_AXI_PROTOCOL", "1");
    model_param_props.addLong("C_S_AXI_PROTOCOL", "0");
    model_param_props.addLong("C_IGNORE_ID", "0");
    model_param_props.addLong("C_AXI_ID_WIDTH", "6");
    model_param_props.addLong("C_AXI_ADDR_WIDTH", "34");
    model_param_props.addLong("C_AXI_DATA_WIDTH", "256");
    model_param_props.addLong("C_AXI_SUPPORTS_WRITE", "1");
    model_param_props.addLong("C_AXI_SUPPORTS_READ", "1");
    model_param_props.addLong("C_AXI_SUPPORTS_USER_SIGNALS", "0");
    model_param_props.addLong("C_AXI_AWUSER_WIDTH", "1");
    model_param_props.addLong("C_AXI_ARUSER_WIDTH", "1");
    model_param_props.addLong("C_AXI_WUSER_WIDTH", "1");
    model_param_props.addLong("C_AXI_RUSER_WIDTH", "1");
    model_param_props.addLong("C_AXI_BUSER_WIDTH", "1");
    model_param_props.addLong("C_TRANSLATION_MODE", "2");
    model_param_props.addString("C_FAMILY", "virtexuplushbm");
    model_param_props.addString("COMPONENT_NAME", "cl_axi4_to_axi3_conv");

  mp_impl = new axi_protocol_converter("inst", model_param_props);

  // initialize AXI sockets
  target_rd_socket = mp_impl->target_rd_socket;
  target_wr_socket = mp_impl->target_wr_socket;
  initiator_rd_socket = mp_impl->initiator_rd_socket;
  initiator_wr_socket = mp_impl->initiator_wr_socket;
}

cl_axi4_to_axi3_conv_sc::~cl_axi4_to_axi3_conv_sc()
{
  xsc::utils::xsc_sim_manager::clean();

  delete mp_impl;
}

