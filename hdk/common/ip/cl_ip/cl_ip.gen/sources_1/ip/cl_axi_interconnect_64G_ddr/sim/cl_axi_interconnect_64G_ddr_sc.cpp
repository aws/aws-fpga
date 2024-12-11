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


#include "cl_axi_interconnect_64G_ddr_sc.h"

#include "axi_crossbar.h"

#include <map>
#include <string>

cl_axi_interconnect_64G_ddr_sc::cl_axi_interconnect_64G_ddr_sc(const sc_core::sc_module_name& nm) : sc_core::sc_module(nm), mp_impl(NULL)
{
  // configure connectivity manager
  xsc::utils::xsc_sim_manager::addInstance("cl_axi_interconnect_64G_ddr", this);

  // initialize module
    xsc::common_cpp::properties model_param_props;
    model_param_props.addLong("C_NUM_SLAVE_SLOTS", "2");
    model_param_props.addLong("C_NUM_MASTER_SLOTS", "2");
    model_param_props.addLong("C_AXI_ID_WIDTH", "16");
    model_param_props.addLong("C_AXI_ADDR_WIDTH", "64");
    model_param_props.addLong("C_AXI_DATA_WIDTH", "512");
    model_param_props.addLong("C_AXI_PROTOCOL", "0");
    model_param_props.addLong("C_NUM_ADDR_RANGES", "1");
    model_param_props.addLong("C_AXI_SUPPORTS_USER_SIGNALS", "0");
    model_param_props.addLong("C_AXI_AWUSER_WIDTH", "1");
    model_param_props.addLong("C_AXI_ARUSER_WIDTH", "1");
    model_param_props.addLong("C_AXI_WUSER_WIDTH", "1");
    model_param_props.addLong("C_AXI_RUSER_WIDTH", "1");
    model_param_props.addLong("C_AXI_BUSER_WIDTH", "1");
    model_param_props.addLong("C_R_REGISTER", "0");
    model_param_props.addLong("C_CONNECTIVITY_MODE", "1");
    model_param_props.addString("C_FAMILY", "virtexuplusHBM");
    model_param_props.addBitString("C_M_AXI_BASE_ADDR", "00000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000", 128);
    model_param_props.addBitString("C_M_AXI_ADDR_WIDTH", "0000000000000000000000000010010000000000000000000000000000100100", 64);
    model_param_props.addBitString("C_S_AXI_BASE_ID", "0000000000000000100000000000000000000000000000000000000000000000", 64);
    model_param_props.addBitString("C_S_AXI_THREAD_ID_WIDTH", "0000000000000000000000000000111100000000000000000000000000001111", 64);
    model_param_props.addBitString("C_M_AXI_WRITE_CONNECTIVITY", "0000000000000000000000000000001100000000000000000000000000000011", 64);
    model_param_props.addBitString("C_M_AXI_READ_CONNECTIVITY", "0000000000000000000000000000001100000000000000000000000000000011", 64);
    model_param_props.addBitString("C_S_AXI_SINGLE_THREAD", "0000000000000000000000000000000000000000000000000000000000000000", 64);
    model_param_props.addBitString("C_S_AXI_WRITE_ACCEPTANCE", "0000000000000000000000000010000000000000000000000000000000100000", 64);
    model_param_props.addBitString("C_S_AXI_READ_ACCEPTANCE", "0000000000000000000000000010000000000000000000000000000000100000", 64);
    model_param_props.addBitString("C_M_AXI_WRITE_ISSUING", "0000000000000000000000000010000000000000000000000000000000100000", 64);
    model_param_props.addBitString("C_M_AXI_READ_ISSUING", "0000000000000000000000000010000000000000000000000000000000100000", 64);
    model_param_props.addBitString("C_S_AXI_ARB_PRIORITY", "0000000000000000000000000000000000000000000000000000000000000000", 64);
    model_param_props.addBitString("C_M_AXI_SECURE", "0000000000000000000000000000000000000000000000000000000000000000", 64);
    model_param_props.addString("COMPONENT_NAME", "cl_axi_interconnect_64G_ddr");

  mp_impl = new axi_crossbar("inst", model_param_props);

  // initialize AXI sockets
  target_0_rd_socket = mp_impl->target_0_rd_socket;
  target_0_wr_socket = mp_impl->target_0_wr_socket;
  initiator_0_rd_socket = mp_impl->initiator_0_rd_socket;
  initiator_0_wr_socket = mp_impl->initiator_0_wr_socket;
  target_1_rd_socket = mp_impl->target_1_rd_socket;
  target_1_wr_socket = mp_impl->target_1_wr_socket;
  initiator_1_rd_socket = mp_impl->initiator_1_rd_socket;
  initiator_1_wr_socket = mp_impl->initiator_1_wr_socket;
}

cl_axi_interconnect_64G_ddr_sc::~cl_axi_interconnect_64G_ddr_sc()
{
  xsc::utils::xsc_sim_manager::clean();

  delete mp_impl;
}

