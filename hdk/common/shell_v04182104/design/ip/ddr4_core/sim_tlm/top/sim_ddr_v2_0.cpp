// (c) Copyright(C) 2013 - 2019 by Xilinx, Inc. All rights reserved.
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
#include "sim_ddr_v2_0.h"
#include <sstream>
#include <fstream>

sim_ddr_v2_0::sim_ddr_v2_0(sc_core::sc_module_name name,
    xsc::common_cpp::properties model_param_props) :
  sc_module(name) {
    //Configuring user parameters here
    //sim_xdma::getInstance()->numberOfddrs = numberOfddrs;
    clk=model_param_props.getFloat("C0.DDR4_UI_CLOCK");
    c0_ddr4_ui_clk_sync_rst.initialize(true);
    //Configuring user parameters here
    //sim_xdma::getInstance()->numberOfddrs = numberOfddrs;
    m_report_handler=new xsc::common_cpp::report_handler("report_handler");
    //m_report_handler->set_verbosity_level(xsc::common_cpp::VERBOSITY::DEBUG);
    std::string clk_prop=model_param_props.getString("System_Clock");
    if(clk_prop=="Differential")
    {
      c0_sys_clk_i(out1);
    }
    else
    {
      c0_sys_clk_p(out1);
      c0_sys_clk_n(out2);
    }
    std::string param_suffix="0";
    model_param_props.addString("ddr_index", param_suffix);
    model_param_props.addLong("partial_data_length", std::to_string(64));
    int ddr_saxi_width = 0;
    ddr_saxi_width = model_param_props.getLongLong("C0.DDR4_AXI_DATA_WIDTH");
    ddrx_top_tlm_model = new xsc::sim_ddr_v1_0::sim_ddrx(sc_core::sc_gen_unique_name("ddrx_top_tlm_model"),
        model_param_props, ddr_saxi_width,m_report_handler);
    C0_DDR_SAXI_wr_socket = new xtlm::xtlm_aximm_target_socket(
        sc_core::sc_gen_unique_name("C0_DDR_SAXI_wr_socket"),
        model_param_props.getLongLong("C0.DDR4_AXI_DATA_WIDTH"));
    C0_DDR_SAXI_rd_socket = new xtlm::xtlm_aximm_target_socket(
        sc_core::sc_gen_unique_name("C0_DDR_SAXI_rd_socket"),
        model_param_props.getLongLong("C0.DDR4_AXI_DATA_WIDTH"));
    (C0_DDR_SAXI_wr_socket)->bind(*ddrx_top_tlm_model->C0_DDRX_S_AXI_wr_socket);
    (C0_DDR_SAXI_rd_socket)->bind(*ddrx_top_tlm_model->C0_DDRX_S_AXI_rd_socket);
    bool control=model_param_props.getBool("C0.DDR4_Ecc");
    if(control==true)
    {
      C0_DDR_SAXI_CTRL_rd_socket= new xtlm::xtlm_aximm_target_socket("target_rd_socket",32);
      C0_DDR_SAXI_CTRL_wr_socket = new xtlm::xtlm_aximm_target_socket("target_wr_socket",32);
      rd_target_util = new xtlm::xtlm_aximm_target_rd_socket_util("rd_tar_util",
          xtlm::aximm::TRANSACTION, 32);
      wr_target_util = new xtlm::xtlm_aximm_target_wr_socket_util("wr_tar_util",
          xtlm::aximm::TRANSACTION, 32);
      C0_DDR_SAXI_CTRL_rd_socket->bind(rd_target_util->rd_socket);
      C0_DDR_SAXI_CTRL_wr_socket->bind(wr_target_util->wr_socket);
    }
    else
    {
      C0_DDR_SAXI_CTRL_rd_socket=nullptr;
      C0_DDR_SAXI_CTRL_wr_socket=nullptr;
      rd_target_util=nullptr;
      wr_target_util=nullptr;
    }
    ddrx_top_tlm_model->axi_clk.bind(c0_ddr4_ui_clk);
    SC_THREAD(generateReset);


  }
void sim_ddr_v2_0::generateReset() {
  wait(1000000000/(2*clk),SC_NS);
  c0_ddr4_ui_clk_sync_rst.write(!c0_ddr4_ui_clk_sync_rst.read());
}
sim_ddr_v2_0::~sim_ddr_v2_0() {
  if(m_report_handler->get_verbosity_level()==xsc::common_cpp::VERBOSITY::DEBUG) {
    m_ss.str("");
    m_ss<<"sim_ddr_v1_1 destructor"<<std::endl;
    XSC_REPORT_INFO_VERB((*m_report_handler),"ddrv1_0",m_ss.str().c_str(),DEBUG);
  }

  delete ddrx_top_tlm_model;
  delete C0_DDR_SAXI_wr_socket;
  delete C0_DDR_SAXI_rd_socket;
  delete wr_target_util;
  delete rd_target_util;
  delete C0_DDR_SAXI_CTRL_rd_socket;
  delete C0_DDR_SAXI_CTRL_wr_socket;  
}

