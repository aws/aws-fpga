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


#include "cl_sda_axil_xbar_sc.h"

#include "cl_sda_axil_xbar.h"

#include "axi_crossbar.h"

#include <map>
#include <string>





#ifdef XILINX_SIMULATOR
cl_sda_axil_xbar::cl_sda_axil_xbar(const sc_core::sc_module_name& nm) : cl_sda_axil_xbar_sc(nm), aclk("aclk"), aresetn("aresetn"), s_axi_awaddr("s_axi_awaddr"), s_axi_awprot("s_axi_awprot"), s_axi_awvalid("s_axi_awvalid"), s_axi_awready("s_axi_awready"), s_axi_wdata("s_axi_wdata"), s_axi_wstrb("s_axi_wstrb"), s_axi_wvalid("s_axi_wvalid"), s_axi_wready("s_axi_wready"), s_axi_bresp("s_axi_bresp"), s_axi_bvalid("s_axi_bvalid"), s_axi_bready("s_axi_bready"), s_axi_araddr("s_axi_araddr"), s_axi_arprot("s_axi_arprot"), s_axi_arvalid("s_axi_arvalid"), s_axi_arready("s_axi_arready"), s_axi_rdata("s_axi_rdata"), s_axi_rresp("s_axi_rresp"), s_axi_rvalid("s_axi_rvalid"), s_axi_rready("s_axi_rready"), m_axi_awaddr("m_axi_awaddr"), m_axi_awprot("m_axi_awprot"), m_axi_awvalid("m_axi_awvalid"), m_axi_awready("m_axi_awready"), m_axi_wdata("m_axi_wdata"), m_axi_wstrb("m_axi_wstrb"), m_axi_wvalid("m_axi_wvalid"), m_axi_wready("m_axi_wready"), m_axi_bresp("m_axi_bresp"), m_axi_bvalid("m_axi_bvalid"), m_axi_bready("m_axi_bready"), m_axi_araddr("m_axi_araddr"), m_axi_arprot("m_axi_arprot"), m_axi_arvalid("m_axi_arvalid"), m_axi_arready("m_axi_arready"), m_axi_rdata("m_axi_rdata"), m_axi_rresp("m_axi_rresp"), m_axi_rvalid("m_axi_rvalid"), m_axi_rready("m_axi_rready")
{

  // initialize pins
  mp_impl->aclk(aclk);
  mp_impl->aresetn(aresetn);

  // initialize transactors
  mp_S00_AXI_transactor = NULL;
  mp_s_axi_awvalid_converter = NULL;
  mp_s_axi_awready_converter = NULL;
  mp_s_axi_wvalid_converter = NULL;
  mp_s_axi_wready_converter = NULL;
  mp_s_axi_bvalid_converter = NULL;
  mp_s_axi_bready_converter = NULL;
  mp_s_axi_arvalid_converter = NULL;
  mp_s_axi_arready_converter = NULL;
  mp_s_axi_rvalid_converter = NULL;
  mp_s_axi_rready_converter = NULL;
  mp_M00_AXI_transactor = NULL;
  mp_m_axi_awaddr_converter_0 = NULL;
  mp_m_axi_awprot_converter_0 = NULL;
  mp_m_axi_awvalid_converter_0 = NULL;
  mp_m_axi_awready_converter_0 = NULL;
  mp_m_axi_wdata_converter_0 = NULL;
  mp_m_axi_wstrb_converter_0 = NULL;
  mp_m_axi_wvalid_converter_0 = NULL;
  mp_m_axi_wready_converter_0 = NULL;
  mp_m_axi_bresp_converter_0 = NULL;
  mp_m_axi_bvalid_converter_0 = NULL;
  mp_m_axi_bready_converter_0 = NULL;
  mp_m_axi_araddr_converter_0 = NULL;
  mp_m_axi_arprot_converter_0 = NULL;
  mp_m_axi_arvalid_converter_0 = NULL;
  mp_m_axi_arready_converter_0 = NULL;
  mp_m_axi_rdata_converter_0 = NULL;
  mp_m_axi_rresp_converter_0 = NULL;
  mp_m_axi_rvalid_converter_0 = NULL;
  mp_m_axi_rready_converter_0 = NULL;
  mp_M01_AXI_transactor = NULL;
  mp_m_axi_awaddr_converter_1 = NULL;
  mp_m_axi_awprot_converter_1 = NULL;
  mp_m_axi_awvalid_converter_1 = NULL;
  mp_m_axi_awready_converter_1 = NULL;
  mp_m_axi_wdata_converter_1 = NULL;
  mp_m_axi_wstrb_converter_1 = NULL;
  mp_m_axi_wvalid_converter_1 = NULL;
  mp_m_axi_wready_converter_1 = NULL;
  mp_m_axi_bresp_converter_1 = NULL;
  mp_m_axi_bvalid_converter_1 = NULL;
  mp_m_axi_bready_converter_1 = NULL;
  mp_m_axi_araddr_converter_1 = NULL;
  mp_m_axi_arprot_converter_1 = NULL;
  mp_m_axi_arvalid_converter_1 = NULL;
  mp_m_axi_arready_converter_1 = NULL;
  mp_m_axi_rdata_converter_1 = NULL;
  mp_m_axi_rresp_converter_1 = NULL;
  mp_m_axi_rvalid_converter_1 = NULL;
  mp_m_axi_rready_converter_1 = NULL;

  // initialize junctures
  mp_m_axi_concat_araddr = NULL;
  mp_m_axi_concat_arprot = NULL;
  mp_m_axi_concat_arvalid = NULL;
  mp_m_axi_concat_awaddr = NULL;
  mp_m_axi_concat_awprot = NULL;
  mp_m_axi_concat_awvalid = NULL;
  mp_m_axi_concat_bready = NULL;
  mp_m_axi_concat_rready = NULL;
  mp_m_axi_concat_wdata = NULL;
  mp_m_axi_concat_wstrb = NULL;
  mp_m_axi_concat_wvalid = NULL;
  mp_m_axi_split_arready = NULL;
  mp_m_axi_split_awready = NULL;
  mp_m_axi_split_bresp = NULL;
  mp_m_axi_split_bvalid = NULL;
  mp_m_axi_split_rdata = NULL;
  mp_m_axi_split_rresp = NULL;
  mp_m_axi_split_rvalid = NULL;
  mp_m_axi_split_wready = NULL;
  mp_m_axi_concat_awaddr = new xsc::xsc_concatenator<64, 2>("m_axi_concat_awaddr");
  mp_m_axi_concat_awaddr->in_port[0](m_axi_concat_awaddr_out_0);
  mp_m_axi_concat_awaddr->out_port(m_axi_awaddr);
    mp_m_axi_concat_awaddr->offset_port(0, 0);
  mp_m_axi_concat_awprot = new xsc::xsc_concatenator<6, 2>("m_axi_concat_awprot");
  mp_m_axi_concat_awprot->in_port[0](m_axi_concat_awprot_out_0);
  mp_m_axi_concat_awprot->out_port(m_axi_awprot);
    mp_m_axi_concat_awprot->offset_port(0, 0);
  mp_m_axi_concat_awvalid = new xsc::xsc_concatenator<2, 2>("m_axi_concat_awvalid");
  mp_m_axi_concat_awvalid->in_port[0](m_axi_concat_awvalid_out_0);
  mp_m_axi_concat_awvalid->out_port(m_axi_awvalid);
    mp_m_axi_concat_awvalid->offset_port(0, 0);
  mp_m_axi_split_awready = new xsc::xsc_split<2, 2>("m_axi_split_awready");
  mp_m_axi_split_awready->in_port(m_axi_awready);
  mp_m_axi_split_awready->out_port[0](m_axi_split_awready_out_0);
    mp_m_axi_split_awready->add_mask(0,1,0);
  mp_m_axi_concat_wdata = new xsc::xsc_concatenator<64, 2>("m_axi_concat_wdata");
  mp_m_axi_concat_wdata->in_port[0](m_axi_concat_wdata_out_0);
  mp_m_axi_concat_wdata->out_port(m_axi_wdata);
    mp_m_axi_concat_wdata->offset_port(0, 0);
  mp_m_axi_concat_wstrb = new xsc::xsc_concatenator<8, 2>("m_axi_concat_wstrb");
  mp_m_axi_concat_wstrb->in_port[0](m_axi_concat_wstrb_out_0);
  mp_m_axi_concat_wstrb->out_port(m_axi_wstrb);
    mp_m_axi_concat_wstrb->offset_port(0, 0);
  mp_m_axi_concat_wvalid = new xsc::xsc_concatenator<2, 2>("m_axi_concat_wvalid");
  mp_m_axi_concat_wvalid->in_port[0](m_axi_concat_wvalid_out_0);
  mp_m_axi_concat_wvalid->out_port(m_axi_wvalid);
    mp_m_axi_concat_wvalid->offset_port(0, 0);
  mp_m_axi_split_wready = new xsc::xsc_split<2, 2>("m_axi_split_wready");
  mp_m_axi_split_wready->in_port(m_axi_wready);
  mp_m_axi_split_wready->out_port[0](m_axi_split_wready_out_0);
    mp_m_axi_split_wready->add_mask(0,1,0);
  mp_m_axi_split_bresp = new xsc::xsc_split<4, 2>("m_axi_split_bresp");
  mp_m_axi_split_bresp->in_port(m_axi_bresp);
  mp_m_axi_split_bresp->out_port[0](m_axi_split_bresp_out_0);
    mp_m_axi_split_bresp->add_mask(0,2,0);
  mp_m_axi_split_bvalid = new xsc::xsc_split<2, 2>("m_axi_split_bvalid");
  mp_m_axi_split_bvalid->in_port(m_axi_bvalid);
  mp_m_axi_split_bvalid->out_port[0](m_axi_split_bvalid_out_0);
    mp_m_axi_split_bvalid->add_mask(0,1,0);
  mp_m_axi_concat_bready = new xsc::xsc_concatenator<2, 2>("m_axi_concat_bready");
  mp_m_axi_concat_bready->in_port[0](m_axi_concat_bready_out_0);
  mp_m_axi_concat_bready->out_port(m_axi_bready);
    mp_m_axi_concat_bready->offset_port(0, 0);
  mp_m_axi_concat_araddr = new xsc::xsc_concatenator<64, 2>("m_axi_concat_araddr");
  mp_m_axi_concat_araddr->in_port[0](m_axi_concat_araddr_out_0);
  mp_m_axi_concat_araddr->out_port(m_axi_araddr);
    mp_m_axi_concat_araddr->offset_port(0, 0);
  mp_m_axi_concat_arprot = new xsc::xsc_concatenator<6, 2>("m_axi_concat_arprot");
  mp_m_axi_concat_arprot->in_port[0](m_axi_concat_arprot_out_0);
  mp_m_axi_concat_arprot->out_port(m_axi_arprot);
    mp_m_axi_concat_arprot->offset_port(0, 0);
  mp_m_axi_concat_arvalid = new xsc::xsc_concatenator<2, 2>("m_axi_concat_arvalid");
  mp_m_axi_concat_arvalid->in_port[0](m_axi_concat_arvalid_out_0);
  mp_m_axi_concat_arvalid->out_port(m_axi_arvalid);
    mp_m_axi_concat_arvalid->offset_port(0, 0);
  mp_m_axi_split_arready = new xsc::xsc_split<2, 2>("m_axi_split_arready");
  mp_m_axi_split_arready->in_port(m_axi_arready);
  mp_m_axi_split_arready->out_port[0](m_axi_split_arready_out_0);
    mp_m_axi_split_arready->add_mask(0,1,0);
  mp_m_axi_split_rdata = new xsc::xsc_split<64, 2>("m_axi_split_rdata");
  mp_m_axi_split_rdata->in_port(m_axi_rdata);
  mp_m_axi_split_rdata->out_port[0](m_axi_split_rdata_out_0);
    mp_m_axi_split_rdata->add_mask(0,32,0);
  mp_m_axi_split_rresp = new xsc::xsc_split<4, 2>("m_axi_split_rresp");
  mp_m_axi_split_rresp->in_port(m_axi_rresp);
  mp_m_axi_split_rresp->out_port[0](m_axi_split_rresp_out_0);
    mp_m_axi_split_rresp->add_mask(0,2,0);
  mp_m_axi_split_rvalid = new xsc::xsc_split<2, 2>("m_axi_split_rvalid");
  mp_m_axi_split_rvalid->in_port(m_axi_rvalid);
  mp_m_axi_split_rvalid->out_port[0](m_axi_split_rvalid_out_0);
    mp_m_axi_split_rvalid->add_mask(0,1,0);
  mp_m_axi_concat_rready = new xsc::xsc_concatenator<2, 2>("m_axi_concat_rready");
  mp_m_axi_concat_rready->in_port[0](m_axi_concat_rready_out_0);
  mp_m_axi_concat_rready->out_port(m_axi_rready);
    mp_m_axi_concat_rready->offset_port(0, 0);
  mp_m_axi_concat_awaddr->in_port[1](m_axi_concat_awaddr_out_1);
  mp_m_axi_concat_awaddr->offset_port(1, 32);
  mp_m_axi_concat_awprot->in_port[1](m_axi_concat_awprot_out_1);
  mp_m_axi_concat_awprot->offset_port(1, 3);
  mp_m_axi_concat_awvalid->in_port[1](m_axi_concat_awvalid_out_1);
  mp_m_axi_concat_awvalid->offset_port(1, 1);
  
  mp_m_axi_split_awready->out_port[1](m_axi_split_awready_out_1);
    mp_m_axi_split_awready->add_mask(1,2,1);
  mp_m_axi_concat_wdata->in_port[1](m_axi_concat_wdata_out_1);
  mp_m_axi_concat_wdata->offset_port(1, 32);
  mp_m_axi_concat_wstrb->in_port[1](m_axi_concat_wstrb_out_1);
  mp_m_axi_concat_wstrb->offset_port(1, 4);
  mp_m_axi_concat_wvalid->in_port[1](m_axi_concat_wvalid_out_1);
  mp_m_axi_concat_wvalid->offset_port(1, 1);
  
  mp_m_axi_split_wready->out_port[1](m_axi_split_wready_out_1);
    mp_m_axi_split_wready->add_mask(1,2,1);
  
  mp_m_axi_split_bresp->out_port[1](m_axi_split_bresp_out_1);
    mp_m_axi_split_bresp->add_mask(1,4,2);
  
  mp_m_axi_split_bvalid->out_port[1](m_axi_split_bvalid_out_1);
    mp_m_axi_split_bvalid->add_mask(1,2,1);
  mp_m_axi_concat_bready->in_port[1](m_axi_concat_bready_out_1);
  mp_m_axi_concat_bready->offset_port(1, 1);
  mp_m_axi_concat_araddr->in_port[1](m_axi_concat_araddr_out_1);
  mp_m_axi_concat_araddr->offset_port(1, 32);
  mp_m_axi_concat_arprot->in_port[1](m_axi_concat_arprot_out_1);
  mp_m_axi_concat_arprot->offset_port(1, 3);
  mp_m_axi_concat_arvalid->in_port[1](m_axi_concat_arvalid_out_1);
  mp_m_axi_concat_arvalid->offset_port(1, 1);
  
  mp_m_axi_split_arready->out_port[1](m_axi_split_arready_out_1);
    mp_m_axi_split_arready->add_mask(1,2,1);
  
  mp_m_axi_split_rdata->out_port[1](m_axi_split_rdata_out_1);
    mp_m_axi_split_rdata->add_mask(1,64,32);
  
  mp_m_axi_split_rresp->out_port[1](m_axi_split_rresp_out_1);
    mp_m_axi_split_rresp->add_mask(1,4,2);
  
  mp_m_axi_split_rvalid->out_port[1](m_axi_split_rvalid_out_1);
    mp_m_axi_split_rvalid->add_mask(1,2,1);
  mp_m_axi_concat_rready->in_port[1](m_axi_concat_rready_out_1);
  mp_m_axi_concat_rready->offset_port(1, 1);

  // initialize socket stubs

}

void cl_sda_axil_xbar::before_end_of_elaboration()
{
  // configure 'S00_AXI' transactor

  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_sda_axil_xbar", "S00_AXI_TLM_MODE") != 1)
  {
    // Instantiate Socket Stubs

  // 'S00_AXI' transactor parameters
    xsc::common_cpp::properties S00_AXI_transactor_param_props;
    S00_AXI_transactor_param_props.addLong("DATA_WIDTH", "32");
    S00_AXI_transactor_param_props.addLong("FREQ_HZ", "100000000");
    S00_AXI_transactor_param_props.addLong("ID_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("ADDR_WIDTH", "32");
    S00_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("HAS_BURST", "0");
    S00_AXI_transactor_param_props.addLong("HAS_LOCK", "0");
    S00_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    S00_AXI_transactor_param_props.addLong("HAS_CACHE", "0");
    S00_AXI_transactor_param_props.addLong("HAS_QOS", "0");
    S00_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    S00_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    S00_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    S00_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    S00_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    S00_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    S00_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    S00_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    S00_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    S00_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    S00_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    S00_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    S00_AXI_transactor_param_props.addLong("HAS_SIZE", "0");
    S00_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    S00_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    S00_AXI_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    S00_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    S00_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_S00_AXI_transactor = new xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>("S00_AXI_transactor", S00_AXI_transactor_param_props);

    // S00_AXI' transactor ports

    mp_S00_AXI_transactor->AWADDR(s_axi_awaddr);
    mp_S00_AXI_transactor->AWPROT(s_axi_awprot);
    mp_s_axi_awvalid_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_awvalid_converter");
    mp_s_axi_awvalid_converter->vector_in(s_axi_awvalid);
    mp_s_axi_awvalid_converter->scalar_out(m_s_axi_awvalid_converter_signal);
    mp_S00_AXI_transactor->AWVALID(m_s_axi_awvalid_converter_signal);
    mp_s_axi_awready_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_awready_converter");
    mp_s_axi_awready_converter->scalar_in(m_s_axi_awready_converter_signal);
    mp_s_axi_awready_converter->vector_out(s_axi_awready);
    mp_S00_AXI_transactor->AWREADY(m_s_axi_awready_converter_signal);
    mp_S00_AXI_transactor->WDATA(s_axi_wdata);
    mp_S00_AXI_transactor->WSTRB(s_axi_wstrb);
    mp_s_axi_wvalid_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_wvalid_converter");
    mp_s_axi_wvalid_converter->vector_in(s_axi_wvalid);
    mp_s_axi_wvalid_converter->scalar_out(m_s_axi_wvalid_converter_signal);
    mp_S00_AXI_transactor->WVALID(m_s_axi_wvalid_converter_signal);
    mp_s_axi_wready_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_wready_converter");
    mp_s_axi_wready_converter->scalar_in(m_s_axi_wready_converter_signal);
    mp_s_axi_wready_converter->vector_out(s_axi_wready);
    mp_S00_AXI_transactor->WREADY(m_s_axi_wready_converter_signal);
    mp_S00_AXI_transactor->BRESP(s_axi_bresp);
    mp_s_axi_bvalid_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_bvalid_converter");
    mp_s_axi_bvalid_converter->scalar_in(m_s_axi_bvalid_converter_signal);
    mp_s_axi_bvalid_converter->vector_out(s_axi_bvalid);
    mp_S00_AXI_transactor->BVALID(m_s_axi_bvalid_converter_signal);
    mp_s_axi_bready_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_bready_converter");
    mp_s_axi_bready_converter->vector_in(s_axi_bready);
    mp_s_axi_bready_converter->scalar_out(m_s_axi_bready_converter_signal);
    mp_S00_AXI_transactor->BREADY(m_s_axi_bready_converter_signal);
    mp_S00_AXI_transactor->ARADDR(s_axi_araddr);
    mp_S00_AXI_transactor->ARPROT(s_axi_arprot);
    mp_s_axi_arvalid_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_arvalid_converter");
    mp_s_axi_arvalid_converter->vector_in(s_axi_arvalid);
    mp_s_axi_arvalid_converter->scalar_out(m_s_axi_arvalid_converter_signal);
    mp_S00_AXI_transactor->ARVALID(m_s_axi_arvalid_converter_signal);
    mp_s_axi_arready_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_arready_converter");
    mp_s_axi_arready_converter->scalar_in(m_s_axi_arready_converter_signal);
    mp_s_axi_arready_converter->vector_out(s_axi_arready);
    mp_S00_AXI_transactor->ARREADY(m_s_axi_arready_converter_signal);
    mp_S00_AXI_transactor->RDATA(s_axi_rdata);
    mp_S00_AXI_transactor->RRESP(s_axi_rresp);
    mp_s_axi_rvalid_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_rvalid_converter");
    mp_s_axi_rvalid_converter->scalar_in(m_s_axi_rvalid_converter_signal);
    mp_s_axi_rvalid_converter->vector_out(s_axi_rvalid);
    mp_S00_AXI_transactor->RVALID(m_s_axi_rvalid_converter_signal);
    mp_s_axi_rready_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_rready_converter");
    mp_s_axi_rready_converter->vector_in(s_axi_rready);
    mp_s_axi_rready_converter->scalar_out(m_s_axi_rready_converter_signal);
    mp_S00_AXI_transactor->RREADY(m_s_axi_rready_converter_signal);
    mp_S00_AXI_transactor->CLK(aclk);
    mp_S00_AXI_transactor->RST(aresetn);

    // S00_AXI' transactor sockets

    mp_impl->target_0_rd_socket->bind(*(mp_S00_AXI_transactor->rd_socket));
    mp_impl->target_0_wr_socket->bind(*(mp_S00_AXI_transactor->wr_socket));
  }
  else
  {
  }

  // configure 'M00_AXI' transactor

  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_sda_axil_xbar", "M00_AXI_TLM_MODE") != 1)
  {
    // Instantiate Socket Stubs

  // 'M00_AXI' transactor parameters
    xsc::common_cpp::properties M00_AXI_transactor_param_props;
    M00_AXI_transactor_param_props.addLong("DATA_WIDTH", "32");
    M00_AXI_transactor_param_props.addLong("FREQ_HZ", "100000000");
    M00_AXI_transactor_param_props.addLong("ID_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("ADDR_WIDTH", "32");
    M00_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("HAS_BURST", "0");
    M00_AXI_transactor_param_props.addLong("HAS_LOCK", "0");
    M00_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    M00_AXI_transactor_param_props.addLong("HAS_CACHE", "0");
    M00_AXI_transactor_param_props.addLong("HAS_QOS", "0");
    M00_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    M00_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    M00_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    M00_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    M00_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    M00_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    M00_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    M00_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    M00_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    M00_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    M00_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    M00_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    M00_AXI_transactor_param_props.addLong("HAS_SIZE", "0");
    M00_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    M00_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    M00_AXI_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    M00_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    M00_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_M00_AXI_transactor = new xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>("M00_AXI_transactor", M00_AXI_transactor_param_props);

    // M00_AXI' transactor ports

    mp_m_axi_awaddr_converter_0 = new xsc::common::vector2vector_converter<32,64>("m_axi_awaddr_converter_0");
    mp_m_axi_awaddr_converter_0->vector_in(m_m_axi_awaddr_converter_0_signal);
    mp_m_axi_awaddr_converter_0->vector_out(m_axi_concat_awaddr_out_0);
    mp_M00_AXI_transactor->AWADDR(m_m_axi_awaddr_converter_0_signal);
    mp_m_axi_awprot_converter_0 = new xsc::common::vector2vector_converter<3,6>("m_axi_awprot_converter_0");
    mp_m_axi_awprot_converter_0->vector_in(m_m_axi_awprot_converter_0_signal);
    mp_m_axi_awprot_converter_0->vector_out(m_axi_concat_awprot_out_0);
    mp_M00_AXI_transactor->AWPROT(m_m_axi_awprot_converter_0_signal);
    mp_m_axi_awvalid_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_awvalid_converter_0");
    mp_m_axi_awvalid_converter_0->scalar_in(m_m_axi_awvalid_converter_0_signal);
    mp_m_axi_awvalid_converter_0->vector_out(m_axi_concat_awvalid_out_0);
    mp_M00_AXI_transactor->AWVALID(m_m_axi_awvalid_converter_0_signal);
    mp_m_axi_awready_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_awready_converter_0");
    mp_m_axi_awready_converter_0->vector_in(m_axi_split_awready_out_0);
    mp_m_axi_awready_converter_0->scalar_out(m_m_axi_awready_converter_0_signal);
    mp_M00_AXI_transactor->AWREADY(m_m_axi_awready_converter_0_signal);
    mp_m_axi_wdata_converter_0 = new xsc::common::vector2vector_converter<32,64>("m_axi_wdata_converter_0");
    mp_m_axi_wdata_converter_0->vector_in(m_m_axi_wdata_converter_0_signal);
    mp_m_axi_wdata_converter_0->vector_out(m_axi_concat_wdata_out_0);
    mp_M00_AXI_transactor->WDATA(m_m_axi_wdata_converter_0_signal);
    mp_m_axi_wstrb_converter_0 = new xsc::common::vector2vector_converter<4,8>("m_axi_wstrb_converter_0");
    mp_m_axi_wstrb_converter_0->vector_in(m_m_axi_wstrb_converter_0_signal);
    mp_m_axi_wstrb_converter_0->vector_out(m_axi_concat_wstrb_out_0);
    mp_M00_AXI_transactor->WSTRB(m_m_axi_wstrb_converter_0_signal);
    mp_m_axi_wvalid_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_wvalid_converter_0");
    mp_m_axi_wvalid_converter_0->scalar_in(m_m_axi_wvalid_converter_0_signal);
    mp_m_axi_wvalid_converter_0->vector_out(m_axi_concat_wvalid_out_0);
    mp_M00_AXI_transactor->WVALID(m_m_axi_wvalid_converter_0_signal);
    mp_m_axi_wready_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_wready_converter_0");
    mp_m_axi_wready_converter_0->vector_in(m_axi_split_wready_out_0);
    mp_m_axi_wready_converter_0->scalar_out(m_m_axi_wready_converter_0_signal);
    mp_M00_AXI_transactor->WREADY(m_m_axi_wready_converter_0_signal);
    mp_m_axi_bresp_converter_0 = new xsc::common::vector2vector_converter<4,2>("m_axi_bresp_converter_0");
    mp_m_axi_bresp_converter_0->vector_in(m_axi_split_bresp_out_0);
    mp_m_axi_bresp_converter_0->vector_out(m_m_axi_bresp_converter_0_signal);
    mp_M00_AXI_transactor->BRESP(m_m_axi_bresp_converter_0_signal);
    mp_m_axi_bvalid_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_bvalid_converter_0");
    mp_m_axi_bvalid_converter_0->vector_in(m_axi_split_bvalid_out_0);
    mp_m_axi_bvalid_converter_0->scalar_out(m_m_axi_bvalid_converter_0_signal);
    mp_M00_AXI_transactor->BVALID(m_m_axi_bvalid_converter_0_signal);
    mp_m_axi_bready_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_bready_converter_0");
    mp_m_axi_bready_converter_0->scalar_in(m_m_axi_bready_converter_0_signal);
    mp_m_axi_bready_converter_0->vector_out(m_axi_concat_bready_out_0);
    mp_M00_AXI_transactor->BREADY(m_m_axi_bready_converter_0_signal);
    mp_m_axi_araddr_converter_0 = new xsc::common::vector2vector_converter<32,64>("m_axi_araddr_converter_0");
    mp_m_axi_araddr_converter_0->vector_in(m_m_axi_araddr_converter_0_signal);
    mp_m_axi_araddr_converter_0->vector_out(m_axi_concat_araddr_out_0);
    mp_M00_AXI_transactor->ARADDR(m_m_axi_araddr_converter_0_signal);
    mp_m_axi_arprot_converter_0 = new xsc::common::vector2vector_converter<3,6>("m_axi_arprot_converter_0");
    mp_m_axi_arprot_converter_0->vector_in(m_m_axi_arprot_converter_0_signal);
    mp_m_axi_arprot_converter_0->vector_out(m_axi_concat_arprot_out_0);
    mp_M00_AXI_transactor->ARPROT(m_m_axi_arprot_converter_0_signal);
    mp_m_axi_arvalid_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_arvalid_converter_0");
    mp_m_axi_arvalid_converter_0->scalar_in(m_m_axi_arvalid_converter_0_signal);
    mp_m_axi_arvalid_converter_0->vector_out(m_axi_concat_arvalid_out_0);
    mp_M00_AXI_transactor->ARVALID(m_m_axi_arvalid_converter_0_signal);
    mp_m_axi_arready_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_arready_converter_0");
    mp_m_axi_arready_converter_0->vector_in(m_axi_split_arready_out_0);
    mp_m_axi_arready_converter_0->scalar_out(m_m_axi_arready_converter_0_signal);
    mp_M00_AXI_transactor->ARREADY(m_m_axi_arready_converter_0_signal);
    mp_m_axi_rdata_converter_0 = new xsc::common::vector2vector_converter<64,32>("m_axi_rdata_converter_0");
    mp_m_axi_rdata_converter_0->vector_in(m_axi_split_rdata_out_0);
    mp_m_axi_rdata_converter_0->vector_out(m_m_axi_rdata_converter_0_signal);
    mp_M00_AXI_transactor->RDATA(m_m_axi_rdata_converter_0_signal);
    mp_m_axi_rresp_converter_0 = new xsc::common::vector2vector_converter<4,2>("m_axi_rresp_converter_0");
    mp_m_axi_rresp_converter_0->vector_in(m_axi_split_rresp_out_0);
    mp_m_axi_rresp_converter_0->vector_out(m_m_axi_rresp_converter_0_signal);
    mp_M00_AXI_transactor->RRESP(m_m_axi_rresp_converter_0_signal);
    mp_m_axi_rvalid_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_rvalid_converter_0");
    mp_m_axi_rvalid_converter_0->vector_in(m_axi_split_rvalid_out_0);
    mp_m_axi_rvalid_converter_0->scalar_out(m_m_axi_rvalid_converter_0_signal);
    mp_M00_AXI_transactor->RVALID(m_m_axi_rvalid_converter_0_signal);
    mp_m_axi_rready_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_rready_converter_0");
    mp_m_axi_rready_converter_0->scalar_in(m_m_axi_rready_converter_0_signal);
    mp_m_axi_rready_converter_0->vector_out(m_axi_concat_rready_out_0);
    mp_M00_AXI_transactor->RREADY(m_m_axi_rready_converter_0_signal);
    mp_M00_AXI_transactor->CLK(aclk);
    mp_M00_AXI_transactor->RST(aresetn);

    // M00_AXI' transactor sockets

    mp_impl->initiator_0_rd_socket->bind(*(mp_M00_AXI_transactor->rd_socket));
    mp_impl->initiator_0_wr_socket->bind(*(mp_M00_AXI_transactor->wr_socket));
  }
  else
  {
  }

  // configure 'M01_AXI' transactor

  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_sda_axil_xbar", "M01_AXI_TLM_MODE") != 1)
  {
    // Instantiate Socket Stubs

  // 'M01_AXI' transactor parameters
    xsc::common_cpp::properties M01_AXI_transactor_param_props;
    M01_AXI_transactor_param_props.addLong("DATA_WIDTH", "32");
    M01_AXI_transactor_param_props.addLong("FREQ_HZ", "100000000");
    M01_AXI_transactor_param_props.addLong("ID_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("ADDR_WIDTH", "32");
    M01_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("HAS_BURST", "0");
    M01_AXI_transactor_param_props.addLong("HAS_LOCK", "0");
    M01_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    M01_AXI_transactor_param_props.addLong("HAS_CACHE", "0");
    M01_AXI_transactor_param_props.addLong("HAS_QOS", "0");
    M01_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    M01_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    M01_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    M01_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    M01_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    M01_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    M01_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    M01_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    M01_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    M01_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    M01_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    M01_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    M01_AXI_transactor_param_props.addLong("HAS_SIZE", "0");
    M01_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    M01_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    M01_AXI_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    M01_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    M01_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_M01_AXI_transactor = new xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>("M01_AXI_transactor", M01_AXI_transactor_param_props);

    // M01_AXI' transactor ports

    mp_m_axi_awaddr_converter_1 = new xsc::common::vector2vector_converter<32,64>("m_axi_awaddr_converter_1");
    mp_m_axi_awaddr_converter_1->vector_in(m_m_axi_awaddr_converter_1_signal);
    mp_m_axi_awaddr_converter_1->vector_out(m_axi_concat_awaddr_out_1);
    mp_M01_AXI_transactor->AWADDR(m_m_axi_awaddr_converter_1_signal);
    mp_m_axi_awprot_converter_1 = new xsc::common::vector2vector_converter<3,6>("m_axi_awprot_converter_1");
    mp_m_axi_awprot_converter_1->vector_in(m_m_axi_awprot_converter_1_signal);
    mp_m_axi_awprot_converter_1->vector_out(m_axi_concat_awprot_out_1);
    mp_M01_AXI_transactor->AWPROT(m_m_axi_awprot_converter_1_signal);
    mp_m_axi_awvalid_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_awvalid_converter_1");
    mp_m_axi_awvalid_converter_1->scalar_in(m_m_axi_awvalid_converter_1_signal);
    mp_m_axi_awvalid_converter_1->vector_out(m_axi_concat_awvalid_out_1);
    mp_M01_AXI_transactor->AWVALID(m_m_axi_awvalid_converter_1_signal);
    mp_m_axi_awready_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_awready_converter_1");
    mp_m_axi_awready_converter_1->vector_in(m_axi_split_awready_out_1);
    mp_m_axi_awready_converter_1->scalar_out(m_m_axi_awready_converter_1_signal);
    mp_M01_AXI_transactor->AWREADY(m_m_axi_awready_converter_1_signal);
    mp_m_axi_wdata_converter_1 = new xsc::common::vector2vector_converter<32,64>("m_axi_wdata_converter_1");
    mp_m_axi_wdata_converter_1->vector_in(m_m_axi_wdata_converter_1_signal);
    mp_m_axi_wdata_converter_1->vector_out(m_axi_concat_wdata_out_1);
    mp_M01_AXI_transactor->WDATA(m_m_axi_wdata_converter_1_signal);
    mp_m_axi_wstrb_converter_1 = new xsc::common::vector2vector_converter<4,8>("m_axi_wstrb_converter_1");
    mp_m_axi_wstrb_converter_1->vector_in(m_m_axi_wstrb_converter_1_signal);
    mp_m_axi_wstrb_converter_1->vector_out(m_axi_concat_wstrb_out_1);
    mp_M01_AXI_transactor->WSTRB(m_m_axi_wstrb_converter_1_signal);
    mp_m_axi_wvalid_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_wvalid_converter_1");
    mp_m_axi_wvalid_converter_1->scalar_in(m_m_axi_wvalid_converter_1_signal);
    mp_m_axi_wvalid_converter_1->vector_out(m_axi_concat_wvalid_out_1);
    mp_M01_AXI_transactor->WVALID(m_m_axi_wvalid_converter_1_signal);
    mp_m_axi_wready_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_wready_converter_1");
    mp_m_axi_wready_converter_1->vector_in(m_axi_split_wready_out_1);
    mp_m_axi_wready_converter_1->scalar_out(m_m_axi_wready_converter_1_signal);
    mp_M01_AXI_transactor->WREADY(m_m_axi_wready_converter_1_signal);
    mp_m_axi_bresp_converter_1 = new xsc::common::vector2vector_converter<4,2>("m_axi_bresp_converter_1");
    mp_m_axi_bresp_converter_1->vector_in(m_axi_split_bresp_out_1);
    mp_m_axi_bresp_converter_1->vector_out(m_m_axi_bresp_converter_1_signal);
    mp_M01_AXI_transactor->BRESP(m_m_axi_bresp_converter_1_signal);
    mp_m_axi_bvalid_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_bvalid_converter_1");
    mp_m_axi_bvalid_converter_1->vector_in(m_axi_split_bvalid_out_1);
    mp_m_axi_bvalid_converter_1->scalar_out(m_m_axi_bvalid_converter_1_signal);
    mp_M01_AXI_transactor->BVALID(m_m_axi_bvalid_converter_1_signal);
    mp_m_axi_bready_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_bready_converter_1");
    mp_m_axi_bready_converter_1->scalar_in(m_m_axi_bready_converter_1_signal);
    mp_m_axi_bready_converter_1->vector_out(m_axi_concat_bready_out_1);
    mp_M01_AXI_transactor->BREADY(m_m_axi_bready_converter_1_signal);
    mp_m_axi_araddr_converter_1 = new xsc::common::vector2vector_converter<32,64>("m_axi_araddr_converter_1");
    mp_m_axi_araddr_converter_1->vector_in(m_m_axi_araddr_converter_1_signal);
    mp_m_axi_araddr_converter_1->vector_out(m_axi_concat_araddr_out_1);
    mp_M01_AXI_transactor->ARADDR(m_m_axi_araddr_converter_1_signal);
    mp_m_axi_arprot_converter_1 = new xsc::common::vector2vector_converter<3,6>("m_axi_arprot_converter_1");
    mp_m_axi_arprot_converter_1->vector_in(m_m_axi_arprot_converter_1_signal);
    mp_m_axi_arprot_converter_1->vector_out(m_axi_concat_arprot_out_1);
    mp_M01_AXI_transactor->ARPROT(m_m_axi_arprot_converter_1_signal);
    mp_m_axi_arvalid_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_arvalid_converter_1");
    mp_m_axi_arvalid_converter_1->scalar_in(m_m_axi_arvalid_converter_1_signal);
    mp_m_axi_arvalid_converter_1->vector_out(m_axi_concat_arvalid_out_1);
    mp_M01_AXI_transactor->ARVALID(m_m_axi_arvalid_converter_1_signal);
    mp_m_axi_arready_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_arready_converter_1");
    mp_m_axi_arready_converter_1->vector_in(m_axi_split_arready_out_1);
    mp_m_axi_arready_converter_1->scalar_out(m_m_axi_arready_converter_1_signal);
    mp_M01_AXI_transactor->ARREADY(m_m_axi_arready_converter_1_signal);
    mp_m_axi_rdata_converter_1 = new xsc::common::vector2vector_converter<64,32>("m_axi_rdata_converter_1");
    mp_m_axi_rdata_converter_1->vector_in(m_axi_split_rdata_out_1);
    mp_m_axi_rdata_converter_1->vector_out(m_m_axi_rdata_converter_1_signal);
    mp_M01_AXI_transactor->RDATA(m_m_axi_rdata_converter_1_signal);
    mp_m_axi_rresp_converter_1 = new xsc::common::vector2vector_converter<4,2>("m_axi_rresp_converter_1");
    mp_m_axi_rresp_converter_1->vector_in(m_axi_split_rresp_out_1);
    mp_m_axi_rresp_converter_1->vector_out(m_m_axi_rresp_converter_1_signal);
    mp_M01_AXI_transactor->RRESP(m_m_axi_rresp_converter_1_signal);
    mp_m_axi_rvalid_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_rvalid_converter_1");
    mp_m_axi_rvalid_converter_1->vector_in(m_axi_split_rvalid_out_1);
    mp_m_axi_rvalid_converter_1->scalar_out(m_m_axi_rvalid_converter_1_signal);
    mp_M01_AXI_transactor->RVALID(m_m_axi_rvalid_converter_1_signal);
    mp_m_axi_rready_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_rready_converter_1");
    mp_m_axi_rready_converter_1->scalar_in(m_m_axi_rready_converter_1_signal);
    mp_m_axi_rready_converter_1->vector_out(m_axi_concat_rready_out_1);
    mp_M01_AXI_transactor->RREADY(m_m_axi_rready_converter_1_signal);
    mp_M01_AXI_transactor->CLK(aclk);
    mp_M01_AXI_transactor->RST(aresetn);

    // M01_AXI' transactor sockets

    mp_impl->initiator_1_rd_socket->bind(*(mp_M01_AXI_transactor->rd_socket));
    mp_impl->initiator_1_wr_socket->bind(*(mp_M01_AXI_transactor->wr_socket));
  }
  else
  {
  }

}

#endif // XILINX_SIMULATOR




#ifdef XM_SYSTEMC
cl_sda_axil_xbar::cl_sda_axil_xbar(const sc_core::sc_module_name& nm) : cl_sda_axil_xbar_sc(nm), aclk("aclk"), aresetn("aresetn"), s_axi_awaddr("s_axi_awaddr"), s_axi_awprot("s_axi_awprot"), s_axi_awvalid("s_axi_awvalid"), s_axi_awready("s_axi_awready"), s_axi_wdata("s_axi_wdata"), s_axi_wstrb("s_axi_wstrb"), s_axi_wvalid("s_axi_wvalid"), s_axi_wready("s_axi_wready"), s_axi_bresp("s_axi_bresp"), s_axi_bvalid("s_axi_bvalid"), s_axi_bready("s_axi_bready"), s_axi_araddr("s_axi_araddr"), s_axi_arprot("s_axi_arprot"), s_axi_arvalid("s_axi_arvalid"), s_axi_arready("s_axi_arready"), s_axi_rdata("s_axi_rdata"), s_axi_rresp("s_axi_rresp"), s_axi_rvalid("s_axi_rvalid"), s_axi_rready("s_axi_rready"), m_axi_awaddr("m_axi_awaddr"), m_axi_awprot("m_axi_awprot"), m_axi_awvalid("m_axi_awvalid"), m_axi_awready("m_axi_awready"), m_axi_wdata("m_axi_wdata"), m_axi_wstrb("m_axi_wstrb"), m_axi_wvalid("m_axi_wvalid"), m_axi_wready("m_axi_wready"), m_axi_bresp("m_axi_bresp"), m_axi_bvalid("m_axi_bvalid"), m_axi_bready("m_axi_bready"), m_axi_araddr("m_axi_araddr"), m_axi_arprot("m_axi_arprot"), m_axi_arvalid("m_axi_arvalid"), m_axi_arready("m_axi_arready"), m_axi_rdata("m_axi_rdata"), m_axi_rresp("m_axi_rresp"), m_axi_rvalid("m_axi_rvalid"), m_axi_rready("m_axi_rready")
{

  // initialize pins
  mp_impl->aclk(aclk);
  mp_impl->aresetn(aresetn);

  // initialize transactors
  mp_S00_AXI_transactor = NULL;
  mp_s_axi_awvalid_converter = NULL;
  mp_s_axi_awready_converter = NULL;
  mp_s_axi_wvalid_converter = NULL;
  mp_s_axi_wready_converter = NULL;
  mp_s_axi_bvalid_converter = NULL;
  mp_s_axi_bready_converter = NULL;
  mp_s_axi_arvalid_converter = NULL;
  mp_s_axi_arready_converter = NULL;
  mp_s_axi_rvalid_converter = NULL;
  mp_s_axi_rready_converter = NULL;
  mp_M00_AXI_transactor = NULL;
  mp_m_axi_awaddr_converter_0 = NULL;
  mp_m_axi_awprot_converter_0 = NULL;
  mp_m_axi_awvalid_converter_0 = NULL;
  mp_m_axi_awready_converter_0 = NULL;
  mp_m_axi_wdata_converter_0 = NULL;
  mp_m_axi_wstrb_converter_0 = NULL;
  mp_m_axi_wvalid_converter_0 = NULL;
  mp_m_axi_wready_converter_0 = NULL;
  mp_m_axi_bresp_converter_0 = NULL;
  mp_m_axi_bvalid_converter_0 = NULL;
  mp_m_axi_bready_converter_0 = NULL;
  mp_m_axi_araddr_converter_0 = NULL;
  mp_m_axi_arprot_converter_0 = NULL;
  mp_m_axi_arvalid_converter_0 = NULL;
  mp_m_axi_arready_converter_0 = NULL;
  mp_m_axi_rdata_converter_0 = NULL;
  mp_m_axi_rresp_converter_0 = NULL;
  mp_m_axi_rvalid_converter_0 = NULL;
  mp_m_axi_rready_converter_0 = NULL;
  mp_M01_AXI_transactor = NULL;
  mp_m_axi_awaddr_converter_1 = NULL;
  mp_m_axi_awprot_converter_1 = NULL;
  mp_m_axi_awvalid_converter_1 = NULL;
  mp_m_axi_awready_converter_1 = NULL;
  mp_m_axi_wdata_converter_1 = NULL;
  mp_m_axi_wstrb_converter_1 = NULL;
  mp_m_axi_wvalid_converter_1 = NULL;
  mp_m_axi_wready_converter_1 = NULL;
  mp_m_axi_bresp_converter_1 = NULL;
  mp_m_axi_bvalid_converter_1 = NULL;
  mp_m_axi_bready_converter_1 = NULL;
  mp_m_axi_araddr_converter_1 = NULL;
  mp_m_axi_arprot_converter_1 = NULL;
  mp_m_axi_arvalid_converter_1 = NULL;
  mp_m_axi_arready_converter_1 = NULL;
  mp_m_axi_rdata_converter_1 = NULL;
  mp_m_axi_rresp_converter_1 = NULL;
  mp_m_axi_rvalid_converter_1 = NULL;
  mp_m_axi_rready_converter_1 = NULL;

  // initialize junctures
  mp_m_axi_concat_araddr = NULL;
  mp_m_axi_concat_arprot = NULL;
  mp_m_axi_concat_arvalid = NULL;
  mp_m_axi_concat_awaddr = NULL;
  mp_m_axi_concat_awprot = NULL;
  mp_m_axi_concat_awvalid = NULL;
  mp_m_axi_concat_bready = NULL;
  mp_m_axi_concat_rready = NULL;
  mp_m_axi_concat_wdata = NULL;
  mp_m_axi_concat_wstrb = NULL;
  mp_m_axi_concat_wvalid = NULL;
  mp_m_axi_split_arready = NULL;
  mp_m_axi_split_awready = NULL;
  mp_m_axi_split_bresp = NULL;
  mp_m_axi_split_bvalid = NULL;
  mp_m_axi_split_rdata = NULL;
  mp_m_axi_split_rresp = NULL;
  mp_m_axi_split_rvalid = NULL;
  mp_m_axi_split_wready = NULL;
  mp_m_axi_concat_awaddr = new xsc::xsc_concatenator<64, 2>("m_axi_concat_awaddr");
  mp_m_axi_concat_awaddr->in_port[0](m_axi_concat_awaddr_out_0);
  mp_m_axi_concat_awaddr->out_port(m_axi_awaddr);
    mp_m_axi_concat_awaddr->offset_port(0, 0);
  mp_m_axi_concat_awprot = new xsc::xsc_concatenator<6, 2>("m_axi_concat_awprot");
  mp_m_axi_concat_awprot->in_port[0](m_axi_concat_awprot_out_0);
  mp_m_axi_concat_awprot->out_port(m_axi_awprot);
    mp_m_axi_concat_awprot->offset_port(0, 0);
  mp_m_axi_concat_awvalid = new xsc::xsc_concatenator<2, 2>("m_axi_concat_awvalid");
  mp_m_axi_concat_awvalid->in_port[0](m_axi_concat_awvalid_out_0);
  mp_m_axi_concat_awvalid->out_port(m_axi_awvalid);
    mp_m_axi_concat_awvalid->offset_port(0, 0);
  mp_m_axi_split_awready = new xsc::xsc_split<2, 2>("m_axi_split_awready");
  mp_m_axi_split_awready->in_port(m_axi_awready);
  mp_m_axi_split_awready->out_port[0](m_axi_split_awready_out_0);
    mp_m_axi_split_awready->add_mask(0,1,0);
  mp_m_axi_concat_wdata = new xsc::xsc_concatenator<64, 2>("m_axi_concat_wdata");
  mp_m_axi_concat_wdata->in_port[0](m_axi_concat_wdata_out_0);
  mp_m_axi_concat_wdata->out_port(m_axi_wdata);
    mp_m_axi_concat_wdata->offset_port(0, 0);
  mp_m_axi_concat_wstrb = new xsc::xsc_concatenator<8, 2>("m_axi_concat_wstrb");
  mp_m_axi_concat_wstrb->in_port[0](m_axi_concat_wstrb_out_0);
  mp_m_axi_concat_wstrb->out_port(m_axi_wstrb);
    mp_m_axi_concat_wstrb->offset_port(0, 0);
  mp_m_axi_concat_wvalid = new xsc::xsc_concatenator<2, 2>("m_axi_concat_wvalid");
  mp_m_axi_concat_wvalid->in_port[0](m_axi_concat_wvalid_out_0);
  mp_m_axi_concat_wvalid->out_port(m_axi_wvalid);
    mp_m_axi_concat_wvalid->offset_port(0, 0);
  mp_m_axi_split_wready = new xsc::xsc_split<2, 2>("m_axi_split_wready");
  mp_m_axi_split_wready->in_port(m_axi_wready);
  mp_m_axi_split_wready->out_port[0](m_axi_split_wready_out_0);
    mp_m_axi_split_wready->add_mask(0,1,0);
  mp_m_axi_split_bresp = new xsc::xsc_split<4, 2>("m_axi_split_bresp");
  mp_m_axi_split_bresp->in_port(m_axi_bresp);
  mp_m_axi_split_bresp->out_port[0](m_axi_split_bresp_out_0);
    mp_m_axi_split_bresp->add_mask(0,2,0);
  mp_m_axi_split_bvalid = new xsc::xsc_split<2, 2>("m_axi_split_bvalid");
  mp_m_axi_split_bvalid->in_port(m_axi_bvalid);
  mp_m_axi_split_bvalid->out_port[0](m_axi_split_bvalid_out_0);
    mp_m_axi_split_bvalid->add_mask(0,1,0);
  mp_m_axi_concat_bready = new xsc::xsc_concatenator<2, 2>("m_axi_concat_bready");
  mp_m_axi_concat_bready->in_port[0](m_axi_concat_bready_out_0);
  mp_m_axi_concat_bready->out_port(m_axi_bready);
    mp_m_axi_concat_bready->offset_port(0, 0);
  mp_m_axi_concat_araddr = new xsc::xsc_concatenator<64, 2>("m_axi_concat_araddr");
  mp_m_axi_concat_araddr->in_port[0](m_axi_concat_araddr_out_0);
  mp_m_axi_concat_araddr->out_port(m_axi_araddr);
    mp_m_axi_concat_araddr->offset_port(0, 0);
  mp_m_axi_concat_arprot = new xsc::xsc_concatenator<6, 2>("m_axi_concat_arprot");
  mp_m_axi_concat_arprot->in_port[0](m_axi_concat_arprot_out_0);
  mp_m_axi_concat_arprot->out_port(m_axi_arprot);
    mp_m_axi_concat_arprot->offset_port(0, 0);
  mp_m_axi_concat_arvalid = new xsc::xsc_concatenator<2, 2>("m_axi_concat_arvalid");
  mp_m_axi_concat_arvalid->in_port[0](m_axi_concat_arvalid_out_0);
  mp_m_axi_concat_arvalid->out_port(m_axi_arvalid);
    mp_m_axi_concat_arvalid->offset_port(0, 0);
  mp_m_axi_split_arready = new xsc::xsc_split<2, 2>("m_axi_split_arready");
  mp_m_axi_split_arready->in_port(m_axi_arready);
  mp_m_axi_split_arready->out_port[0](m_axi_split_arready_out_0);
    mp_m_axi_split_arready->add_mask(0,1,0);
  mp_m_axi_split_rdata = new xsc::xsc_split<64, 2>("m_axi_split_rdata");
  mp_m_axi_split_rdata->in_port(m_axi_rdata);
  mp_m_axi_split_rdata->out_port[0](m_axi_split_rdata_out_0);
    mp_m_axi_split_rdata->add_mask(0,32,0);
  mp_m_axi_split_rresp = new xsc::xsc_split<4, 2>("m_axi_split_rresp");
  mp_m_axi_split_rresp->in_port(m_axi_rresp);
  mp_m_axi_split_rresp->out_port[0](m_axi_split_rresp_out_0);
    mp_m_axi_split_rresp->add_mask(0,2,0);
  mp_m_axi_split_rvalid = new xsc::xsc_split<2, 2>("m_axi_split_rvalid");
  mp_m_axi_split_rvalid->in_port(m_axi_rvalid);
  mp_m_axi_split_rvalid->out_port[0](m_axi_split_rvalid_out_0);
    mp_m_axi_split_rvalid->add_mask(0,1,0);
  mp_m_axi_concat_rready = new xsc::xsc_concatenator<2, 2>("m_axi_concat_rready");
  mp_m_axi_concat_rready->in_port[0](m_axi_concat_rready_out_0);
  mp_m_axi_concat_rready->out_port(m_axi_rready);
    mp_m_axi_concat_rready->offset_port(0, 0);
  mp_m_axi_concat_awaddr->in_port[1](m_axi_concat_awaddr_out_1);
  mp_m_axi_concat_awaddr->offset_port(1, 32);
  mp_m_axi_concat_awprot->in_port[1](m_axi_concat_awprot_out_1);
  mp_m_axi_concat_awprot->offset_port(1, 3);
  mp_m_axi_concat_awvalid->in_port[1](m_axi_concat_awvalid_out_1);
  mp_m_axi_concat_awvalid->offset_port(1, 1);
  
  mp_m_axi_split_awready->out_port[1](m_axi_split_awready_out_1);
    mp_m_axi_split_awready->add_mask(1,2,1);
  mp_m_axi_concat_wdata->in_port[1](m_axi_concat_wdata_out_1);
  mp_m_axi_concat_wdata->offset_port(1, 32);
  mp_m_axi_concat_wstrb->in_port[1](m_axi_concat_wstrb_out_1);
  mp_m_axi_concat_wstrb->offset_port(1, 4);
  mp_m_axi_concat_wvalid->in_port[1](m_axi_concat_wvalid_out_1);
  mp_m_axi_concat_wvalid->offset_port(1, 1);
  
  mp_m_axi_split_wready->out_port[1](m_axi_split_wready_out_1);
    mp_m_axi_split_wready->add_mask(1,2,1);
  
  mp_m_axi_split_bresp->out_port[1](m_axi_split_bresp_out_1);
    mp_m_axi_split_bresp->add_mask(1,4,2);
  
  mp_m_axi_split_bvalid->out_port[1](m_axi_split_bvalid_out_1);
    mp_m_axi_split_bvalid->add_mask(1,2,1);
  mp_m_axi_concat_bready->in_port[1](m_axi_concat_bready_out_1);
  mp_m_axi_concat_bready->offset_port(1, 1);
  mp_m_axi_concat_araddr->in_port[1](m_axi_concat_araddr_out_1);
  mp_m_axi_concat_araddr->offset_port(1, 32);
  mp_m_axi_concat_arprot->in_port[1](m_axi_concat_arprot_out_1);
  mp_m_axi_concat_arprot->offset_port(1, 3);
  mp_m_axi_concat_arvalid->in_port[1](m_axi_concat_arvalid_out_1);
  mp_m_axi_concat_arvalid->offset_port(1, 1);
  
  mp_m_axi_split_arready->out_port[1](m_axi_split_arready_out_1);
    mp_m_axi_split_arready->add_mask(1,2,1);
  
  mp_m_axi_split_rdata->out_port[1](m_axi_split_rdata_out_1);
    mp_m_axi_split_rdata->add_mask(1,64,32);
  
  mp_m_axi_split_rresp->out_port[1](m_axi_split_rresp_out_1);
    mp_m_axi_split_rresp->add_mask(1,4,2);
  
  mp_m_axi_split_rvalid->out_port[1](m_axi_split_rvalid_out_1);
    mp_m_axi_split_rvalid->add_mask(1,2,1);
  mp_m_axi_concat_rready->in_port[1](m_axi_concat_rready_out_1);
  mp_m_axi_concat_rready->offset_port(1, 1);

  // initialize socket stubs

}

void cl_sda_axil_xbar::before_end_of_elaboration()
{
  // configure 'S00_AXI' transactor

  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_sda_axil_xbar", "S00_AXI_TLM_MODE") != 1)
  {
    // Instantiate Socket Stubs

  // 'S00_AXI' transactor parameters
    xsc::common_cpp::properties S00_AXI_transactor_param_props;
    S00_AXI_transactor_param_props.addLong("DATA_WIDTH", "32");
    S00_AXI_transactor_param_props.addLong("FREQ_HZ", "100000000");
    S00_AXI_transactor_param_props.addLong("ID_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("ADDR_WIDTH", "32");
    S00_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("HAS_BURST", "0");
    S00_AXI_transactor_param_props.addLong("HAS_LOCK", "0");
    S00_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    S00_AXI_transactor_param_props.addLong("HAS_CACHE", "0");
    S00_AXI_transactor_param_props.addLong("HAS_QOS", "0");
    S00_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    S00_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    S00_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    S00_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    S00_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    S00_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    S00_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    S00_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    S00_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    S00_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    S00_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    S00_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    S00_AXI_transactor_param_props.addLong("HAS_SIZE", "0");
    S00_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    S00_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    S00_AXI_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    S00_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    S00_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_S00_AXI_transactor = new xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>("S00_AXI_transactor", S00_AXI_transactor_param_props);

    // S00_AXI' transactor ports

    mp_S00_AXI_transactor->AWADDR(s_axi_awaddr);
    mp_S00_AXI_transactor->AWPROT(s_axi_awprot);
    mp_s_axi_awvalid_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_awvalid_converter");
    mp_s_axi_awvalid_converter->vector_in(s_axi_awvalid);
    mp_s_axi_awvalid_converter->scalar_out(m_s_axi_awvalid_converter_signal);
    mp_S00_AXI_transactor->AWVALID(m_s_axi_awvalid_converter_signal);
    mp_s_axi_awready_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_awready_converter");
    mp_s_axi_awready_converter->scalar_in(m_s_axi_awready_converter_signal);
    mp_s_axi_awready_converter->vector_out(s_axi_awready);
    mp_S00_AXI_transactor->AWREADY(m_s_axi_awready_converter_signal);
    mp_S00_AXI_transactor->WDATA(s_axi_wdata);
    mp_S00_AXI_transactor->WSTRB(s_axi_wstrb);
    mp_s_axi_wvalid_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_wvalid_converter");
    mp_s_axi_wvalid_converter->vector_in(s_axi_wvalid);
    mp_s_axi_wvalid_converter->scalar_out(m_s_axi_wvalid_converter_signal);
    mp_S00_AXI_transactor->WVALID(m_s_axi_wvalid_converter_signal);
    mp_s_axi_wready_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_wready_converter");
    mp_s_axi_wready_converter->scalar_in(m_s_axi_wready_converter_signal);
    mp_s_axi_wready_converter->vector_out(s_axi_wready);
    mp_S00_AXI_transactor->WREADY(m_s_axi_wready_converter_signal);
    mp_S00_AXI_transactor->BRESP(s_axi_bresp);
    mp_s_axi_bvalid_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_bvalid_converter");
    mp_s_axi_bvalid_converter->scalar_in(m_s_axi_bvalid_converter_signal);
    mp_s_axi_bvalid_converter->vector_out(s_axi_bvalid);
    mp_S00_AXI_transactor->BVALID(m_s_axi_bvalid_converter_signal);
    mp_s_axi_bready_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_bready_converter");
    mp_s_axi_bready_converter->vector_in(s_axi_bready);
    mp_s_axi_bready_converter->scalar_out(m_s_axi_bready_converter_signal);
    mp_S00_AXI_transactor->BREADY(m_s_axi_bready_converter_signal);
    mp_S00_AXI_transactor->ARADDR(s_axi_araddr);
    mp_S00_AXI_transactor->ARPROT(s_axi_arprot);
    mp_s_axi_arvalid_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_arvalid_converter");
    mp_s_axi_arvalid_converter->vector_in(s_axi_arvalid);
    mp_s_axi_arvalid_converter->scalar_out(m_s_axi_arvalid_converter_signal);
    mp_S00_AXI_transactor->ARVALID(m_s_axi_arvalid_converter_signal);
    mp_s_axi_arready_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_arready_converter");
    mp_s_axi_arready_converter->scalar_in(m_s_axi_arready_converter_signal);
    mp_s_axi_arready_converter->vector_out(s_axi_arready);
    mp_S00_AXI_transactor->ARREADY(m_s_axi_arready_converter_signal);
    mp_S00_AXI_transactor->RDATA(s_axi_rdata);
    mp_S00_AXI_transactor->RRESP(s_axi_rresp);
    mp_s_axi_rvalid_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_rvalid_converter");
    mp_s_axi_rvalid_converter->scalar_in(m_s_axi_rvalid_converter_signal);
    mp_s_axi_rvalid_converter->vector_out(s_axi_rvalid);
    mp_S00_AXI_transactor->RVALID(m_s_axi_rvalid_converter_signal);
    mp_s_axi_rready_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_rready_converter");
    mp_s_axi_rready_converter->vector_in(s_axi_rready);
    mp_s_axi_rready_converter->scalar_out(m_s_axi_rready_converter_signal);
    mp_S00_AXI_transactor->RREADY(m_s_axi_rready_converter_signal);
    mp_S00_AXI_transactor->CLK(aclk);
    mp_S00_AXI_transactor->RST(aresetn);

    // S00_AXI' transactor sockets

    mp_impl->target_0_rd_socket->bind(*(mp_S00_AXI_transactor->rd_socket));
    mp_impl->target_0_wr_socket->bind(*(mp_S00_AXI_transactor->wr_socket));
  }
  else
  {
  }

  // configure 'M00_AXI' transactor

  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_sda_axil_xbar", "M00_AXI_TLM_MODE") != 1)
  {
    // Instantiate Socket Stubs

  // 'M00_AXI' transactor parameters
    xsc::common_cpp::properties M00_AXI_transactor_param_props;
    M00_AXI_transactor_param_props.addLong("DATA_WIDTH", "32");
    M00_AXI_transactor_param_props.addLong("FREQ_HZ", "100000000");
    M00_AXI_transactor_param_props.addLong("ID_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("ADDR_WIDTH", "32");
    M00_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("HAS_BURST", "0");
    M00_AXI_transactor_param_props.addLong("HAS_LOCK", "0");
    M00_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    M00_AXI_transactor_param_props.addLong("HAS_CACHE", "0");
    M00_AXI_transactor_param_props.addLong("HAS_QOS", "0");
    M00_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    M00_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    M00_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    M00_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    M00_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    M00_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    M00_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    M00_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    M00_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    M00_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    M00_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    M00_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    M00_AXI_transactor_param_props.addLong("HAS_SIZE", "0");
    M00_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    M00_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    M00_AXI_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    M00_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    M00_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_M00_AXI_transactor = new xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>("M00_AXI_transactor", M00_AXI_transactor_param_props);

    // M00_AXI' transactor ports

    mp_m_axi_awaddr_converter_0 = new xsc::common::vector2vector_converter<32,64>("m_axi_awaddr_converter_0");
    mp_m_axi_awaddr_converter_0->vector_in(m_m_axi_awaddr_converter_0_signal);
    mp_m_axi_awaddr_converter_0->vector_out(m_axi_concat_awaddr_out_0);
    mp_M00_AXI_transactor->AWADDR(m_m_axi_awaddr_converter_0_signal);
    mp_m_axi_awprot_converter_0 = new xsc::common::vector2vector_converter<3,6>("m_axi_awprot_converter_0");
    mp_m_axi_awprot_converter_0->vector_in(m_m_axi_awprot_converter_0_signal);
    mp_m_axi_awprot_converter_0->vector_out(m_axi_concat_awprot_out_0);
    mp_M00_AXI_transactor->AWPROT(m_m_axi_awprot_converter_0_signal);
    mp_m_axi_awvalid_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_awvalid_converter_0");
    mp_m_axi_awvalid_converter_0->scalar_in(m_m_axi_awvalid_converter_0_signal);
    mp_m_axi_awvalid_converter_0->vector_out(m_axi_concat_awvalid_out_0);
    mp_M00_AXI_transactor->AWVALID(m_m_axi_awvalid_converter_0_signal);
    mp_m_axi_awready_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_awready_converter_0");
    mp_m_axi_awready_converter_0->vector_in(m_axi_split_awready_out_0);
    mp_m_axi_awready_converter_0->scalar_out(m_m_axi_awready_converter_0_signal);
    mp_M00_AXI_transactor->AWREADY(m_m_axi_awready_converter_0_signal);
    mp_m_axi_wdata_converter_0 = new xsc::common::vector2vector_converter<32,64>("m_axi_wdata_converter_0");
    mp_m_axi_wdata_converter_0->vector_in(m_m_axi_wdata_converter_0_signal);
    mp_m_axi_wdata_converter_0->vector_out(m_axi_concat_wdata_out_0);
    mp_M00_AXI_transactor->WDATA(m_m_axi_wdata_converter_0_signal);
    mp_m_axi_wstrb_converter_0 = new xsc::common::vector2vector_converter<4,8>("m_axi_wstrb_converter_0");
    mp_m_axi_wstrb_converter_0->vector_in(m_m_axi_wstrb_converter_0_signal);
    mp_m_axi_wstrb_converter_0->vector_out(m_axi_concat_wstrb_out_0);
    mp_M00_AXI_transactor->WSTRB(m_m_axi_wstrb_converter_0_signal);
    mp_m_axi_wvalid_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_wvalid_converter_0");
    mp_m_axi_wvalid_converter_0->scalar_in(m_m_axi_wvalid_converter_0_signal);
    mp_m_axi_wvalid_converter_0->vector_out(m_axi_concat_wvalid_out_0);
    mp_M00_AXI_transactor->WVALID(m_m_axi_wvalid_converter_0_signal);
    mp_m_axi_wready_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_wready_converter_0");
    mp_m_axi_wready_converter_0->vector_in(m_axi_split_wready_out_0);
    mp_m_axi_wready_converter_0->scalar_out(m_m_axi_wready_converter_0_signal);
    mp_M00_AXI_transactor->WREADY(m_m_axi_wready_converter_0_signal);
    mp_m_axi_bresp_converter_0 = new xsc::common::vector2vector_converter<4,2>("m_axi_bresp_converter_0");
    mp_m_axi_bresp_converter_0->vector_in(m_axi_split_bresp_out_0);
    mp_m_axi_bresp_converter_0->vector_out(m_m_axi_bresp_converter_0_signal);
    mp_M00_AXI_transactor->BRESP(m_m_axi_bresp_converter_0_signal);
    mp_m_axi_bvalid_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_bvalid_converter_0");
    mp_m_axi_bvalid_converter_0->vector_in(m_axi_split_bvalid_out_0);
    mp_m_axi_bvalid_converter_0->scalar_out(m_m_axi_bvalid_converter_0_signal);
    mp_M00_AXI_transactor->BVALID(m_m_axi_bvalid_converter_0_signal);
    mp_m_axi_bready_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_bready_converter_0");
    mp_m_axi_bready_converter_0->scalar_in(m_m_axi_bready_converter_0_signal);
    mp_m_axi_bready_converter_0->vector_out(m_axi_concat_bready_out_0);
    mp_M00_AXI_transactor->BREADY(m_m_axi_bready_converter_0_signal);
    mp_m_axi_araddr_converter_0 = new xsc::common::vector2vector_converter<32,64>("m_axi_araddr_converter_0");
    mp_m_axi_araddr_converter_0->vector_in(m_m_axi_araddr_converter_0_signal);
    mp_m_axi_araddr_converter_0->vector_out(m_axi_concat_araddr_out_0);
    mp_M00_AXI_transactor->ARADDR(m_m_axi_araddr_converter_0_signal);
    mp_m_axi_arprot_converter_0 = new xsc::common::vector2vector_converter<3,6>("m_axi_arprot_converter_0");
    mp_m_axi_arprot_converter_0->vector_in(m_m_axi_arprot_converter_0_signal);
    mp_m_axi_arprot_converter_0->vector_out(m_axi_concat_arprot_out_0);
    mp_M00_AXI_transactor->ARPROT(m_m_axi_arprot_converter_0_signal);
    mp_m_axi_arvalid_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_arvalid_converter_0");
    mp_m_axi_arvalid_converter_0->scalar_in(m_m_axi_arvalid_converter_0_signal);
    mp_m_axi_arvalid_converter_0->vector_out(m_axi_concat_arvalid_out_0);
    mp_M00_AXI_transactor->ARVALID(m_m_axi_arvalid_converter_0_signal);
    mp_m_axi_arready_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_arready_converter_0");
    mp_m_axi_arready_converter_0->vector_in(m_axi_split_arready_out_0);
    mp_m_axi_arready_converter_0->scalar_out(m_m_axi_arready_converter_0_signal);
    mp_M00_AXI_transactor->ARREADY(m_m_axi_arready_converter_0_signal);
    mp_m_axi_rdata_converter_0 = new xsc::common::vector2vector_converter<64,32>("m_axi_rdata_converter_0");
    mp_m_axi_rdata_converter_0->vector_in(m_axi_split_rdata_out_0);
    mp_m_axi_rdata_converter_0->vector_out(m_m_axi_rdata_converter_0_signal);
    mp_M00_AXI_transactor->RDATA(m_m_axi_rdata_converter_0_signal);
    mp_m_axi_rresp_converter_0 = new xsc::common::vector2vector_converter<4,2>("m_axi_rresp_converter_0");
    mp_m_axi_rresp_converter_0->vector_in(m_axi_split_rresp_out_0);
    mp_m_axi_rresp_converter_0->vector_out(m_m_axi_rresp_converter_0_signal);
    mp_M00_AXI_transactor->RRESP(m_m_axi_rresp_converter_0_signal);
    mp_m_axi_rvalid_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_rvalid_converter_0");
    mp_m_axi_rvalid_converter_0->vector_in(m_axi_split_rvalid_out_0);
    mp_m_axi_rvalid_converter_0->scalar_out(m_m_axi_rvalid_converter_0_signal);
    mp_M00_AXI_transactor->RVALID(m_m_axi_rvalid_converter_0_signal);
    mp_m_axi_rready_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_rready_converter_0");
    mp_m_axi_rready_converter_0->scalar_in(m_m_axi_rready_converter_0_signal);
    mp_m_axi_rready_converter_0->vector_out(m_axi_concat_rready_out_0);
    mp_M00_AXI_transactor->RREADY(m_m_axi_rready_converter_0_signal);
    mp_M00_AXI_transactor->CLK(aclk);
    mp_M00_AXI_transactor->RST(aresetn);

    // M00_AXI' transactor sockets

    mp_impl->initiator_0_rd_socket->bind(*(mp_M00_AXI_transactor->rd_socket));
    mp_impl->initiator_0_wr_socket->bind(*(mp_M00_AXI_transactor->wr_socket));
  }
  else
  {
  }

  // configure 'M01_AXI' transactor

  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_sda_axil_xbar", "M01_AXI_TLM_MODE") != 1)
  {
    // Instantiate Socket Stubs

  // 'M01_AXI' transactor parameters
    xsc::common_cpp::properties M01_AXI_transactor_param_props;
    M01_AXI_transactor_param_props.addLong("DATA_WIDTH", "32");
    M01_AXI_transactor_param_props.addLong("FREQ_HZ", "100000000");
    M01_AXI_transactor_param_props.addLong("ID_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("ADDR_WIDTH", "32");
    M01_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("HAS_BURST", "0");
    M01_AXI_transactor_param_props.addLong("HAS_LOCK", "0");
    M01_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    M01_AXI_transactor_param_props.addLong("HAS_CACHE", "0");
    M01_AXI_transactor_param_props.addLong("HAS_QOS", "0");
    M01_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    M01_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    M01_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    M01_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    M01_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    M01_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    M01_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    M01_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    M01_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    M01_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    M01_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    M01_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    M01_AXI_transactor_param_props.addLong("HAS_SIZE", "0");
    M01_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    M01_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    M01_AXI_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    M01_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    M01_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_M01_AXI_transactor = new xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>("M01_AXI_transactor", M01_AXI_transactor_param_props);

    // M01_AXI' transactor ports

    mp_m_axi_awaddr_converter_1 = new xsc::common::vector2vector_converter<32,64>("m_axi_awaddr_converter_1");
    mp_m_axi_awaddr_converter_1->vector_in(m_m_axi_awaddr_converter_1_signal);
    mp_m_axi_awaddr_converter_1->vector_out(m_axi_concat_awaddr_out_1);
    mp_M01_AXI_transactor->AWADDR(m_m_axi_awaddr_converter_1_signal);
    mp_m_axi_awprot_converter_1 = new xsc::common::vector2vector_converter<3,6>("m_axi_awprot_converter_1");
    mp_m_axi_awprot_converter_1->vector_in(m_m_axi_awprot_converter_1_signal);
    mp_m_axi_awprot_converter_1->vector_out(m_axi_concat_awprot_out_1);
    mp_M01_AXI_transactor->AWPROT(m_m_axi_awprot_converter_1_signal);
    mp_m_axi_awvalid_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_awvalid_converter_1");
    mp_m_axi_awvalid_converter_1->scalar_in(m_m_axi_awvalid_converter_1_signal);
    mp_m_axi_awvalid_converter_1->vector_out(m_axi_concat_awvalid_out_1);
    mp_M01_AXI_transactor->AWVALID(m_m_axi_awvalid_converter_1_signal);
    mp_m_axi_awready_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_awready_converter_1");
    mp_m_axi_awready_converter_1->vector_in(m_axi_split_awready_out_1);
    mp_m_axi_awready_converter_1->scalar_out(m_m_axi_awready_converter_1_signal);
    mp_M01_AXI_transactor->AWREADY(m_m_axi_awready_converter_1_signal);
    mp_m_axi_wdata_converter_1 = new xsc::common::vector2vector_converter<32,64>("m_axi_wdata_converter_1");
    mp_m_axi_wdata_converter_1->vector_in(m_m_axi_wdata_converter_1_signal);
    mp_m_axi_wdata_converter_1->vector_out(m_axi_concat_wdata_out_1);
    mp_M01_AXI_transactor->WDATA(m_m_axi_wdata_converter_1_signal);
    mp_m_axi_wstrb_converter_1 = new xsc::common::vector2vector_converter<4,8>("m_axi_wstrb_converter_1");
    mp_m_axi_wstrb_converter_1->vector_in(m_m_axi_wstrb_converter_1_signal);
    mp_m_axi_wstrb_converter_1->vector_out(m_axi_concat_wstrb_out_1);
    mp_M01_AXI_transactor->WSTRB(m_m_axi_wstrb_converter_1_signal);
    mp_m_axi_wvalid_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_wvalid_converter_1");
    mp_m_axi_wvalid_converter_1->scalar_in(m_m_axi_wvalid_converter_1_signal);
    mp_m_axi_wvalid_converter_1->vector_out(m_axi_concat_wvalid_out_1);
    mp_M01_AXI_transactor->WVALID(m_m_axi_wvalid_converter_1_signal);
    mp_m_axi_wready_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_wready_converter_1");
    mp_m_axi_wready_converter_1->vector_in(m_axi_split_wready_out_1);
    mp_m_axi_wready_converter_1->scalar_out(m_m_axi_wready_converter_1_signal);
    mp_M01_AXI_transactor->WREADY(m_m_axi_wready_converter_1_signal);
    mp_m_axi_bresp_converter_1 = new xsc::common::vector2vector_converter<4,2>("m_axi_bresp_converter_1");
    mp_m_axi_bresp_converter_1->vector_in(m_axi_split_bresp_out_1);
    mp_m_axi_bresp_converter_1->vector_out(m_m_axi_bresp_converter_1_signal);
    mp_M01_AXI_transactor->BRESP(m_m_axi_bresp_converter_1_signal);
    mp_m_axi_bvalid_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_bvalid_converter_1");
    mp_m_axi_bvalid_converter_1->vector_in(m_axi_split_bvalid_out_1);
    mp_m_axi_bvalid_converter_1->scalar_out(m_m_axi_bvalid_converter_1_signal);
    mp_M01_AXI_transactor->BVALID(m_m_axi_bvalid_converter_1_signal);
    mp_m_axi_bready_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_bready_converter_1");
    mp_m_axi_bready_converter_1->scalar_in(m_m_axi_bready_converter_1_signal);
    mp_m_axi_bready_converter_1->vector_out(m_axi_concat_bready_out_1);
    mp_M01_AXI_transactor->BREADY(m_m_axi_bready_converter_1_signal);
    mp_m_axi_araddr_converter_1 = new xsc::common::vector2vector_converter<32,64>("m_axi_araddr_converter_1");
    mp_m_axi_araddr_converter_1->vector_in(m_m_axi_araddr_converter_1_signal);
    mp_m_axi_araddr_converter_1->vector_out(m_axi_concat_araddr_out_1);
    mp_M01_AXI_transactor->ARADDR(m_m_axi_araddr_converter_1_signal);
    mp_m_axi_arprot_converter_1 = new xsc::common::vector2vector_converter<3,6>("m_axi_arprot_converter_1");
    mp_m_axi_arprot_converter_1->vector_in(m_m_axi_arprot_converter_1_signal);
    mp_m_axi_arprot_converter_1->vector_out(m_axi_concat_arprot_out_1);
    mp_M01_AXI_transactor->ARPROT(m_m_axi_arprot_converter_1_signal);
    mp_m_axi_arvalid_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_arvalid_converter_1");
    mp_m_axi_arvalid_converter_1->scalar_in(m_m_axi_arvalid_converter_1_signal);
    mp_m_axi_arvalid_converter_1->vector_out(m_axi_concat_arvalid_out_1);
    mp_M01_AXI_transactor->ARVALID(m_m_axi_arvalid_converter_1_signal);
    mp_m_axi_arready_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_arready_converter_1");
    mp_m_axi_arready_converter_1->vector_in(m_axi_split_arready_out_1);
    mp_m_axi_arready_converter_1->scalar_out(m_m_axi_arready_converter_1_signal);
    mp_M01_AXI_transactor->ARREADY(m_m_axi_arready_converter_1_signal);
    mp_m_axi_rdata_converter_1 = new xsc::common::vector2vector_converter<64,32>("m_axi_rdata_converter_1");
    mp_m_axi_rdata_converter_1->vector_in(m_axi_split_rdata_out_1);
    mp_m_axi_rdata_converter_1->vector_out(m_m_axi_rdata_converter_1_signal);
    mp_M01_AXI_transactor->RDATA(m_m_axi_rdata_converter_1_signal);
    mp_m_axi_rresp_converter_1 = new xsc::common::vector2vector_converter<4,2>("m_axi_rresp_converter_1");
    mp_m_axi_rresp_converter_1->vector_in(m_axi_split_rresp_out_1);
    mp_m_axi_rresp_converter_1->vector_out(m_m_axi_rresp_converter_1_signal);
    mp_M01_AXI_transactor->RRESP(m_m_axi_rresp_converter_1_signal);
    mp_m_axi_rvalid_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_rvalid_converter_1");
    mp_m_axi_rvalid_converter_1->vector_in(m_axi_split_rvalid_out_1);
    mp_m_axi_rvalid_converter_1->scalar_out(m_m_axi_rvalid_converter_1_signal);
    mp_M01_AXI_transactor->RVALID(m_m_axi_rvalid_converter_1_signal);
    mp_m_axi_rready_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_rready_converter_1");
    mp_m_axi_rready_converter_1->scalar_in(m_m_axi_rready_converter_1_signal);
    mp_m_axi_rready_converter_1->vector_out(m_axi_concat_rready_out_1);
    mp_M01_AXI_transactor->RREADY(m_m_axi_rready_converter_1_signal);
    mp_M01_AXI_transactor->CLK(aclk);
    mp_M01_AXI_transactor->RST(aresetn);

    // M01_AXI' transactor sockets

    mp_impl->initiator_1_rd_socket->bind(*(mp_M01_AXI_transactor->rd_socket));
    mp_impl->initiator_1_wr_socket->bind(*(mp_M01_AXI_transactor->wr_socket));
  }
  else
  {
  }

}

#endif // XM_SYSTEMC




#ifdef RIVIERA
cl_sda_axil_xbar::cl_sda_axil_xbar(const sc_core::sc_module_name& nm) : cl_sda_axil_xbar_sc(nm), aclk("aclk"), aresetn("aresetn"), s_axi_awaddr("s_axi_awaddr"), s_axi_awprot("s_axi_awprot"), s_axi_awvalid("s_axi_awvalid"), s_axi_awready("s_axi_awready"), s_axi_wdata("s_axi_wdata"), s_axi_wstrb("s_axi_wstrb"), s_axi_wvalid("s_axi_wvalid"), s_axi_wready("s_axi_wready"), s_axi_bresp("s_axi_bresp"), s_axi_bvalid("s_axi_bvalid"), s_axi_bready("s_axi_bready"), s_axi_araddr("s_axi_araddr"), s_axi_arprot("s_axi_arprot"), s_axi_arvalid("s_axi_arvalid"), s_axi_arready("s_axi_arready"), s_axi_rdata("s_axi_rdata"), s_axi_rresp("s_axi_rresp"), s_axi_rvalid("s_axi_rvalid"), s_axi_rready("s_axi_rready"), m_axi_awaddr("m_axi_awaddr"), m_axi_awprot("m_axi_awprot"), m_axi_awvalid("m_axi_awvalid"), m_axi_awready("m_axi_awready"), m_axi_wdata("m_axi_wdata"), m_axi_wstrb("m_axi_wstrb"), m_axi_wvalid("m_axi_wvalid"), m_axi_wready("m_axi_wready"), m_axi_bresp("m_axi_bresp"), m_axi_bvalid("m_axi_bvalid"), m_axi_bready("m_axi_bready"), m_axi_araddr("m_axi_araddr"), m_axi_arprot("m_axi_arprot"), m_axi_arvalid("m_axi_arvalid"), m_axi_arready("m_axi_arready"), m_axi_rdata("m_axi_rdata"), m_axi_rresp("m_axi_rresp"), m_axi_rvalid("m_axi_rvalid"), m_axi_rready("m_axi_rready")
{

  // initialize pins
  mp_impl->aclk(aclk);
  mp_impl->aresetn(aresetn);

  // initialize transactors
  mp_S00_AXI_transactor = NULL;
  mp_s_axi_awvalid_converter = NULL;
  mp_s_axi_awready_converter = NULL;
  mp_s_axi_wvalid_converter = NULL;
  mp_s_axi_wready_converter = NULL;
  mp_s_axi_bvalid_converter = NULL;
  mp_s_axi_bready_converter = NULL;
  mp_s_axi_arvalid_converter = NULL;
  mp_s_axi_arready_converter = NULL;
  mp_s_axi_rvalid_converter = NULL;
  mp_s_axi_rready_converter = NULL;
  mp_M00_AXI_transactor = NULL;
  mp_m_axi_awaddr_converter_0 = NULL;
  mp_m_axi_awprot_converter_0 = NULL;
  mp_m_axi_awvalid_converter_0 = NULL;
  mp_m_axi_awready_converter_0 = NULL;
  mp_m_axi_wdata_converter_0 = NULL;
  mp_m_axi_wstrb_converter_0 = NULL;
  mp_m_axi_wvalid_converter_0 = NULL;
  mp_m_axi_wready_converter_0 = NULL;
  mp_m_axi_bresp_converter_0 = NULL;
  mp_m_axi_bvalid_converter_0 = NULL;
  mp_m_axi_bready_converter_0 = NULL;
  mp_m_axi_araddr_converter_0 = NULL;
  mp_m_axi_arprot_converter_0 = NULL;
  mp_m_axi_arvalid_converter_0 = NULL;
  mp_m_axi_arready_converter_0 = NULL;
  mp_m_axi_rdata_converter_0 = NULL;
  mp_m_axi_rresp_converter_0 = NULL;
  mp_m_axi_rvalid_converter_0 = NULL;
  mp_m_axi_rready_converter_0 = NULL;
  mp_M01_AXI_transactor = NULL;
  mp_m_axi_awaddr_converter_1 = NULL;
  mp_m_axi_awprot_converter_1 = NULL;
  mp_m_axi_awvalid_converter_1 = NULL;
  mp_m_axi_awready_converter_1 = NULL;
  mp_m_axi_wdata_converter_1 = NULL;
  mp_m_axi_wstrb_converter_1 = NULL;
  mp_m_axi_wvalid_converter_1 = NULL;
  mp_m_axi_wready_converter_1 = NULL;
  mp_m_axi_bresp_converter_1 = NULL;
  mp_m_axi_bvalid_converter_1 = NULL;
  mp_m_axi_bready_converter_1 = NULL;
  mp_m_axi_araddr_converter_1 = NULL;
  mp_m_axi_arprot_converter_1 = NULL;
  mp_m_axi_arvalid_converter_1 = NULL;
  mp_m_axi_arready_converter_1 = NULL;
  mp_m_axi_rdata_converter_1 = NULL;
  mp_m_axi_rresp_converter_1 = NULL;
  mp_m_axi_rvalid_converter_1 = NULL;
  mp_m_axi_rready_converter_1 = NULL;

  // initialize junctures
  mp_m_axi_concat_araddr = NULL;
  mp_m_axi_concat_arprot = NULL;
  mp_m_axi_concat_arvalid = NULL;
  mp_m_axi_concat_awaddr = NULL;
  mp_m_axi_concat_awprot = NULL;
  mp_m_axi_concat_awvalid = NULL;
  mp_m_axi_concat_bready = NULL;
  mp_m_axi_concat_rready = NULL;
  mp_m_axi_concat_wdata = NULL;
  mp_m_axi_concat_wstrb = NULL;
  mp_m_axi_concat_wvalid = NULL;
  mp_m_axi_split_arready = NULL;
  mp_m_axi_split_awready = NULL;
  mp_m_axi_split_bresp = NULL;
  mp_m_axi_split_bvalid = NULL;
  mp_m_axi_split_rdata = NULL;
  mp_m_axi_split_rresp = NULL;
  mp_m_axi_split_rvalid = NULL;
  mp_m_axi_split_wready = NULL;
  mp_m_axi_concat_awaddr = new xsc::xsc_concatenator<64, 2>("m_axi_concat_awaddr");
  mp_m_axi_concat_awaddr->in_port[0](m_axi_concat_awaddr_out_0);
  mp_m_axi_concat_awaddr->out_port(m_axi_awaddr);
    mp_m_axi_concat_awaddr->offset_port(0, 0);
  mp_m_axi_concat_awprot = new xsc::xsc_concatenator<6, 2>("m_axi_concat_awprot");
  mp_m_axi_concat_awprot->in_port[0](m_axi_concat_awprot_out_0);
  mp_m_axi_concat_awprot->out_port(m_axi_awprot);
    mp_m_axi_concat_awprot->offset_port(0, 0);
  mp_m_axi_concat_awvalid = new xsc::xsc_concatenator<2, 2>("m_axi_concat_awvalid");
  mp_m_axi_concat_awvalid->in_port[0](m_axi_concat_awvalid_out_0);
  mp_m_axi_concat_awvalid->out_port(m_axi_awvalid);
    mp_m_axi_concat_awvalid->offset_port(0, 0);
  mp_m_axi_split_awready = new xsc::xsc_split<2, 2>("m_axi_split_awready");
  mp_m_axi_split_awready->in_port(m_axi_awready);
  mp_m_axi_split_awready->out_port[0](m_axi_split_awready_out_0);
    mp_m_axi_split_awready->add_mask(0,1,0);
  mp_m_axi_concat_wdata = new xsc::xsc_concatenator<64, 2>("m_axi_concat_wdata");
  mp_m_axi_concat_wdata->in_port[0](m_axi_concat_wdata_out_0);
  mp_m_axi_concat_wdata->out_port(m_axi_wdata);
    mp_m_axi_concat_wdata->offset_port(0, 0);
  mp_m_axi_concat_wstrb = new xsc::xsc_concatenator<8, 2>("m_axi_concat_wstrb");
  mp_m_axi_concat_wstrb->in_port[0](m_axi_concat_wstrb_out_0);
  mp_m_axi_concat_wstrb->out_port(m_axi_wstrb);
    mp_m_axi_concat_wstrb->offset_port(0, 0);
  mp_m_axi_concat_wvalid = new xsc::xsc_concatenator<2, 2>("m_axi_concat_wvalid");
  mp_m_axi_concat_wvalid->in_port[0](m_axi_concat_wvalid_out_0);
  mp_m_axi_concat_wvalid->out_port(m_axi_wvalid);
    mp_m_axi_concat_wvalid->offset_port(0, 0);
  mp_m_axi_split_wready = new xsc::xsc_split<2, 2>("m_axi_split_wready");
  mp_m_axi_split_wready->in_port(m_axi_wready);
  mp_m_axi_split_wready->out_port[0](m_axi_split_wready_out_0);
    mp_m_axi_split_wready->add_mask(0,1,0);
  mp_m_axi_split_bresp = new xsc::xsc_split<4, 2>("m_axi_split_bresp");
  mp_m_axi_split_bresp->in_port(m_axi_bresp);
  mp_m_axi_split_bresp->out_port[0](m_axi_split_bresp_out_0);
    mp_m_axi_split_bresp->add_mask(0,2,0);
  mp_m_axi_split_bvalid = new xsc::xsc_split<2, 2>("m_axi_split_bvalid");
  mp_m_axi_split_bvalid->in_port(m_axi_bvalid);
  mp_m_axi_split_bvalid->out_port[0](m_axi_split_bvalid_out_0);
    mp_m_axi_split_bvalid->add_mask(0,1,0);
  mp_m_axi_concat_bready = new xsc::xsc_concatenator<2, 2>("m_axi_concat_bready");
  mp_m_axi_concat_bready->in_port[0](m_axi_concat_bready_out_0);
  mp_m_axi_concat_bready->out_port(m_axi_bready);
    mp_m_axi_concat_bready->offset_port(0, 0);
  mp_m_axi_concat_araddr = new xsc::xsc_concatenator<64, 2>("m_axi_concat_araddr");
  mp_m_axi_concat_araddr->in_port[0](m_axi_concat_araddr_out_0);
  mp_m_axi_concat_araddr->out_port(m_axi_araddr);
    mp_m_axi_concat_araddr->offset_port(0, 0);
  mp_m_axi_concat_arprot = new xsc::xsc_concatenator<6, 2>("m_axi_concat_arprot");
  mp_m_axi_concat_arprot->in_port[0](m_axi_concat_arprot_out_0);
  mp_m_axi_concat_arprot->out_port(m_axi_arprot);
    mp_m_axi_concat_arprot->offset_port(0, 0);
  mp_m_axi_concat_arvalid = new xsc::xsc_concatenator<2, 2>("m_axi_concat_arvalid");
  mp_m_axi_concat_arvalid->in_port[0](m_axi_concat_arvalid_out_0);
  mp_m_axi_concat_arvalid->out_port(m_axi_arvalid);
    mp_m_axi_concat_arvalid->offset_port(0, 0);
  mp_m_axi_split_arready = new xsc::xsc_split<2, 2>("m_axi_split_arready");
  mp_m_axi_split_arready->in_port(m_axi_arready);
  mp_m_axi_split_arready->out_port[0](m_axi_split_arready_out_0);
    mp_m_axi_split_arready->add_mask(0,1,0);
  mp_m_axi_split_rdata = new xsc::xsc_split<64, 2>("m_axi_split_rdata");
  mp_m_axi_split_rdata->in_port(m_axi_rdata);
  mp_m_axi_split_rdata->out_port[0](m_axi_split_rdata_out_0);
    mp_m_axi_split_rdata->add_mask(0,32,0);
  mp_m_axi_split_rresp = new xsc::xsc_split<4, 2>("m_axi_split_rresp");
  mp_m_axi_split_rresp->in_port(m_axi_rresp);
  mp_m_axi_split_rresp->out_port[0](m_axi_split_rresp_out_0);
    mp_m_axi_split_rresp->add_mask(0,2,0);
  mp_m_axi_split_rvalid = new xsc::xsc_split<2, 2>("m_axi_split_rvalid");
  mp_m_axi_split_rvalid->in_port(m_axi_rvalid);
  mp_m_axi_split_rvalid->out_port[0](m_axi_split_rvalid_out_0);
    mp_m_axi_split_rvalid->add_mask(0,1,0);
  mp_m_axi_concat_rready = new xsc::xsc_concatenator<2, 2>("m_axi_concat_rready");
  mp_m_axi_concat_rready->in_port[0](m_axi_concat_rready_out_0);
  mp_m_axi_concat_rready->out_port(m_axi_rready);
    mp_m_axi_concat_rready->offset_port(0, 0);
  mp_m_axi_concat_awaddr->in_port[1](m_axi_concat_awaddr_out_1);
  mp_m_axi_concat_awaddr->offset_port(1, 32);
  mp_m_axi_concat_awprot->in_port[1](m_axi_concat_awprot_out_1);
  mp_m_axi_concat_awprot->offset_port(1, 3);
  mp_m_axi_concat_awvalid->in_port[1](m_axi_concat_awvalid_out_1);
  mp_m_axi_concat_awvalid->offset_port(1, 1);
  
  mp_m_axi_split_awready->out_port[1](m_axi_split_awready_out_1);
    mp_m_axi_split_awready->add_mask(1,2,1);
  mp_m_axi_concat_wdata->in_port[1](m_axi_concat_wdata_out_1);
  mp_m_axi_concat_wdata->offset_port(1, 32);
  mp_m_axi_concat_wstrb->in_port[1](m_axi_concat_wstrb_out_1);
  mp_m_axi_concat_wstrb->offset_port(1, 4);
  mp_m_axi_concat_wvalid->in_port[1](m_axi_concat_wvalid_out_1);
  mp_m_axi_concat_wvalid->offset_port(1, 1);
  
  mp_m_axi_split_wready->out_port[1](m_axi_split_wready_out_1);
    mp_m_axi_split_wready->add_mask(1,2,1);
  
  mp_m_axi_split_bresp->out_port[1](m_axi_split_bresp_out_1);
    mp_m_axi_split_bresp->add_mask(1,4,2);
  
  mp_m_axi_split_bvalid->out_port[1](m_axi_split_bvalid_out_1);
    mp_m_axi_split_bvalid->add_mask(1,2,1);
  mp_m_axi_concat_bready->in_port[1](m_axi_concat_bready_out_1);
  mp_m_axi_concat_bready->offset_port(1, 1);
  mp_m_axi_concat_araddr->in_port[1](m_axi_concat_araddr_out_1);
  mp_m_axi_concat_araddr->offset_port(1, 32);
  mp_m_axi_concat_arprot->in_port[1](m_axi_concat_arprot_out_1);
  mp_m_axi_concat_arprot->offset_port(1, 3);
  mp_m_axi_concat_arvalid->in_port[1](m_axi_concat_arvalid_out_1);
  mp_m_axi_concat_arvalid->offset_port(1, 1);
  
  mp_m_axi_split_arready->out_port[1](m_axi_split_arready_out_1);
    mp_m_axi_split_arready->add_mask(1,2,1);
  
  mp_m_axi_split_rdata->out_port[1](m_axi_split_rdata_out_1);
    mp_m_axi_split_rdata->add_mask(1,64,32);
  
  mp_m_axi_split_rresp->out_port[1](m_axi_split_rresp_out_1);
    mp_m_axi_split_rresp->add_mask(1,4,2);
  
  mp_m_axi_split_rvalid->out_port[1](m_axi_split_rvalid_out_1);
    mp_m_axi_split_rvalid->add_mask(1,2,1);
  mp_m_axi_concat_rready->in_port[1](m_axi_concat_rready_out_1);
  mp_m_axi_concat_rready->offset_port(1, 1);

  // initialize socket stubs

}

void cl_sda_axil_xbar::before_end_of_elaboration()
{
  // configure 'S00_AXI' transactor

  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_sda_axil_xbar", "S00_AXI_TLM_MODE") != 1)
  {
    // Instantiate Socket Stubs

  // 'S00_AXI' transactor parameters
    xsc::common_cpp::properties S00_AXI_transactor_param_props;
    S00_AXI_transactor_param_props.addLong("DATA_WIDTH", "32");
    S00_AXI_transactor_param_props.addLong("FREQ_HZ", "100000000");
    S00_AXI_transactor_param_props.addLong("ID_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("ADDR_WIDTH", "32");
    S00_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("HAS_BURST", "0");
    S00_AXI_transactor_param_props.addLong("HAS_LOCK", "0");
    S00_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    S00_AXI_transactor_param_props.addLong("HAS_CACHE", "0");
    S00_AXI_transactor_param_props.addLong("HAS_QOS", "0");
    S00_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    S00_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    S00_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    S00_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    S00_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    S00_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    S00_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    S00_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    S00_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    S00_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    S00_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    S00_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    S00_AXI_transactor_param_props.addLong("HAS_SIZE", "0");
    S00_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    S00_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    S00_AXI_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    S00_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    S00_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_S00_AXI_transactor = new xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>("S00_AXI_transactor", S00_AXI_transactor_param_props);

    // S00_AXI' transactor ports

    mp_S00_AXI_transactor->AWADDR(s_axi_awaddr);
    mp_S00_AXI_transactor->AWPROT(s_axi_awprot);
    mp_s_axi_awvalid_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_awvalid_converter");
    mp_s_axi_awvalid_converter->vector_in(s_axi_awvalid);
    mp_s_axi_awvalid_converter->scalar_out(m_s_axi_awvalid_converter_signal);
    mp_S00_AXI_transactor->AWVALID(m_s_axi_awvalid_converter_signal);
    mp_s_axi_awready_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_awready_converter");
    mp_s_axi_awready_converter->scalar_in(m_s_axi_awready_converter_signal);
    mp_s_axi_awready_converter->vector_out(s_axi_awready);
    mp_S00_AXI_transactor->AWREADY(m_s_axi_awready_converter_signal);
    mp_S00_AXI_transactor->WDATA(s_axi_wdata);
    mp_S00_AXI_transactor->WSTRB(s_axi_wstrb);
    mp_s_axi_wvalid_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_wvalid_converter");
    mp_s_axi_wvalid_converter->vector_in(s_axi_wvalid);
    mp_s_axi_wvalid_converter->scalar_out(m_s_axi_wvalid_converter_signal);
    mp_S00_AXI_transactor->WVALID(m_s_axi_wvalid_converter_signal);
    mp_s_axi_wready_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_wready_converter");
    mp_s_axi_wready_converter->scalar_in(m_s_axi_wready_converter_signal);
    mp_s_axi_wready_converter->vector_out(s_axi_wready);
    mp_S00_AXI_transactor->WREADY(m_s_axi_wready_converter_signal);
    mp_S00_AXI_transactor->BRESP(s_axi_bresp);
    mp_s_axi_bvalid_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_bvalid_converter");
    mp_s_axi_bvalid_converter->scalar_in(m_s_axi_bvalid_converter_signal);
    mp_s_axi_bvalid_converter->vector_out(s_axi_bvalid);
    mp_S00_AXI_transactor->BVALID(m_s_axi_bvalid_converter_signal);
    mp_s_axi_bready_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_bready_converter");
    mp_s_axi_bready_converter->vector_in(s_axi_bready);
    mp_s_axi_bready_converter->scalar_out(m_s_axi_bready_converter_signal);
    mp_S00_AXI_transactor->BREADY(m_s_axi_bready_converter_signal);
    mp_S00_AXI_transactor->ARADDR(s_axi_araddr);
    mp_S00_AXI_transactor->ARPROT(s_axi_arprot);
    mp_s_axi_arvalid_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_arvalid_converter");
    mp_s_axi_arvalid_converter->vector_in(s_axi_arvalid);
    mp_s_axi_arvalid_converter->scalar_out(m_s_axi_arvalid_converter_signal);
    mp_S00_AXI_transactor->ARVALID(m_s_axi_arvalid_converter_signal);
    mp_s_axi_arready_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_arready_converter");
    mp_s_axi_arready_converter->scalar_in(m_s_axi_arready_converter_signal);
    mp_s_axi_arready_converter->vector_out(s_axi_arready);
    mp_S00_AXI_transactor->ARREADY(m_s_axi_arready_converter_signal);
    mp_S00_AXI_transactor->RDATA(s_axi_rdata);
    mp_S00_AXI_transactor->RRESP(s_axi_rresp);
    mp_s_axi_rvalid_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_rvalid_converter");
    mp_s_axi_rvalid_converter->scalar_in(m_s_axi_rvalid_converter_signal);
    mp_s_axi_rvalid_converter->vector_out(s_axi_rvalid);
    mp_S00_AXI_transactor->RVALID(m_s_axi_rvalid_converter_signal);
    mp_s_axi_rready_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_rready_converter");
    mp_s_axi_rready_converter->vector_in(s_axi_rready);
    mp_s_axi_rready_converter->scalar_out(m_s_axi_rready_converter_signal);
    mp_S00_AXI_transactor->RREADY(m_s_axi_rready_converter_signal);
    mp_S00_AXI_transactor->CLK(aclk);
    mp_S00_AXI_transactor->RST(aresetn);

    // S00_AXI' transactor sockets

    mp_impl->target_0_rd_socket->bind(*(mp_S00_AXI_transactor->rd_socket));
    mp_impl->target_0_wr_socket->bind(*(mp_S00_AXI_transactor->wr_socket));
  }
  else
  {
  }

  // configure 'M00_AXI' transactor

  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_sda_axil_xbar", "M00_AXI_TLM_MODE") != 1)
  {
    // Instantiate Socket Stubs

  // 'M00_AXI' transactor parameters
    xsc::common_cpp::properties M00_AXI_transactor_param_props;
    M00_AXI_transactor_param_props.addLong("DATA_WIDTH", "32");
    M00_AXI_transactor_param_props.addLong("FREQ_HZ", "100000000");
    M00_AXI_transactor_param_props.addLong("ID_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("ADDR_WIDTH", "32");
    M00_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("HAS_BURST", "0");
    M00_AXI_transactor_param_props.addLong("HAS_LOCK", "0");
    M00_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    M00_AXI_transactor_param_props.addLong("HAS_CACHE", "0");
    M00_AXI_transactor_param_props.addLong("HAS_QOS", "0");
    M00_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    M00_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    M00_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    M00_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    M00_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    M00_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    M00_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    M00_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    M00_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    M00_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    M00_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    M00_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    M00_AXI_transactor_param_props.addLong("HAS_SIZE", "0");
    M00_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    M00_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    M00_AXI_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    M00_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    M00_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_M00_AXI_transactor = new xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>("M00_AXI_transactor", M00_AXI_transactor_param_props);

    // M00_AXI' transactor ports

    mp_m_axi_awaddr_converter_0 = new xsc::common::vector2vector_converter<32,64>("m_axi_awaddr_converter_0");
    mp_m_axi_awaddr_converter_0->vector_in(m_m_axi_awaddr_converter_0_signal);
    mp_m_axi_awaddr_converter_0->vector_out(m_axi_concat_awaddr_out_0);
    mp_M00_AXI_transactor->AWADDR(m_m_axi_awaddr_converter_0_signal);
    mp_m_axi_awprot_converter_0 = new xsc::common::vector2vector_converter<3,6>("m_axi_awprot_converter_0");
    mp_m_axi_awprot_converter_0->vector_in(m_m_axi_awprot_converter_0_signal);
    mp_m_axi_awprot_converter_0->vector_out(m_axi_concat_awprot_out_0);
    mp_M00_AXI_transactor->AWPROT(m_m_axi_awprot_converter_0_signal);
    mp_m_axi_awvalid_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_awvalid_converter_0");
    mp_m_axi_awvalid_converter_0->scalar_in(m_m_axi_awvalid_converter_0_signal);
    mp_m_axi_awvalid_converter_0->vector_out(m_axi_concat_awvalid_out_0);
    mp_M00_AXI_transactor->AWVALID(m_m_axi_awvalid_converter_0_signal);
    mp_m_axi_awready_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_awready_converter_0");
    mp_m_axi_awready_converter_0->vector_in(m_axi_split_awready_out_0);
    mp_m_axi_awready_converter_0->scalar_out(m_m_axi_awready_converter_0_signal);
    mp_M00_AXI_transactor->AWREADY(m_m_axi_awready_converter_0_signal);
    mp_m_axi_wdata_converter_0 = new xsc::common::vector2vector_converter<32,64>("m_axi_wdata_converter_0");
    mp_m_axi_wdata_converter_0->vector_in(m_m_axi_wdata_converter_0_signal);
    mp_m_axi_wdata_converter_0->vector_out(m_axi_concat_wdata_out_0);
    mp_M00_AXI_transactor->WDATA(m_m_axi_wdata_converter_0_signal);
    mp_m_axi_wstrb_converter_0 = new xsc::common::vector2vector_converter<4,8>("m_axi_wstrb_converter_0");
    mp_m_axi_wstrb_converter_0->vector_in(m_m_axi_wstrb_converter_0_signal);
    mp_m_axi_wstrb_converter_0->vector_out(m_axi_concat_wstrb_out_0);
    mp_M00_AXI_transactor->WSTRB(m_m_axi_wstrb_converter_0_signal);
    mp_m_axi_wvalid_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_wvalid_converter_0");
    mp_m_axi_wvalid_converter_0->scalar_in(m_m_axi_wvalid_converter_0_signal);
    mp_m_axi_wvalid_converter_0->vector_out(m_axi_concat_wvalid_out_0);
    mp_M00_AXI_transactor->WVALID(m_m_axi_wvalid_converter_0_signal);
    mp_m_axi_wready_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_wready_converter_0");
    mp_m_axi_wready_converter_0->vector_in(m_axi_split_wready_out_0);
    mp_m_axi_wready_converter_0->scalar_out(m_m_axi_wready_converter_0_signal);
    mp_M00_AXI_transactor->WREADY(m_m_axi_wready_converter_0_signal);
    mp_m_axi_bresp_converter_0 = new xsc::common::vector2vector_converter<4,2>("m_axi_bresp_converter_0");
    mp_m_axi_bresp_converter_0->vector_in(m_axi_split_bresp_out_0);
    mp_m_axi_bresp_converter_0->vector_out(m_m_axi_bresp_converter_0_signal);
    mp_M00_AXI_transactor->BRESP(m_m_axi_bresp_converter_0_signal);
    mp_m_axi_bvalid_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_bvalid_converter_0");
    mp_m_axi_bvalid_converter_0->vector_in(m_axi_split_bvalid_out_0);
    mp_m_axi_bvalid_converter_0->scalar_out(m_m_axi_bvalid_converter_0_signal);
    mp_M00_AXI_transactor->BVALID(m_m_axi_bvalid_converter_0_signal);
    mp_m_axi_bready_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_bready_converter_0");
    mp_m_axi_bready_converter_0->scalar_in(m_m_axi_bready_converter_0_signal);
    mp_m_axi_bready_converter_0->vector_out(m_axi_concat_bready_out_0);
    mp_M00_AXI_transactor->BREADY(m_m_axi_bready_converter_0_signal);
    mp_m_axi_araddr_converter_0 = new xsc::common::vector2vector_converter<32,64>("m_axi_araddr_converter_0");
    mp_m_axi_araddr_converter_0->vector_in(m_m_axi_araddr_converter_0_signal);
    mp_m_axi_araddr_converter_0->vector_out(m_axi_concat_araddr_out_0);
    mp_M00_AXI_transactor->ARADDR(m_m_axi_araddr_converter_0_signal);
    mp_m_axi_arprot_converter_0 = new xsc::common::vector2vector_converter<3,6>("m_axi_arprot_converter_0");
    mp_m_axi_arprot_converter_0->vector_in(m_m_axi_arprot_converter_0_signal);
    mp_m_axi_arprot_converter_0->vector_out(m_axi_concat_arprot_out_0);
    mp_M00_AXI_transactor->ARPROT(m_m_axi_arprot_converter_0_signal);
    mp_m_axi_arvalid_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_arvalid_converter_0");
    mp_m_axi_arvalid_converter_0->scalar_in(m_m_axi_arvalid_converter_0_signal);
    mp_m_axi_arvalid_converter_0->vector_out(m_axi_concat_arvalid_out_0);
    mp_M00_AXI_transactor->ARVALID(m_m_axi_arvalid_converter_0_signal);
    mp_m_axi_arready_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_arready_converter_0");
    mp_m_axi_arready_converter_0->vector_in(m_axi_split_arready_out_0);
    mp_m_axi_arready_converter_0->scalar_out(m_m_axi_arready_converter_0_signal);
    mp_M00_AXI_transactor->ARREADY(m_m_axi_arready_converter_0_signal);
    mp_m_axi_rdata_converter_0 = new xsc::common::vector2vector_converter<64,32>("m_axi_rdata_converter_0");
    mp_m_axi_rdata_converter_0->vector_in(m_axi_split_rdata_out_0);
    mp_m_axi_rdata_converter_0->vector_out(m_m_axi_rdata_converter_0_signal);
    mp_M00_AXI_transactor->RDATA(m_m_axi_rdata_converter_0_signal);
    mp_m_axi_rresp_converter_0 = new xsc::common::vector2vector_converter<4,2>("m_axi_rresp_converter_0");
    mp_m_axi_rresp_converter_0->vector_in(m_axi_split_rresp_out_0);
    mp_m_axi_rresp_converter_0->vector_out(m_m_axi_rresp_converter_0_signal);
    mp_M00_AXI_transactor->RRESP(m_m_axi_rresp_converter_0_signal);
    mp_m_axi_rvalid_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_rvalid_converter_0");
    mp_m_axi_rvalid_converter_0->vector_in(m_axi_split_rvalid_out_0);
    mp_m_axi_rvalid_converter_0->scalar_out(m_m_axi_rvalid_converter_0_signal);
    mp_M00_AXI_transactor->RVALID(m_m_axi_rvalid_converter_0_signal);
    mp_m_axi_rready_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_rready_converter_0");
    mp_m_axi_rready_converter_0->scalar_in(m_m_axi_rready_converter_0_signal);
    mp_m_axi_rready_converter_0->vector_out(m_axi_concat_rready_out_0);
    mp_M00_AXI_transactor->RREADY(m_m_axi_rready_converter_0_signal);
    mp_M00_AXI_transactor->CLK(aclk);
    mp_M00_AXI_transactor->RST(aresetn);

    // M00_AXI' transactor sockets

    mp_impl->initiator_0_rd_socket->bind(*(mp_M00_AXI_transactor->rd_socket));
    mp_impl->initiator_0_wr_socket->bind(*(mp_M00_AXI_transactor->wr_socket));
  }
  else
  {
  }

  // configure 'M01_AXI' transactor

  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_sda_axil_xbar", "M01_AXI_TLM_MODE") != 1)
  {
    // Instantiate Socket Stubs

  // 'M01_AXI' transactor parameters
    xsc::common_cpp::properties M01_AXI_transactor_param_props;
    M01_AXI_transactor_param_props.addLong("DATA_WIDTH", "32");
    M01_AXI_transactor_param_props.addLong("FREQ_HZ", "100000000");
    M01_AXI_transactor_param_props.addLong("ID_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("ADDR_WIDTH", "32");
    M01_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("HAS_BURST", "0");
    M01_AXI_transactor_param_props.addLong("HAS_LOCK", "0");
    M01_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    M01_AXI_transactor_param_props.addLong("HAS_CACHE", "0");
    M01_AXI_transactor_param_props.addLong("HAS_QOS", "0");
    M01_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    M01_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    M01_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    M01_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    M01_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    M01_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    M01_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    M01_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    M01_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    M01_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    M01_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    M01_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    M01_AXI_transactor_param_props.addLong("HAS_SIZE", "0");
    M01_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    M01_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    M01_AXI_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    M01_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    M01_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_M01_AXI_transactor = new xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>("M01_AXI_transactor", M01_AXI_transactor_param_props);

    // M01_AXI' transactor ports

    mp_m_axi_awaddr_converter_1 = new xsc::common::vector2vector_converter<32,64>("m_axi_awaddr_converter_1");
    mp_m_axi_awaddr_converter_1->vector_in(m_m_axi_awaddr_converter_1_signal);
    mp_m_axi_awaddr_converter_1->vector_out(m_axi_concat_awaddr_out_1);
    mp_M01_AXI_transactor->AWADDR(m_m_axi_awaddr_converter_1_signal);
    mp_m_axi_awprot_converter_1 = new xsc::common::vector2vector_converter<3,6>("m_axi_awprot_converter_1");
    mp_m_axi_awprot_converter_1->vector_in(m_m_axi_awprot_converter_1_signal);
    mp_m_axi_awprot_converter_1->vector_out(m_axi_concat_awprot_out_1);
    mp_M01_AXI_transactor->AWPROT(m_m_axi_awprot_converter_1_signal);
    mp_m_axi_awvalid_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_awvalid_converter_1");
    mp_m_axi_awvalid_converter_1->scalar_in(m_m_axi_awvalid_converter_1_signal);
    mp_m_axi_awvalid_converter_1->vector_out(m_axi_concat_awvalid_out_1);
    mp_M01_AXI_transactor->AWVALID(m_m_axi_awvalid_converter_1_signal);
    mp_m_axi_awready_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_awready_converter_1");
    mp_m_axi_awready_converter_1->vector_in(m_axi_split_awready_out_1);
    mp_m_axi_awready_converter_1->scalar_out(m_m_axi_awready_converter_1_signal);
    mp_M01_AXI_transactor->AWREADY(m_m_axi_awready_converter_1_signal);
    mp_m_axi_wdata_converter_1 = new xsc::common::vector2vector_converter<32,64>("m_axi_wdata_converter_1");
    mp_m_axi_wdata_converter_1->vector_in(m_m_axi_wdata_converter_1_signal);
    mp_m_axi_wdata_converter_1->vector_out(m_axi_concat_wdata_out_1);
    mp_M01_AXI_transactor->WDATA(m_m_axi_wdata_converter_1_signal);
    mp_m_axi_wstrb_converter_1 = new xsc::common::vector2vector_converter<4,8>("m_axi_wstrb_converter_1");
    mp_m_axi_wstrb_converter_1->vector_in(m_m_axi_wstrb_converter_1_signal);
    mp_m_axi_wstrb_converter_1->vector_out(m_axi_concat_wstrb_out_1);
    mp_M01_AXI_transactor->WSTRB(m_m_axi_wstrb_converter_1_signal);
    mp_m_axi_wvalid_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_wvalid_converter_1");
    mp_m_axi_wvalid_converter_1->scalar_in(m_m_axi_wvalid_converter_1_signal);
    mp_m_axi_wvalid_converter_1->vector_out(m_axi_concat_wvalid_out_1);
    mp_M01_AXI_transactor->WVALID(m_m_axi_wvalid_converter_1_signal);
    mp_m_axi_wready_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_wready_converter_1");
    mp_m_axi_wready_converter_1->vector_in(m_axi_split_wready_out_1);
    mp_m_axi_wready_converter_1->scalar_out(m_m_axi_wready_converter_1_signal);
    mp_M01_AXI_transactor->WREADY(m_m_axi_wready_converter_1_signal);
    mp_m_axi_bresp_converter_1 = new xsc::common::vector2vector_converter<4,2>("m_axi_bresp_converter_1");
    mp_m_axi_bresp_converter_1->vector_in(m_axi_split_bresp_out_1);
    mp_m_axi_bresp_converter_1->vector_out(m_m_axi_bresp_converter_1_signal);
    mp_M01_AXI_transactor->BRESP(m_m_axi_bresp_converter_1_signal);
    mp_m_axi_bvalid_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_bvalid_converter_1");
    mp_m_axi_bvalid_converter_1->vector_in(m_axi_split_bvalid_out_1);
    mp_m_axi_bvalid_converter_1->scalar_out(m_m_axi_bvalid_converter_1_signal);
    mp_M01_AXI_transactor->BVALID(m_m_axi_bvalid_converter_1_signal);
    mp_m_axi_bready_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_bready_converter_1");
    mp_m_axi_bready_converter_1->scalar_in(m_m_axi_bready_converter_1_signal);
    mp_m_axi_bready_converter_1->vector_out(m_axi_concat_bready_out_1);
    mp_M01_AXI_transactor->BREADY(m_m_axi_bready_converter_1_signal);
    mp_m_axi_araddr_converter_1 = new xsc::common::vector2vector_converter<32,64>("m_axi_araddr_converter_1");
    mp_m_axi_araddr_converter_1->vector_in(m_m_axi_araddr_converter_1_signal);
    mp_m_axi_araddr_converter_1->vector_out(m_axi_concat_araddr_out_1);
    mp_M01_AXI_transactor->ARADDR(m_m_axi_araddr_converter_1_signal);
    mp_m_axi_arprot_converter_1 = new xsc::common::vector2vector_converter<3,6>("m_axi_arprot_converter_1");
    mp_m_axi_arprot_converter_1->vector_in(m_m_axi_arprot_converter_1_signal);
    mp_m_axi_arprot_converter_1->vector_out(m_axi_concat_arprot_out_1);
    mp_M01_AXI_transactor->ARPROT(m_m_axi_arprot_converter_1_signal);
    mp_m_axi_arvalid_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_arvalid_converter_1");
    mp_m_axi_arvalid_converter_1->scalar_in(m_m_axi_arvalid_converter_1_signal);
    mp_m_axi_arvalid_converter_1->vector_out(m_axi_concat_arvalid_out_1);
    mp_M01_AXI_transactor->ARVALID(m_m_axi_arvalid_converter_1_signal);
    mp_m_axi_arready_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_arready_converter_1");
    mp_m_axi_arready_converter_1->vector_in(m_axi_split_arready_out_1);
    mp_m_axi_arready_converter_1->scalar_out(m_m_axi_arready_converter_1_signal);
    mp_M01_AXI_transactor->ARREADY(m_m_axi_arready_converter_1_signal);
    mp_m_axi_rdata_converter_1 = new xsc::common::vector2vector_converter<64,32>("m_axi_rdata_converter_1");
    mp_m_axi_rdata_converter_1->vector_in(m_axi_split_rdata_out_1);
    mp_m_axi_rdata_converter_1->vector_out(m_m_axi_rdata_converter_1_signal);
    mp_M01_AXI_transactor->RDATA(m_m_axi_rdata_converter_1_signal);
    mp_m_axi_rresp_converter_1 = new xsc::common::vector2vector_converter<4,2>("m_axi_rresp_converter_1");
    mp_m_axi_rresp_converter_1->vector_in(m_axi_split_rresp_out_1);
    mp_m_axi_rresp_converter_1->vector_out(m_m_axi_rresp_converter_1_signal);
    mp_M01_AXI_transactor->RRESP(m_m_axi_rresp_converter_1_signal);
    mp_m_axi_rvalid_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_rvalid_converter_1");
    mp_m_axi_rvalid_converter_1->vector_in(m_axi_split_rvalid_out_1);
    mp_m_axi_rvalid_converter_1->scalar_out(m_m_axi_rvalid_converter_1_signal);
    mp_M01_AXI_transactor->RVALID(m_m_axi_rvalid_converter_1_signal);
    mp_m_axi_rready_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_rready_converter_1");
    mp_m_axi_rready_converter_1->scalar_in(m_m_axi_rready_converter_1_signal);
    mp_m_axi_rready_converter_1->vector_out(m_axi_concat_rready_out_1);
    mp_M01_AXI_transactor->RREADY(m_m_axi_rready_converter_1_signal);
    mp_M01_AXI_transactor->CLK(aclk);
    mp_M01_AXI_transactor->RST(aresetn);

    // M01_AXI' transactor sockets

    mp_impl->initiator_1_rd_socket->bind(*(mp_M01_AXI_transactor->rd_socket));
    mp_impl->initiator_1_wr_socket->bind(*(mp_M01_AXI_transactor->wr_socket));
  }
  else
  {
  }

}

#endif // RIVIERA




#ifdef VCSSYSTEMC
cl_sda_axil_xbar::cl_sda_axil_xbar(const sc_core::sc_module_name& nm) : cl_sda_axil_xbar_sc(nm),  aclk("aclk"), aresetn("aresetn"), s_axi_awaddr("s_axi_awaddr"), s_axi_awprot("s_axi_awprot"), s_axi_awvalid("s_axi_awvalid"), s_axi_awready("s_axi_awready"), s_axi_wdata("s_axi_wdata"), s_axi_wstrb("s_axi_wstrb"), s_axi_wvalid("s_axi_wvalid"), s_axi_wready("s_axi_wready"), s_axi_bresp("s_axi_bresp"), s_axi_bvalid("s_axi_bvalid"), s_axi_bready("s_axi_bready"), s_axi_araddr("s_axi_araddr"), s_axi_arprot("s_axi_arprot"), s_axi_arvalid("s_axi_arvalid"), s_axi_arready("s_axi_arready"), s_axi_rdata("s_axi_rdata"), s_axi_rresp("s_axi_rresp"), s_axi_rvalid("s_axi_rvalid"), s_axi_rready("s_axi_rready"), m_axi_awaddr("m_axi_awaddr"), m_axi_awprot("m_axi_awprot"), m_axi_awvalid("m_axi_awvalid"), m_axi_awready("m_axi_awready"), m_axi_wdata("m_axi_wdata"), m_axi_wstrb("m_axi_wstrb"), m_axi_wvalid("m_axi_wvalid"), m_axi_wready("m_axi_wready"), m_axi_bresp("m_axi_bresp"), m_axi_bvalid("m_axi_bvalid"), m_axi_bready("m_axi_bready"), m_axi_araddr("m_axi_araddr"), m_axi_arprot("m_axi_arprot"), m_axi_arvalid("m_axi_arvalid"), m_axi_arready("m_axi_arready"), m_axi_rdata("m_axi_rdata"), m_axi_rresp("m_axi_rresp"), m_axi_rvalid("m_axi_rvalid"), m_axi_rready("m_axi_rready")
{
  // initialize pins
  mp_impl->aclk(aclk);
  mp_impl->aresetn(aresetn);

  // initialize transactors
  mp_S00_AXI_transactor = NULL;
  mp_s_axi_awvalid_converter = NULL;
  mp_s_axi_awready_converter = NULL;
  mp_s_axi_wvalid_converter = NULL;
  mp_s_axi_wready_converter = NULL;
  mp_s_axi_bvalid_converter = NULL;
  mp_s_axi_bready_converter = NULL;
  mp_s_axi_arvalid_converter = NULL;
  mp_s_axi_arready_converter = NULL;
  mp_s_axi_rvalid_converter = NULL;
  mp_s_axi_rready_converter = NULL;
  mp_M00_AXI_transactor = NULL;
  mp_m_axi_awaddr_converter_0 = NULL;
  mp_m_axi_awprot_converter_0 = NULL;
  mp_m_axi_awvalid_converter_0 = NULL;
  mp_m_axi_awready_converter_0 = NULL;
  mp_m_axi_wdata_converter_0 = NULL;
  mp_m_axi_wstrb_converter_0 = NULL;
  mp_m_axi_wvalid_converter_0 = NULL;
  mp_m_axi_wready_converter_0 = NULL;
  mp_m_axi_bresp_converter_0 = NULL;
  mp_m_axi_bvalid_converter_0 = NULL;
  mp_m_axi_bready_converter_0 = NULL;
  mp_m_axi_araddr_converter_0 = NULL;
  mp_m_axi_arprot_converter_0 = NULL;
  mp_m_axi_arvalid_converter_0 = NULL;
  mp_m_axi_arready_converter_0 = NULL;
  mp_m_axi_rdata_converter_0 = NULL;
  mp_m_axi_rresp_converter_0 = NULL;
  mp_m_axi_rvalid_converter_0 = NULL;
  mp_m_axi_rready_converter_0 = NULL;
  mp_M01_AXI_transactor = NULL;
  mp_m_axi_awaddr_converter_1 = NULL;
  mp_m_axi_awprot_converter_1 = NULL;
  mp_m_axi_awvalid_converter_1 = NULL;
  mp_m_axi_awready_converter_1 = NULL;
  mp_m_axi_wdata_converter_1 = NULL;
  mp_m_axi_wstrb_converter_1 = NULL;
  mp_m_axi_wvalid_converter_1 = NULL;
  mp_m_axi_wready_converter_1 = NULL;
  mp_m_axi_bresp_converter_1 = NULL;
  mp_m_axi_bvalid_converter_1 = NULL;
  mp_m_axi_bready_converter_1 = NULL;
  mp_m_axi_araddr_converter_1 = NULL;
  mp_m_axi_arprot_converter_1 = NULL;
  mp_m_axi_arvalid_converter_1 = NULL;
  mp_m_axi_arready_converter_1 = NULL;
  mp_m_axi_rdata_converter_1 = NULL;
  mp_m_axi_rresp_converter_1 = NULL;
  mp_m_axi_rvalid_converter_1 = NULL;
  mp_m_axi_rready_converter_1 = NULL;

  // initialize port junctures
  mp_m_axi_concat_araddr = NULL;
  mp_m_axi_concat_arprot = NULL;
  mp_m_axi_concat_arvalid = NULL;
  mp_m_axi_concat_awaddr = NULL;
  mp_m_axi_concat_awprot = NULL;
  mp_m_axi_concat_awvalid = NULL;
  mp_m_axi_concat_bready = NULL;
  mp_m_axi_concat_rready = NULL;
  mp_m_axi_concat_wdata = NULL;
  mp_m_axi_concat_wstrb = NULL;
  mp_m_axi_concat_wvalid = NULL;
  mp_m_axi_split_arready = NULL;
  mp_m_axi_split_awready = NULL;
  mp_m_axi_split_bresp = NULL;
  mp_m_axi_split_bvalid = NULL;
  mp_m_axi_split_rdata = NULL;
  mp_m_axi_split_rresp = NULL;
  mp_m_axi_split_rvalid = NULL;
  mp_m_axi_split_wready = NULL;

  // Instantiate Socket Stubs

  // configure S00_AXI_transactor
    xsc::common_cpp::properties S00_AXI_transactor_param_props;
    S00_AXI_transactor_param_props.addLong("DATA_WIDTH", "32");
    S00_AXI_transactor_param_props.addLong("FREQ_HZ", "100000000");
    S00_AXI_transactor_param_props.addLong("ID_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("ADDR_WIDTH", "32");
    S00_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("HAS_BURST", "0");
    S00_AXI_transactor_param_props.addLong("HAS_LOCK", "0");
    S00_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    S00_AXI_transactor_param_props.addLong("HAS_CACHE", "0");
    S00_AXI_transactor_param_props.addLong("HAS_QOS", "0");
    S00_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    S00_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    S00_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    S00_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    S00_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    S00_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    S00_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    S00_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    S00_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    S00_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    S00_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    S00_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    S00_AXI_transactor_param_props.addLong("HAS_SIZE", "0");
    S00_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    S00_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    S00_AXI_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    S00_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    S00_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_S00_AXI_transactor = new xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>("S00_AXI_transactor", S00_AXI_transactor_param_props);
  mp_S00_AXI_transactor->AWADDR(s_axi_awaddr);
  mp_S00_AXI_transactor->AWPROT(s_axi_awprot);
  mp_s_axi_awvalid_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_awvalid_converter");
  mp_s_axi_awvalid_converter->vector_in(s_axi_awvalid);
  mp_s_axi_awvalid_converter->scalar_out(m_s_axi_awvalid_converter_signal);
  mp_S00_AXI_transactor->AWVALID(m_s_axi_awvalid_converter_signal);
  mp_s_axi_awready_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_awready_converter");
  mp_s_axi_awready_converter->scalar_in(m_s_axi_awready_converter_signal);
  mp_s_axi_awready_converter->vector_out(s_axi_awready);
  mp_S00_AXI_transactor->AWREADY(m_s_axi_awready_converter_signal);
  mp_S00_AXI_transactor->WDATA(s_axi_wdata);
  mp_S00_AXI_transactor->WSTRB(s_axi_wstrb);
  mp_s_axi_wvalid_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_wvalid_converter");
  mp_s_axi_wvalid_converter->vector_in(s_axi_wvalid);
  mp_s_axi_wvalid_converter->scalar_out(m_s_axi_wvalid_converter_signal);
  mp_S00_AXI_transactor->WVALID(m_s_axi_wvalid_converter_signal);
  mp_s_axi_wready_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_wready_converter");
  mp_s_axi_wready_converter->scalar_in(m_s_axi_wready_converter_signal);
  mp_s_axi_wready_converter->vector_out(s_axi_wready);
  mp_S00_AXI_transactor->WREADY(m_s_axi_wready_converter_signal);
  mp_S00_AXI_transactor->BRESP(s_axi_bresp);
  mp_s_axi_bvalid_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_bvalid_converter");
  mp_s_axi_bvalid_converter->scalar_in(m_s_axi_bvalid_converter_signal);
  mp_s_axi_bvalid_converter->vector_out(s_axi_bvalid);
  mp_S00_AXI_transactor->BVALID(m_s_axi_bvalid_converter_signal);
  mp_s_axi_bready_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_bready_converter");
  mp_s_axi_bready_converter->vector_in(s_axi_bready);
  mp_s_axi_bready_converter->scalar_out(m_s_axi_bready_converter_signal);
  mp_S00_AXI_transactor->BREADY(m_s_axi_bready_converter_signal);
  mp_S00_AXI_transactor->ARADDR(s_axi_araddr);
  mp_S00_AXI_transactor->ARPROT(s_axi_arprot);
  mp_s_axi_arvalid_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_arvalid_converter");
  mp_s_axi_arvalid_converter->vector_in(s_axi_arvalid);
  mp_s_axi_arvalid_converter->scalar_out(m_s_axi_arvalid_converter_signal);
  mp_S00_AXI_transactor->ARVALID(m_s_axi_arvalid_converter_signal);
  mp_s_axi_arready_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_arready_converter");
  mp_s_axi_arready_converter->scalar_in(m_s_axi_arready_converter_signal);
  mp_s_axi_arready_converter->vector_out(s_axi_arready);
  mp_S00_AXI_transactor->ARREADY(m_s_axi_arready_converter_signal);
  mp_S00_AXI_transactor->RDATA(s_axi_rdata);
  mp_S00_AXI_transactor->RRESP(s_axi_rresp);
  mp_s_axi_rvalid_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_rvalid_converter");
  mp_s_axi_rvalid_converter->scalar_in(m_s_axi_rvalid_converter_signal);
  mp_s_axi_rvalid_converter->vector_out(s_axi_rvalid);
  mp_S00_AXI_transactor->RVALID(m_s_axi_rvalid_converter_signal);
  mp_s_axi_rready_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_rready_converter");
  mp_s_axi_rready_converter->vector_in(s_axi_rready);
  mp_s_axi_rready_converter->scalar_out(m_s_axi_rready_converter_signal);
  mp_S00_AXI_transactor->RREADY(m_s_axi_rready_converter_signal);
  mp_S00_AXI_transactor->CLK(aclk);
  mp_S00_AXI_transactor->RST(aresetn);
  // configure M00_AXI_transactor
    xsc::common_cpp::properties M00_AXI_transactor_param_props;
    M00_AXI_transactor_param_props.addLong("DATA_WIDTH", "32");
    M00_AXI_transactor_param_props.addLong("FREQ_HZ", "100000000");
    M00_AXI_transactor_param_props.addLong("ID_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("ADDR_WIDTH", "32");
    M00_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("HAS_BURST", "0");
    M00_AXI_transactor_param_props.addLong("HAS_LOCK", "0");
    M00_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    M00_AXI_transactor_param_props.addLong("HAS_CACHE", "0");
    M00_AXI_transactor_param_props.addLong("HAS_QOS", "0");
    M00_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    M00_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    M00_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    M00_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    M00_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    M00_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    M00_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    M00_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    M00_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    M00_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    M00_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    M00_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    M00_AXI_transactor_param_props.addLong("HAS_SIZE", "0");
    M00_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    M00_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    M00_AXI_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    M00_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    M00_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_M00_AXI_transactor = new xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>("M00_AXI_transactor", M00_AXI_transactor_param_props);
  mp_m_axi_awaddr_converter_0 = new xsc::common::vector2vector_converter<32,64>("m_axi_awaddr_converter_0");
  mp_m_axi_concat_awaddr = new xsc::xsc_concatenator<64, 2>("m_axi_concat_awaddr");
  mp_m_axi_concat_awaddr->in_port[0](m_axi_concat_awaddr_out_0);
  mp_m_axi_concat_awaddr->out_port(m_axi_awaddr);
    mp_m_axi_concat_awaddr->offset_port(0, 0);
  mp_m_axi_awaddr_converter_0->vector_in(m_m_axi_awaddr_converter_0_signal);
  mp_m_axi_awaddr_converter_0->vector_out(m_axi_concat_awaddr_out_0);
  mp_M00_AXI_transactor->AWADDR(m_m_axi_awaddr_converter_0_signal);
  mp_m_axi_awprot_converter_0 = new xsc::common::vector2vector_converter<3,6>("m_axi_awprot_converter_0");
  mp_m_axi_concat_awprot = new xsc::xsc_concatenator<6, 2>("m_axi_concat_awprot");
  mp_m_axi_concat_awprot->in_port[0](m_axi_concat_awprot_out_0);
  mp_m_axi_concat_awprot->out_port(m_axi_awprot);
    mp_m_axi_concat_awprot->offset_port(0, 0);
  mp_m_axi_awprot_converter_0->vector_in(m_m_axi_awprot_converter_0_signal);
  mp_m_axi_awprot_converter_0->vector_out(m_axi_concat_awprot_out_0);
  mp_M00_AXI_transactor->AWPROT(m_m_axi_awprot_converter_0_signal);
  mp_m_axi_awvalid_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_awvalid_converter_0");
  mp_m_axi_concat_awvalid = new xsc::xsc_concatenator<2, 2>("m_axi_concat_awvalid");
  mp_m_axi_concat_awvalid->in_port[0](m_axi_concat_awvalid_out_0);
  mp_m_axi_concat_awvalid->out_port(m_axi_awvalid);
    mp_m_axi_concat_awvalid->offset_port(0, 0);
  mp_m_axi_awvalid_converter_0->scalar_in(m_m_axi_awvalid_converter_0_signal);
  mp_m_axi_awvalid_converter_0->vector_out(m_axi_concat_awvalid_out_0);
  mp_M00_AXI_transactor->AWVALID(m_m_axi_awvalid_converter_0_signal);
  mp_m_axi_awready_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_awready_converter_0");
  mp_m_axi_split_awready = new xsc::xsc_split<2, 2>("m_axi_split_awready");
  mp_m_axi_split_awready->in_port(m_axi_awready);
  mp_m_axi_split_awready->out_port[0](m_axi_split_awready_out_0);
    mp_m_axi_split_awready->add_mask(0,1,0);
  mp_m_axi_awready_converter_0->vector_in(m_axi_split_awready_out_0);
  mp_m_axi_awready_converter_0->scalar_out(m_m_axi_awready_converter_0_signal);
  mp_M00_AXI_transactor->AWREADY(m_m_axi_awready_converter_0_signal);
  mp_m_axi_wdata_converter_0 = new xsc::common::vector2vector_converter<32,64>("m_axi_wdata_converter_0");
  mp_m_axi_concat_wdata = new xsc::xsc_concatenator<64, 2>("m_axi_concat_wdata");
  mp_m_axi_concat_wdata->in_port[0](m_axi_concat_wdata_out_0);
  mp_m_axi_concat_wdata->out_port(m_axi_wdata);
    mp_m_axi_concat_wdata->offset_port(0, 0);
  mp_m_axi_wdata_converter_0->vector_in(m_m_axi_wdata_converter_0_signal);
  mp_m_axi_wdata_converter_0->vector_out(m_axi_concat_wdata_out_0);
  mp_M00_AXI_transactor->WDATA(m_m_axi_wdata_converter_0_signal);
  mp_m_axi_wstrb_converter_0 = new xsc::common::vector2vector_converter<4,8>("m_axi_wstrb_converter_0");
  mp_m_axi_concat_wstrb = new xsc::xsc_concatenator<8, 2>("m_axi_concat_wstrb");
  mp_m_axi_concat_wstrb->in_port[0](m_axi_concat_wstrb_out_0);
  mp_m_axi_concat_wstrb->out_port(m_axi_wstrb);
    mp_m_axi_concat_wstrb->offset_port(0, 0);
  mp_m_axi_wstrb_converter_0->vector_in(m_m_axi_wstrb_converter_0_signal);
  mp_m_axi_wstrb_converter_0->vector_out(m_axi_concat_wstrb_out_0);
  mp_M00_AXI_transactor->WSTRB(m_m_axi_wstrb_converter_0_signal);
  mp_m_axi_wvalid_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_wvalid_converter_0");
  mp_m_axi_concat_wvalid = new xsc::xsc_concatenator<2, 2>("m_axi_concat_wvalid");
  mp_m_axi_concat_wvalid->in_port[0](m_axi_concat_wvalid_out_0);
  mp_m_axi_concat_wvalid->out_port(m_axi_wvalid);
    mp_m_axi_concat_wvalid->offset_port(0, 0);
  mp_m_axi_wvalid_converter_0->scalar_in(m_m_axi_wvalid_converter_0_signal);
  mp_m_axi_wvalid_converter_0->vector_out(m_axi_concat_wvalid_out_0);
  mp_M00_AXI_transactor->WVALID(m_m_axi_wvalid_converter_0_signal);
  mp_m_axi_wready_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_wready_converter_0");
  mp_m_axi_split_wready = new xsc::xsc_split<2, 2>("m_axi_split_wready");
  mp_m_axi_split_wready->in_port(m_axi_wready);
  mp_m_axi_split_wready->out_port[0](m_axi_split_wready_out_0);
    mp_m_axi_split_wready->add_mask(0,1,0);
  mp_m_axi_wready_converter_0->vector_in(m_axi_split_wready_out_0);
  mp_m_axi_wready_converter_0->scalar_out(m_m_axi_wready_converter_0_signal);
  mp_M00_AXI_transactor->WREADY(m_m_axi_wready_converter_0_signal);
  mp_m_axi_bresp_converter_0 = new xsc::common::vector2vector_converter<4,2>("m_axi_bresp_converter_0");
  mp_m_axi_split_bresp = new xsc::xsc_split<4, 2>("m_axi_split_bresp");
  mp_m_axi_split_bresp->in_port(m_axi_bresp);
  mp_m_axi_split_bresp->out_port[0](m_axi_split_bresp_out_0);
    mp_m_axi_split_bresp->add_mask(0,2,0);
  mp_m_axi_bresp_converter_0->vector_in(m_axi_split_bresp_out_0);
  mp_m_axi_bresp_converter_0->vector_out(m_m_axi_bresp_converter_0_signal);
  mp_M00_AXI_transactor->BRESP(m_m_axi_bresp_converter_0_signal);
  mp_m_axi_bvalid_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_bvalid_converter_0");
  mp_m_axi_split_bvalid = new xsc::xsc_split<2, 2>("m_axi_split_bvalid");
  mp_m_axi_split_bvalid->in_port(m_axi_bvalid);
  mp_m_axi_split_bvalid->out_port[0](m_axi_split_bvalid_out_0);
    mp_m_axi_split_bvalid->add_mask(0,1,0);
  mp_m_axi_bvalid_converter_0->vector_in(m_axi_split_bvalid_out_0);
  mp_m_axi_bvalid_converter_0->scalar_out(m_m_axi_bvalid_converter_0_signal);
  mp_M00_AXI_transactor->BVALID(m_m_axi_bvalid_converter_0_signal);
  mp_m_axi_bready_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_bready_converter_0");
  mp_m_axi_concat_bready = new xsc::xsc_concatenator<2, 2>("m_axi_concat_bready");
  mp_m_axi_concat_bready->in_port[0](m_axi_concat_bready_out_0);
  mp_m_axi_concat_bready->out_port(m_axi_bready);
    mp_m_axi_concat_bready->offset_port(0, 0);
  mp_m_axi_bready_converter_0->scalar_in(m_m_axi_bready_converter_0_signal);
  mp_m_axi_bready_converter_0->vector_out(m_axi_concat_bready_out_0);
  mp_M00_AXI_transactor->BREADY(m_m_axi_bready_converter_0_signal);
  mp_m_axi_araddr_converter_0 = new xsc::common::vector2vector_converter<32,64>("m_axi_araddr_converter_0");
  mp_m_axi_concat_araddr = new xsc::xsc_concatenator<64, 2>("m_axi_concat_araddr");
  mp_m_axi_concat_araddr->in_port[0](m_axi_concat_araddr_out_0);
  mp_m_axi_concat_araddr->out_port(m_axi_araddr);
    mp_m_axi_concat_araddr->offset_port(0, 0);
  mp_m_axi_araddr_converter_0->vector_in(m_m_axi_araddr_converter_0_signal);
  mp_m_axi_araddr_converter_0->vector_out(m_axi_concat_araddr_out_0);
  mp_M00_AXI_transactor->ARADDR(m_m_axi_araddr_converter_0_signal);
  mp_m_axi_arprot_converter_0 = new xsc::common::vector2vector_converter<3,6>("m_axi_arprot_converter_0");
  mp_m_axi_concat_arprot = new xsc::xsc_concatenator<6, 2>("m_axi_concat_arprot");
  mp_m_axi_concat_arprot->in_port[0](m_axi_concat_arprot_out_0);
  mp_m_axi_concat_arprot->out_port(m_axi_arprot);
    mp_m_axi_concat_arprot->offset_port(0, 0);
  mp_m_axi_arprot_converter_0->vector_in(m_m_axi_arprot_converter_0_signal);
  mp_m_axi_arprot_converter_0->vector_out(m_axi_concat_arprot_out_0);
  mp_M00_AXI_transactor->ARPROT(m_m_axi_arprot_converter_0_signal);
  mp_m_axi_arvalid_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_arvalid_converter_0");
  mp_m_axi_concat_arvalid = new xsc::xsc_concatenator<2, 2>("m_axi_concat_arvalid");
  mp_m_axi_concat_arvalid->in_port[0](m_axi_concat_arvalid_out_0);
  mp_m_axi_concat_arvalid->out_port(m_axi_arvalid);
    mp_m_axi_concat_arvalid->offset_port(0, 0);
  mp_m_axi_arvalid_converter_0->scalar_in(m_m_axi_arvalid_converter_0_signal);
  mp_m_axi_arvalid_converter_0->vector_out(m_axi_concat_arvalid_out_0);
  mp_M00_AXI_transactor->ARVALID(m_m_axi_arvalid_converter_0_signal);
  mp_m_axi_arready_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_arready_converter_0");
  mp_m_axi_split_arready = new xsc::xsc_split<2, 2>("m_axi_split_arready");
  mp_m_axi_split_arready->in_port(m_axi_arready);
  mp_m_axi_split_arready->out_port[0](m_axi_split_arready_out_0);
    mp_m_axi_split_arready->add_mask(0,1,0);
  mp_m_axi_arready_converter_0->vector_in(m_axi_split_arready_out_0);
  mp_m_axi_arready_converter_0->scalar_out(m_m_axi_arready_converter_0_signal);
  mp_M00_AXI_transactor->ARREADY(m_m_axi_arready_converter_0_signal);
  mp_m_axi_rdata_converter_0 = new xsc::common::vector2vector_converter<64,32>("m_axi_rdata_converter_0");
  mp_m_axi_split_rdata = new xsc::xsc_split<64, 2>("m_axi_split_rdata");
  mp_m_axi_split_rdata->in_port(m_axi_rdata);
  mp_m_axi_split_rdata->out_port[0](m_axi_split_rdata_out_0);
    mp_m_axi_split_rdata->add_mask(0,32,0);
  mp_m_axi_rdata_converter_0->vector_in(m_axi_split_rdata_out_0);
  mp_m_axi_rdata_converter_0->vector_out(m_m_axi_rdata_converter_0_signal);
  mp_M00_AXI_transactor->RDATA(m_m_axi_rdata_converter_0_signal);
  mp_m_axi_rresp_converter_0 = new xsc::common::vector2vector_converter<4,2>("m_axi_rresp_converter_0");
  mp_m_axi_split_rresp = new xsc::xsc_split<4, 2>("m_axi_split_rresp");
  mp_m_axi_split_rresp->in_port(m_axi_rresp);
  mp_m_axi_split_rresp->out_port[0](m_axi_split_rresp_out_0);
    mp_m_axi_split_rresp->add_mask(0,2,0);
  mp_m_axi_rresp_converter_0->vector_in(m_axi_split_rresp_out_0);
  mp_m_axi_rresp_converter_0->vector_out(m_m_axi_rresp_converter_0_signal);
  mp_M00_AXI_transactor->RRESP(m_m_axi_rresp_converter_0_signal);
  mp_m_axi_rvalid_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_rvalid_converter_0");
  mp_m_axi_split_rvalid = new xsc::xsc_split<2, 2>("m_axi_split_rvalid");
  mp_m_axi_split_rvalid->in_port(m_axi_rvalid);
  mp_m_axi_split_rvalid->out_port[0](m_axi_split_rvalid_out_0);
    mp_m_axi_split_rvalid->add_mask(0,1,0);
  mp_m_axi_rvalid_converter_0->vector_in(m_axi_split_rvalid_out_0);
  mp_m_axi_rvalid_converter_0->scalar_out(m_m_axi_rvalid_converter_0_signal);
  mp_M00_AXI_transactor->RVALID(m_m_axi_rvalid_converter_0_signal);
  mp_m_axi_rready_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_rready_converter_0");
  mp_m_axi_concat_rready = new xsc::xsc_concatenator<2, 2>("m_axi_concat_rready");
  mp_m_axi_concat_rready->in_port[0](m_axi_concat_rready_out_0);
  mp_m_axi_concat_rready->out_port(m_axi_rready);
    mp_m_axi_concat_rready->offset_port(0, 0);
  mp_m_axi_rready_converter_0->scalar_in(m_m_axi_rready_converter_0_signal);
  mp_m_axi_rready_converter_0->vector_out(m_axi_concat_rready_out_0);
  mp_M00_AXI_transactor->RREADY(m_m_axi_rready_converter_0_signal);
  mp_M00_AXI_transactor->CLK(aclk);
  mp_M00_AXI_transactor->RST(aresetn);
  // configure M01_AXI_transactor
    xsc::common_cpp::properties M01_AXI_transactor_param_props;
    M01_AXI_transactor_param_props.addLong("DATA_WIDTH", "32");
    M01_AXI_transactor_param_props.addLong("FREQ_HZ", "100000000");
    M01_AXI_transactor_param_props.addLong("ID_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("ADDR_WIDTH", "32");
    M01_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("HAS_BURST", "0");
    M01_AXI_transactor_param_props.addLong("HAS_LOCK", "0");
    M01_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    M01_AXI_transactor_param_props.addLong("HAS_CACHE", "0");
    M01_AXI_transactor_param_props.addLong("HAS_QOS", "0");
    M01_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    M01_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    M01_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    M01_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    M01_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    M01_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    M01_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    M01_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    M01_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    M01_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    M01_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    M01_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    M01_AXI_transactor_param_props.addLong("HAS_SIZE", "0");
    M01_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    M01_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    M01_AXI_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    M01_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    M01_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_M01_AXI_transactor = new xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>("M01_AXI_transactor", M01_AXI_transactor_param_props);
  mp_m_axi_awaddr_converter_1 = new xsc::common::vector2vector_converter<32,64>("m_axi_awaddr_converter_1");
  mp_m_axi_concat_awaddr->in_port[1](m_axi_concat_awaddr_out_1);
  mp_m_axi_concat_awaddr->offset_port(1, 32);
  mp_m_axi_awaddr_converter_1->vector_in(m_m_axi_awaddr_converter_1_signal);
  mp_m_axi_awaddr_converter_1->vector_out(m_axi_concat_awaddr_out_1);
  mp_M01_AXI_transactor->AWADDR(m_m_axi_awaddr_converter_1_signal);
  mp_m_axi_awprot_converter_1 = new xsc::common::vector2vector_converter<3,6>("m_axi_awprot_converter_1");
  mp_m_axi_concat_awprot->in_port[1](m_axi_concat_awprot_out_1);
  mp_m_axi_concat_awprot->offset_port(1, 3);
  mp_m_axi_awprot_converter_1->vector_in(m_m_axi_awprot_converter_1_signal);
  mp_m_axi_awprot_converter_1->vector_out(m_axi_concat_awprot_out_1);
  mp_M01_AXI_transactor->AWPROT(m_m_axi_awprot_converter_1_signal);
  mp_m_axi_awvalid_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_awvalid_converter_1");
  mp_m_axi_concat_awvalid->in_port[1](m_axi_concat_awvalid_out_1);
  mp_m_axi_concat_awvalid->offset_port(1, 1);
  mp_m_axi_awvalid_converter_1->scalar_in(m_m_axi_awvalid_converter_1_signal);
  mp_m_axi_awvalid_converter_1->vector_out(m_axi_concat_awvalid_out_1);
  mp_M01_AXI_transactor->AWVALID(m_m_axi_awvalid_converter_1_signal);
  mp_m_axi_awready_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_awready_converter_1");
  
  mp_m_axi_split_awready->out_port[1](m_axi_split_awready_out_1);
    mp_m_axi_split_awready->add_mask(1,2,1);
  mp_m_axi_awready_converter_1->vector_in(m_axi_split_awready_out_1);
  mp_m_axi_awready_converter_1->scalar_out(m_m_axi_awready_converter_1_signal);
  mp_M01_AXI_transactor->AWREADY(m_m_axi_awready_converter_1_signal);
  mp_m_axi_wdata_converter_1 = new xsc::common::vector2vector_converter<32,64>("m_axi_wdata_converter_1");
  mp_m_axi_concat_wdata->in_port[1](m_axi_concat_wdata_out_1);
  mp_m_axi_concat_wdata->offset_port(1, 32);
  mp_m_axi_wdata_converter_1->vector_in(m_m_axi_wdata_converter_1_signal);
  mp_m_axi_wdata_converter_1->vector_out(m_axi_concat_wdata_out_1);
  mp_M01_AXI_transactor->WDATA(m_m_axi_wdata_converter_1_signal);
  mp_m_axi_wstrb_converter_1 = new xsc::common::vector2vector_converter<4,8>("m_axi_wstrb_converter_1");
  mp_m_axi_concat_wstrb->in_port[1](m_axi_concat_wstrb_out_1);
  mp_m_axi_concat_wstrb->offset_port(1, 4);
  mp_m_axi_wstrb_converter_1->vector_in(m_m_axi_wstrb_converter_1_signal);
  mp_m_axi_wstrb_converter_1->vector_out(m_axi_concat_wstrb_out_1);
  mp_M01_AXI_transactor->WSTRB(m_m_axi_wstrb_converter_1_signal);
  mp_m_axi_wvalid_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_wvalid_converter_1");
  mp_m_axi_concat_wvalid->in_port[1](m_axi_concat_wvalid_out_1);
  mp_m_axi_concat_wvalid->offset_port(1, 1);
  mp_m_axi_wvalid_converter_1->scalar_in(m_m_axi_wvalid_converter_1_signal);
  mp_m_axi_wvalid_converter_1->vector_out(m_axi_concat_wvalid_out_1);
  mp_M01_AXI_transactor->WVALID(m_m_axi_wvalid_converter_1_signal);
  mp_m_axi_wready_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_wready_converter_1");
  
  mp_m_axi_split_wready->out_port[1](m_axi_split_wready_out_1);
    mp_m_axi_split_wready->add_mask(1,2,1);
  mp_m_axi_wready_converter_1->vector_in(m_axi_split_wready_out_1);
  mp_m_axi_wready_converter_1->scalar_out(m_m_axi_wready_converter_1_signal);
  mp_M01_AXI_transactor->WREADY(m_m_axi_wready_converter_1_signal);
  mp_m_axi_bresp_converter_1 = new xsc::common::vector2vector_converter<4,2>("m_axi_bresp_converter_1");
  
  mp_m_axi_split_bresp->out_port[1](m_axi_split_bresp_out_1);
    mp_m_axi_split_bresp->add_mask(1,4,2);
  mp_m_axi_bresp_converter_1->vector_in(m_axi_split_bresp_out_1);
  mp_m_axi_bresp_converter_1->vector_out(m_m_axi_bresp_converter_1_signal);
  mp_M01_AXI_transactor->BRESP(m_m_axi_bresp_converter_1_signal);
  mp_m_axi_bvalid_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_bvalid_converter_1");
  
  mp_m_axi_split_bvalid->out_port[1](m_axi_split_bvalid_out_1);
    mp_m_axi_split_bvalid->add_mask(1,2,1);
  mp_m_axi_bvalid_converter_1->vector_in(m_axi_split_bvalid_out_1);
  mp_m_axi_bvalid_converter_1->scalar_out(m_m_axi_bvalid_converter_1_signal);
  mp_M01_AXI_transactor->BVALID(m_m_axi_bvalid_converter_1_signal);
  mp_m_axi_bready_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_bready_converter_1");
  mp_m_axi_concat_bready->in_port[1](m_axi_concat_bready_out_1);
  mp_m_axi_concat_bready->offset_port(1, 1);
  mp_m_axi_bready_converter_1->scalar_in(m_m_axi_bready_converter_1_signal);
  mp_m_axi_bready_converter_1->vector_out(m_axi_concat_bready_out_1);
  mp_M01_AXI_transactor->BREADY(m_m_axi_bready_converter_1_signal);
  mp_m_axi_araddr_converter_1 = new xsc::common::vector2vector_converter<32,64>("m_axi_araddr_converter_1");
  mp_m_axi_concat_araddr->in_port[1](m_axi_concat_araddr_out_1);
  mp_m_axi_concat_araddr->offset_port(1, 32);
  mp_m_axi_araddr_converter_1->vector_in(m_m_axi_araddr_converter_1_signal);
  mp_m_axi_araddr_converter_1->vector_out(m_axi_concat_araddr_out_1);
  mp_M01_AXI_transactor->ARADDR(m_m_axi_araddr_converter_1_signal);
  mp_m_axi_arprot_converter_1 = new xsc::common::vector2vector_converter<3,6>("m_axi_arprot_converter_1");
  mp_m_axi_concat_arprot->in_port[1](m_axi_concat_arprot_out_1);
  mp_m_axi_concat_arprot->offset_port(1, 3);
  mp_m_axi_arprot_converter_1->vector_in(m_m_axi_arprot_converter_1_signal);
  mp_m_axi_arprot_converter_1->vector_out(m_axi_concat_arprot_out_1);
  mp_M01_AXI_transactor->ARPROT(m_m_axi_arprot_converter_1_signal);
  mp_m_axi_arvalid_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_arvalid_converter_1");
  mp_m_axi_concat_arvalid->in_port[1](m_axi_concat_arvalid_out_1);
  mp_m_axi_concat_arvalid->offset_port(1, 1);
  mp_m_axi_arvalid_converter_1->scalar_in(m_m_axi_arvalid_converter_1_signal);
  mp_m_axi_arvalid_converter_1->vector_out(m_axi_concat_arvalid_out_1);
  mp_M01_AXI_transactor->ARVALID(m_m_axi_arvalid_converter_1_signal);
  mp_m_axi_arready_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_arready_converter_1");
  
  mp_m_axi_split_arready->out_port[1](m_axi_split_arready_out_1);
    mp_m_axi_split_arready->add_mask(1,2,1);
  mp_m_axi_arready_converter_1->vector_in(m_axi_split_arready_out_1);
  mp_m_axi_arready_converter_1->scalar_out(m_m_axi_arready_converter_1_signal);
  mp_M01_AXI_transactor->ARREADY(m_m_axi_arready_converter_1_signal);
  mp_m_axi_rdata_converter_1 = new xsc::common::vector2vector_converter<64,32>("m_axi_rdata_converter_1");
  
  mp_m_axi_split_rdata->out_port[1](m_axi_split_rdata_out_1);
    mp_m_axi_split_rdata->add_mask(1,64,32);
  mp_m_axi_rdata_converter_1->vector_in(m_axi_split_rdata_out_1);
  mp_m_axi_rdata_converter_1->vector_out(m_m_axi_rdata_converter_1_signal);
  mp_M01_AXI_transactor->RDATA(m_m_axi_rdata_converter_1_signal);
  mp_m_axi_rresp_converter_1 = new xsc::common::vector2vector_converter<4,2>("m_axi_rresp_converter_1");
  
  mp_m_axi_split_rresp->out_port[1](m_axi_split_rresp_out_1);
    mp_m_axi_split_rresp->add_mask(1,4,2);
  mp_m_axi_rresp_converter_1->vector_in(m_axi_split_rresp_out_1);
  mp_m_axi_rresp_converter_1->vector_out(m_m_axi_rresp_converter_1_signal);
  mp_M01_AXI_transactor->RRESP(m_m_axi_rresp_converter_1_signal);
  mp_m_axi_rvalid_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_rvalid_converter_1");
  
  mp_m_axi_split_rvalid->out_port[1](m_axi_split_rvalid_out_1);
    mp_m_axi_split_rvalid->add_mask(1,2,1);
  mp_m_axi_rvalid_converter_1->vector_in(m_axi_split_rvalid_out_1);
  mp_m_axi_rvalid_converter_1->scalar_out(m_m_axi_rvalid_converter_1_signal);
  mp_M01_AXI_transactor->RVALID(m_m_axi_rvalid_converter_1_signal);
  mp_m_axi_rready_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_rready_converter_1");
  mp_m_axi_concat_rready->in_port[1](m_axi_concat_rready_out_1);
  mp_m_axi_concat_rready->offset_port(1, 1);
  mp_m_axi_rready_converter_1->scalar_in(m_m_axi_rready_converter_1_signal);
  mp_m_axi_rready_converter_1->vector_out(m_axi_concat_rready_out_1);
  mp_M01_AXI_transactor->RREADY(m_m_axi_rready_converter_1_signal);
  mp_M01_AXI_transactor->CLK(aclk);
  mp_M01_AXI_transactor->RST(aresetn);

  // initialize transactors stubs
  S00_AXI_transactor_target_wr_socket_stub = nullptr;
  S00_AXI_transactor_target_rd_socket_stub = nullptr;
  M00_AXI_transactor_initiator_wr_socket_stub = nullptr;
  M00_AXI_transactor_initiator_rd_socket_stub = nullptr;
  M01_AXI_transactor_initiator_wr_socket_stub = nullptr;
  M01_AXI_transactor_initiator_rd_socket_stub = nullptr;

}

void cl_sda_axil_xbar::before_end_of_elaboration()
{
  // configure 'S00_AXI' transactor
  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_sda_axil_xbar", "S00_AXI_TLM_MODE") != 1)
  {
    mp_impl->target_0_rd_socket->bind(*(mp_S00_AXI_transactor->rd_socket));
    mp_impl->target_0_wr_socket->bind(*(mp_S00_AXI_transactor->wr_socket));
  
  }
  else
  {
    S00_AXI_transactor_target_wr_socket_stub = new xtlm::xtlm_aximm_target_stub("wr_socket",0);
    S00_AXI_transactor_target_wr_socket_stub->bind(*(mp_S00_AXI_transactor->wr_socket));
    S00_AXI_transactor_target_rd_socket_stub = new xtlm::xtlm_aximm_target_stub("rd_socket",0);
    S00_AXI_transactor_target_rd_socket_stub->bind(*(mp_S00_AXI_transactor->rd_socket));
    mp_S00_AXI_transactor->disable_transactor();
  }

  // configure 'M00_AXI' transactor
  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_sda_axil_xbar", "M00_AXI_TLM_MODE") != 1)
  {
    mp_impl->initiator_0_rd_socket->bind(*(mp_M00_AXI_transactor->rd_socket));
    mp_impl->initiator_0_wr_socket->bind(*(mp_M00_AXI_transactor->wr_socket));
  
  }
  else
  {
    M00_AXI_transactor_initiator_wr_socket_stub = new xtlm::xtlm_aximm_initiator_stub("wr_socket",0);
    M00_AXI_transactor_initiator_wr_socket_stub->bind(*(mp_M00_AXI_transactor->wr_socket));
    M00_AXI_transactor_initiator_rd_socket_stub = new xtlm::xtlm_aximm_initiator_stub("rd_socket",0);
    M00_AXI_transactor_initiator_rd_socket_stub->bind(*(mp_M00_AXI_transactor->rd_socket));
    mp_M00_AXI_transactor->disable_transactor();
  }

  // configure 'M01_AXI' transactor
  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_sda_axil_xbar", "M01_AXI_TLM_MODE") != 1)
  {
    mp_impl->initiator_1_rd_socket->bind(*(mp_M01_AXI_transactor->rd_socket));
    mp_impl->initiator_1_wr_socket->bind(*(mp_M01_AXI_transactor->wr_socket));
  
  }
  else
  {
    M01_AXI_transactor_initiator_wr_socket_stub = new xtlm::xtlm_aximm_initiator_stub("wr_socket",0);
    M01_AXI_transactor_initiator_wr_socket_stub->bind(*(mp_M01_AXI_transactor->wr_socket));
    M01_AXI_transactor_initiator_rd_socket_stub = new xtlm::xtlm_aximm_initiator_stub("rd_socket",0);
    M01_AXI_transactor_initiator_rd_socket_stub->bind(*(mp_M01_AXI_transactor->rd_socket));
    mp_M01_AXI_transactor->disable_transactor();
  }

}

#endif // VCSSYSTEMC




#ifdef MTI_SYSTEMC
cl_sda_axil_xbar::cl_sda_axil_xbar(const sc_core::sc_module_name& nm) : cl_sda_axil_xbar_sc(nm),  aclk("aclk"), aresetn("aresetn"), s_axi_awaddr("s_axi_awaddr"), s_axi_awprot("s_axi_awprot"), s_axi_awvalid("s_axi_awvalid"), s_axi_awready("s_axi_awready"), s_axi_wdata("s_axi_wdata"), s_axi_wstrb("s_axi_wstrb"), s_axi_wvalid("s_axi_wvalid"), s_axi_wready("s_axi_wready"), s_axi_bresp("s_axi_bresp"), s_axi_bvalid("s_axi_bvalid"), s_axi_bready("s_axi_bready"), s_axi_araddr("s_axi_araddr"), s_axi_arprot("s_axi_arprot"), s_axi_arvalid("s_axi_arvalid"), s_axi_arready("s_axi_arready"), s_axi_rdata("s_axi_rdata"), s_axi_rresp("s_axi_rresp"), s_axi_rvalid("s_axi_rvalid"), s_axi_rready("s_axi_rready"), m_axi_awaddr("m_axi_awaddr"), m_axi_awprot("m_axi_awprot"), m_axi_awvalid("m_axi_awvalid"), m_axi_awready("m_axi_awready"), m_axi_wdata("m_axi_wdata"), m_axi_wstrb("m_axi_wstrb"), m_axi_wvalid("m_axi_wvalid"), m_axi_wready("m_axi_wready"), m_axi_bresp("m_axi_bresp"), m_axi_bvalid("m_axi_bvalid"), m_axi_bready("m_axi_bready"), m_axi_araddr("m_axi_araddr"), m_axi_arprot("m_axi_arprot"), m_axi_arvalid("m_axi_arvalid"), m_axi_arready("m_axi_arready"), m_axi_rdata("m_axi_rdata"), m_axi_rresp("m_axi_rresp"), m_axi_rvalid("m_axi_rvalid"), m_axi_rready("m_axi_rready")
{
  // initialize pins
  mp_impl->aclk(aclk);
  mp_impl->aresetn(aresetn);

  // initialize transactors
  mp_S00_AXI_transactor = NULL;
  mp_s_axi_awvalid_converter = NULL;
  mp_s_axi_awready_converter = NULL;
  mp_s_axi_wvalid_converter = NULL;
  mp_s_axi_wready_converter = NULL;
  mp_s_axi_bvalid_converter = NULL;
  mp_s_axi_bready_converter = NULL;
  mp_s_axi_arvalid_converter = NULL;
  mp_s_axi_arready_converter = NULL;
  mp_s_axi_rvalid_converter = NULL;
  mp_s_axi_rready_converter = NULL;
  mp_M00_AXI_transactor = NULL;
  mp_m_axi_awaddr_converter_0 = NULL;
  mp_m_axi_awprot_converter_0 = NULL;
  mp_m_axi_awvalid_converter_0 = NULL;
  mp_m_axi_awready_converter_0 = NULL;
  mp_m_axi_wdata_converter_0 = NULL;
  mp_m_axi_wstrb_converter_0 = NULL;
  mp_m_axi_wvalid_converter_0 = NULL;
  mp_m_axi_wready_converter_0 = NULL;
  mp_m_axi_bresp_converter_0 = NULL;
  mp_m_axi_bvalid_converter_0 = NULL;
  mp_m_axi_bready_converter_0 = NULL;
  mp_m_axi_araddr_converter_0 = NULL;
  mp_m_axi_arprot_converter_0 = NULL;
  mp_m_axi_arvalid_converter_0 = NULL;
  mp_m_axi_arready_converter_0 = NULL;
  mp_m_axi_rdata_converter_0 = NULL;
  mp_m_axi_rresp_converter_0 = NULL;
  mp_m_axi_rvalid_converter_0 = NULL;
  mp_m_axi_rready_converter_0 = NULL;
  mp_M01_AXI_transactor = NULL;
  mp_m_axi_awaddr_converter_1 = NULL;
  mp_m_axi_awprot_converter_1 = NULL;
  mp_m_axi_awvalid_converter_1 = NULL;
  mp_m_axi_awready_converter_1 = NULL;
  mp_m_axi_wdata_converter_1 = NULL;
  mp_m_axi_wstrb_converter_1 = NULL;
  mp_m_axi_wvalid_converter_1 = NULL;
  mp_m_axi_wready_converter_1 = NULL;
  mp_m_axi_bresp_converter_1 = NULL;
  mp_m_axi_bvalid_converter_1 = NULL;
  mp_m_axi_bready_converter_1 = NULL;
  mp_m_axi_araddr_converter_1 = NULL;
  mp_m_axi_arprot_converter_1 = NULL;
  mp_m_axi_arvalid_converter_1 = NULL;
  mp_m_axi_arready_converter_1 = NULL;
  mp_m_axi_rdata_converter_1 = NULL;
  mp_m_axi_rresp_converter_1 = NULL;
  mp_m_axi_rvalid_converter_1 = NULL;
  mp_m_axi_rready_converter_1 = NULL;

  // initialize port junctures
  mp_m_axi_concat_araddr = NULL;
  mp_m_axi_concat_arprot = NULL;
  mp_m_axi_concat_arvalid = NULL;
  mp_m_axi_concat_awaddr = NULL;
  mp_m_axi_concat_awprot = NULL;
  mp_m_axi_concat_awvalid = NULL;
  mp_m_axi_concat_bready = NULL;
  mp_m_axi_concat_rready = NULL;
  mp_m_axi_concat_wdata = NULL;
  mp_m_axi_concat_wstrb = NULL;
  mp_m_axi_concat_wvalid = NULL;
  mp_m_axi_split_arready = NULL;
  mp_m_axi_split_awready = NULL;
  mp_m_axi_split_bresp = NULL;
  mp_m_axi_split_bvalid = NULL;
  mp_m_axi_split_rdata = NULL;
  mp_m_axi_split_rresp = NULL;
  mp_m_axi_split_rvalid = NULL;
  mp_m_axi_split_wready = NULL;

  // Instantiate Socket Stubs

  // configure S00_AXI_transactor
    xsc::common_cpp::properties S00_AXI_transactor_param_props;
    S00_AXI_transactor_param_props.addLong("DATA_WIDTH", "32");
    S00_AXI_transactor_param_props.addLong("FREQ_HZ", "100000000");
    S00_AXI_transactor_param_props.addLong("ID_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("ADDR_WIDTH", "32");
    S00_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    S00_AXI_transactor_param_props.addLong("HAS_BURST", "0");
    S00_AXI_transactor_param_props.addLong("HAS_LOCK", "0");
    S00_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    S00_AXI_transactor_param_props.addLong("HAS_CACHE", "0");
    S00_AXI_transactor_param_props.addLong("HAS_QOS", "0");
    S00_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    S00_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    S00_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    S00_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    S00_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    S00_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    S00_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    S00_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    S00_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    S00_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    S00_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    S00_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    S00_AXI_transactor_param_props.addLong("HAS_SIZE", "0");
    S00_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    S00_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    S00_AXI_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    S00_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    S00_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_S00_AXI_transactor = new xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>("S00_AXI_transactor", S00_AXI_transactor_param_props);
  mp_S00_AXI_transactor->AWADDR(s_axi_awaddr);
  mp_S00_AXI_transactor->AWPROT(s_axi_awprot);
  mp_s_axi_awvalid_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_awvalid_converter");
  mp_s_axi_awvalid_converter->vector_in(s_axi_awvalid);
  mp_s_axi_awvalid_converter->scalar_out(m_s_axi_awvalid_converter_signal);
  mp_S00_AXI_transactor->AWVALID(m_s_axi_awvalid_converter_signal);
  mp_s_axi_awready_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_awready_converter");
  mp_s_axi_awready_converter->scalar_in(m_s_axi_awready_converter_signal);
  mp_s_axi_awready_converter->vector_out(s_axi_awready);
  mp_S00_AXI_transactor->AWREADY(m_s_axi_awready_converter_signal);
  mp_S00_AXI_transactor->WDATA(s_axi_wdata);
  mp_S00_AXI_transactor->WSTRB(s_axi_wstrb);
  mp_s_axi_wvalid_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_wvalid_converter");
  mp_s_axi_wvalid_converter->vector_in(s_axi_wvalid);
  mp_s_axi_wvalid_converter->scalar_out(m_s_axi_wvalid_converter_signal);
  mp_S00_AXI_transactor->WVALID(m_s_axi_wvalid_converter_signal);
  mp_s_axi_wready_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_wready_converter");
  mp_s_axi_wready_converter->scalar_in(m_s_axi_wready_converter_signal);
  mp_s_axi_wready_converter->vector_out(s_axi_wready);
  mp_S00_AXI_transactor->WREADY(m_s_axi_wready_converter_signal);
  mp_S00_AXI_transactor->BRESP(s_axi_bresp);
  mp_s_axi_bvalid_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_bvalid_converter");
  mp_s_axi_bvalid_converter->scalar_in(m_s_axi_bvalid_converter_signal);
  mp_s_axi_bvalid_converter->vector_out(s_axi_bvalid);
  mp_S00_AXI_transactor->BVALID(m_s_axi_bvalid_converter_signal);
  mp_s_axi_bready_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_bready_converter");
  mp_s_axi_bready_converter->vector_in(s_axi_bready);
  mp_s_axi_bready_converter->scalar_out(m_s_axi_bready_converter_signal);
  mp_S00_AXI_transactor->BREADY(m_s_axi_bready_converter_signal);
  mp_S00_AXI_transactor->ARADDR(s_axi_araddr);
  mp_S00_AXI_transactor->ARPROT(s_axi_arprot);
  mp_s_axi_arvalid_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_arvalid_converter");
  mp_s_axi_arvalid_converter->vector_in(s_axi_arvalid);
  mp_s_axi_arvalid_converter->scalar_out(m_s_axi_arvalid_converter_signal);
  mp_S00_AXI_transactor->ARVALID(m_s_axi_arvalid_converter_signal);
  mp_s_axi_arready_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_arready_converter");
  mp_s_axi_arready_converter->scalar_in(m_s_axi_arready_converter_signal);
  mp_s_axi_arready_converter->vector_out(s_axi_arready);
  mp_S00_AXI_transactor->ARREADY(m_s_axi_arready_converter_signal);
  mp_S00_AXI_transactor->RDATA(s_axi_rdata);
  mp_S00_AXI_transactor->RRESP(s_axi_rresp);
  mp_s_axi_rvalid_converter = new xsc::common::scalar2vectorN_converter<1>("s_axi_rvalid_converter");
  mp_s_axi_rvalid_converter->scalar_in(m_s_axi_rvalid_converter_signal);
  mp_s_axi_rvalid_converter->vector_out(s_axi_rvalid);
  mp_S00_AXI_transactor->RVALID(m_s_axi_rvalid_converter_signal);
  mp_s_axi_rready_converter = new xsc::common::vectorN2scalar_converter<1>("s_axi_rready_converter");
  mp_s_axi_rready_converter->vector_in(s_axi_rready);
  mp_s_axi_rready_converter->scalar_out(m_s_axi_rready_converter_signal);
  mp_S00_AXI_transactor->RREADY(m_s_axi_rready_converter_signal);
  mp_S00_AXI_transactor->CLK(aclk);
  mp_S00_AXI_transactor->RST(aresetn);
  // configure M00_AXI_transactor
    xsc::common_cpp::properties M00_AXI_transactor_param_props;
    M00_AXI_transactor_param_props.addLong("DATA_WIDTH", "32");
    M00_AXI_transactor_param_props.addLong("FREQ_HZ", "100000000");
    M00_AXI_transactor_param_props.addLong("ID_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("ADDR_WIDTH", "32");
    M00_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    M00_AXI_transactor_param_props.addLong("HAS_BURST", "0");
    M00_AXI_transactor_param_props.addLong("HAS_LOCK", "0");
    M00_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    M00_AXI_transactor_param_props.addLong("HAS_CACHE", "0");
    M00_AXI_transactor_param_props.addLong("HAS_QOS", "0");
    M00_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    M00_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    M00_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    M00_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    M00_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    M00_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    M00_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    M00_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    M00_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    M00_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    M00_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    M00_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    M00_AXI_transactor_param_props.addLong("HAS_SIZE", "0");
    M00_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    M00_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    M00_AXI_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    M00_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    M00_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_M00_AXI_transactor = new xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>("M00_AXI_transactor", M00_AXI_transactor_param_props);
  mp_m_axi_awaddr_converter_0 = new xsc::common::vector2vector_converter<32,64>("m_axi_awaddr_converter_0");
  mp_m_axi_concat_awaddr = new xsc::xsc_concatenator<64, 2>("m_axi_concat_awaddr");
  mp_m_axi_concat_awaddr->in_port[0](m_axi_concat_awaddr_out_0);
  mp_m_axi_concat_awaddr->out_port(m_axi_awaddr);
    mp_m_axi_concat_awaddr->offset_port(0, 0);
  mp_m_axi_awaddr_converter_0->vector_in(m_m_axi_awaddr_converter_0_signal);
  mp_m_axi_awaddr_converter_0->vector_out(m_axi_concat_awaddr_out_0);
  mp_M00_AXI_transactor->AWADDR(m_m_axi_awaddr_converter_0_signal);
  mp_m_axi_awprot_converter_0 = new xsc::common::vector2vector_converter<3,6>("m_axi_awprot_converter_0");
  mp_m_axi_concat_awprot = new xsc::xsc_concatenator<6, 2>("m_axi_concat_awprot");
  mp_m_axi_concat_awprot->in_port[0](m_axi_concat_awprot_out_0);
  mp_m_axi_concat_awprot->out_port(m_axi_awprot);
    mp_m_axi_concat_awprot->offset_port(0, 0);
  mp_m_axi_awprot_converter_0->vector_in(m_m_axi_awprot_converter_0_signal);
  mp_m_axi_awprot_converter_0->vector_out(m_axi_concat_awprot_out_0);
  mp_M00_AXI_transactor->AWPROT(m_m_axi_awprot_converter_0_signal);
  mp_m_axi_awvalid_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_awvalid_converter_0");
  mp_m_axi_concat_awvalid = new xsc::xsc_concatenator<2, 2>("m_axi_concat_awvalid");
  mp_m_axi_concat_awvalid->in_port[0](m_axi_concat_awvalid_out_0);
  mp_m_axi_concat_awvalid->out_port(m_axi_awvalid);
    mp_m_axi_concat_awvalid->offset_port(0, 0);
  mp_m_axi_awvalid_converter_0->scalar_in(m_m_axi_awvalid_converter_0_signal);
  mp_m_axi_awvalid_converter_0->vector_out(m_axi_concat_awvalid_out_0);
  mp_M00_AXI_transactor->AWVALID(m_m_axi_awvalid_converter_0_signal);
  mp_m_axi_awready_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_awready_converter_0");
  mp_m_axi_split_awready = new xsc::xsc_split<2, 2>("m_axi_split_awready");
  mp_m_axi_split_awready->in_port(m_axi_awready);
  mp_m_axi_split_awready->out_port[0](m_axi_split_awready_out_0);
    mp_m_axi_split_awready->add_mask(0,1,0);
  mp_m_axi_awready_converter_0->vector_in(m_axi_split_awready_out_0);
  mp_m_axi_awready_converter_0->scalar_out(m_m_axi_awready_converter_0_signal);
  mp_M00_AXI_transactor->AWREADY(m_m_axi_awready_converter_0_signal);
  mp_m_axi_wdata_converter_0 = new xsc::common::vector2vector_converter<32,64>("m_axi_wdata_converter_0");
  mp_m_axi_concat_wdata = new xsc::xsc_concatenator<64, 2>("m_axi_concat_wdata");
  mp_m_axi_concat_wdata->in_port[0](m_axi_concat_wdata_out_0);
  mp_m_axi_concat_wdata->out_port(m_axi_wdata);
    mp_m_axi_concat_wdata->offset_port(0, 0);
  mp_m_axi_wdata_converter_0->vector_in(m_m_axi_wdata_converter_0_signal);
  mp_m_axi_wdata_converter_0->vector_out(m_axi_concat_wdata_out_0);
  mp_M00_AXI_transactor->WDATA(m_m_axi_wdata_converter_0_signal);
  mp_m_axi_wstrb_converter_0 = new xsc::common::vector2vector_converter<4,8>("m_axi_wstrb_converter_0");
  mp_m_axi_concat_wstrb = new xsc::xsc_concatenator<8, 2>("m_axi_concat_wstrb");
  mp_m_axi_concat_wstrb->in_port[0](m_axi_concat_wstrb_out_0);
  mp_m_axi_concat_wstrb->out_port(m_axi_wstrb);
    mp_m_axi_concat_wstrb->offset_port(0, 0);
  mp_m_axi_wstrb_converter_0->vector_in(m_m_axi_wstrb_converter_0_signal);
  mp_m_axi_wstrb_converter_0->vector_out(m_axi_concat_wstrb_out_0);
  mp_M00_AXI_transactor->WSTRB(m_m_axi_wstrb_converter_0_signal);
  mp_m_axi_wvalid_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_wvalid_converter_0");
  mp_m_axi_concat_wvalid = new xsc::xsc_concatenator<2, 2>("m_axi_concat_wvalid");
  mp_m_axi_concat_wvalid->in_port[0](m_axi_concat_wvalid_out_0);
  mp_m_axi_concat_wvalid->out_port(m_axi_wvalid);
    mp_m_axi_concat_wvalid->offset_port(0, 0);
  mp_m_axi_wvalid_converter_0->scalar_in(m_m_axi_wvalid_converter_0_signal);
  mp_m_axi_wvalid_converter_0->vector_out(m_axi_concat_wvalid_out_0);
  mp_M00_AXI_transactor->WVALID(m_m_axi_wvalid_converter_0_signal);
  mp_m_axi_wready_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_wready_converter_0");
  mp_m_axi_split_wready = new xsc::xsc_split<2, 2>("m_axi_split_wready");
  mp_m_axi_split_wready->in_port(m_axi_wready);
  mp_m_axi_split_wready->out_port[0](m_axi_split_wready_out_0);
    mp_m_axi_split_wready->add_mask(0,1,0);
  mp_m_axi_wready_converter_0->vector_in(m_axi_split_wready_out_0);
  mp_m_axi_wready_converter_0->scalar_out(m_m_axi_wready_converter_0_signal);
  mp_M00_AXI_transactor->WREADY(m_m_axi_wready_converter_0_signal);
  mp_m_axi_bresp_converter_0 = new xsc::common::vector2vector_converter<4,2>("m_axi_bresp_converter_0");
  mp_m_axi_split_bresp = new xsc::xsc_split<4, 2>("m_axi_split_bresp");
  mp_m_axi_split_bresp->in_port(m_axi_bresp);
  mp_m_axi_split_bresp->out_port[0](m_axi_split_bresp_out_0);
    mp_m_axi_split_bresp->add_mask(0,2,0);
  mp_m_axi_bresp_converter_0->vector_in(m_axi_split_bresp_out_0);
  mp_m_axi_bresp_converter_0->vector_out(m_m_axi_bresp_converter_0_signal);
  mp_M00_AXI_transactor->BRESP(m_m_axi_bresp_converter_0_signal);
  mp_m_axi_bvalid_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_bvalid_converter_0");
  mp_m_axi_split_bvalid = new xsc::xsc_split<2, 2>("m_axi_split_bvalid");
  mp_m_axi_split_bvalid->in_port(m_axi_bvalid);
  mp_m_axi_split_bvalid->out_port[0](m_axi_split_bvalid_out_0);
    mp_m_axi_split_bvalid->add_mask(0,1,0);
  mp_m_axi_bvalid_converter_0->vector_in(m_axi_split_bvalid_out_0);
  mp_m_axi_bvalid_converter_0->scalar_out(m_m_axi_bvalid_converter_0_signal);
  mp_M00_AXI_transactor->BVALID(m_m_axi_bvalid_converter_0_signal);
  mp_m_axi_bready_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_bready_converter_0");
  mp_m_axi_concat_bready = new xsc::xsc_concatenator<2, 2>("m_axi_concat_bready");
  mp_m_axi_concat_bready->in_port[0](m_axi_concat_bready_out_0);
  mp_m_axi_concat_bready->out_port(m_axi_bready);
    mp_m_axi_concat_bready->offset_port(0, 0);
  mp_m_axi_bready_converter_0->scalar_in(m_m_axi_bready_converter_0_signal);
  mp_m_axi_bready_converter_0->vector_out(m_axi_concat_bready_out_0);
  mp_M00_AXI_transactor->BREADY(m_m_axi_bready_converter_0_signal);
  mp_m_axi_araddr_converter_0 = new xsc::common::vector2vector_converter<32,64>("m_axi_araddr_converter_0");
  mp_m_axi_concat_araddr = new xsc::xsc_concatenator<64, 2>("m_axi_concat_araddr");
  mp_m_axi_concat_araddr->in_port[0](m_axi_concat_araddr_out_0);
  mp_m_axi_concat_araddr->out_port(m_axi_araddr);
    mp_m_axi_concat_araddr->offset_port(0, 0);
  mp_m_axi_araddr_converter_0->vector_in(m_m_axi_araddr_converter_0_signal);
  mp_m_axi_araddr_converter_0->vector_out(m_axi_concat_araddr_out_0);
  mp_M00_AXI_transactor->ARADDR(m_m_axi_araddr_converter_0_signal);
  mp_m_axi_arprot_converter_0 = new xsc::common::vector2vector_converter<3,6>("m_axi_arprot_converter_0");
  mp_m_axi_concat_arprot = new xsc::xsc_concatenator<6, 2>("m_axi_concat_arprot");
  mp_m_axi_concat_arprot->in_port[0](m_axi_concat_arprot_out_0);
  mp_m_axi_concat_arprot->out_port(m_axi_arprot);
    mp_m_axi_concat_arprot->offset_port(0, 0);
  mp_m_axi_arprot_converter_0->vector_in(m_m_axi_arprot_converter_0_signal);
  mp_m_axi_arprot_converter_0->vector_out(m_axi_concat_arprot_out_0);
  mp_M00_AXI_transactor->ARPROT(m_m_axi_arprot_converter_0_signal);
  mp_m_axi_arvalid_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_arvalid_converter_0");
  mp_m_axi_concat_arvalid = new xsc::xsc_concatenator<2, 2>("m_axi_concat_arvalid");
  mp_m_axi_concat_arvalid->in_port[0](m_axi_concat_arvalid_out_0);
  mp_m_axi_concat_arvalid->out_port(m_axi_arvalid);
    mp_m_axi_concat_arvalid->offset_port(0, 0);
  mp_m_axi_arvalid_converter_0->scalar_in(m_m_axi_arvalid_converter_0_signal);
  mp_m_axi_arvalid_converter_0->vector_out(m_axi_concat_arvalid_out_0);
  mp_M00_AXI_transactor->ARVALID(m_m_axi_arvalid_converter_0_signal);
  mp_m_axi_arready_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_arready_converter_0");
  mp_m_axi_split_arready = new xsc::xsc_split<2, 2>("m_axi_split_arready");
  mp_m_axi_split_arready->in_port(m_axi_arready);
  mp_m_axi_split_arready->out_port[0](m_axi_split_arready_out_0);
    mp_m_axi_split_arready->add_mask(0,1,0);
  mp_m_axi_arready_converter_0->vector_in(m_axi_split_arready_out_0);
  mp_m_axi_arready_converter_0->scalar_out(m_m_axi_arready_converter_0_signal);
  mp_M00_AXI_transactor->ARREADY(m_m_axi_arready_converter_0_signal);
  mp_m_axi_rdata_converter_0 = new xsc::common::vector2vector_converter<64,32>("m_axi_rdata_converter_0");
  mp_m_axi_split_rdata = new xsc::xsc_split<64, 2>("m_axi_split_rdata");
  mp_m_axi_split_rdata->in_port(m_axi_rdata);
  mp_m_axi_split_rdata->out_port[0](m_axi_split_rdata_out_0);
    mp_m_axi_split_rdata->add_mask(0,32,0);
  mp_m_axi_rdata_converter_0->vector_in(m_axi_split_rdata_out_0);
  mp_m_axi_rdata_converter_0->vector_out(m_m_axi_rdata_converter_0_signal);
  mp_M00_AXI_transactor->RDATA(m_m_axi_rdata_converter_0_signal);
  mp_m_axi_rresp_converter_0 = new xsc::common::vector2vector_converter<4,2>("m_axi_rresp_converter_0");
  mp_m_axi_split_rresp = new xsc::xsc_split<4, 2>("m_axi_split_rresp");
  mp_m_axi_split_rresp->in_port(m_axi_rresp);
  mp_m_axi_split_rresp->out_port[0](m_axi_split_rresp_out_0);
    mp_m_axi_split_rresp->add_mask(0,2,0);
  mp_m_axi_rresp_converter_0->vector_in(m_axi_split_rresp_out_0);
  mp_m_axi_rresp_converter_0->vector_out(m_m_axi_rresp_converter_0_signal);
  mp_M00_AXI_transactor->RRESP(m_m_axi_rresp_converter_0_signal);
  mp_m_axi_rvalid_converter_0 = new xsc::common::vectorN2scalar_converter<2>("m_axi_rvalid_converter_0");
  mp_m_axi_split_rvalid = new xsc::xsc_split<2, 2>("m_axi_split_rvalid");
  mp_m_axi_split_rvalid->in_port(m_axi_rvalid);
  mp_m_axi_split_rvalid->out_port[0](m_axi_split_rvalid_out_0);
    mp_m_axi_split_rvalid->add_mask(0,1,0);
  mp_m_axi_rvalid_converter_0->vector_in(m_axi_split_rvalid_out_0);
  mp_m_axi_rvalid_converter_0->scalar_out(m_m_axi_rvalid_converter_0_signal);
  mp_M00_AXI_transactor->RVALID(m_m_axi_rvalid_converter_0_signal);
  mp_m_axi_rready_converter_0 = new xsc::common::scalar2vectorN_converter<2>("m_axi_rready_converter_0");
  mp_m_axi_concat_rready = new xsc::xsc_concatenator<2, 2>("m_axi_concat_rready");
  mp_m_axi_concat_rready->in_port[0](m_axi_concat_rready_out_0);
  mp_m_axi_concat_rready->out_port(m_axi_rready);
    mp_m_axi_concat_rready->offset_port(0, 0);
  mp_m_axi_rready_converter_0->scalar_in(m_m_axi_rready_converter_0_signal);
  mp_m_axi_rready_converter_0->vector_out(m_axi_concat_rready_out_0);
  mp_M00_AXI_transactor->RREADY(m_m_axi_rready_converter_0_signal);
  mp_M00_AXI_transactor->CLK(aclk);
  mp_M00_AXI_transactor->RST(aresetn);
  // configure M01_AXI_transactor
    xsc::common_cpp::properties M01_AXI_transactor_param_props;
    M01_AXI_transactor_param_props.addLong("DATA_WIDTH", "32");
    M01_AXI_transactor_param_props.addLong("FREQ_HZ", "100000000");
    M01_AXI_transactor_param_props.addLong("ID_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("ADDR_WIDTH", "32");
    M01_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    M01_AXI_transactor_param_props.addLong("HAS_BURST", "0");
    M01_AXI_transactor_param_props.addLong("HAS_LOCK", "0");
    M01_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    M01_AXI_transactor_param_props.addLong("HAS_CACHE", "0");
    M01_AXI_transactor_param_props.addLong("HAS_QOS", "0");
    M01_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    M01_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    M01_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    M01_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    M01_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    M01_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    M01_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    M01_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    M01_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    M01_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    M01_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    M01_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    M01_AXI_transactor_param_props.addLong("HAS_SIZE", "0");
    M01_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    M01_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    M01_AXI_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    M01_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    M01_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_M01_AXI_transactor = new xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>("M01_AXI_transactor", M01_AXI_transactor_param_props);
  mp_m_axi_awaddr_converter_1 = new xsc::common::vector2vector_converter<32,64>("m_axi_awaddr_converter_1");
  mp_m_axi_concat_awaddr->in_port[1](m_axi_concat_awaddr_out_1);
  mp_m_axi_concat_awaddr->offset_port(1, 32);
  mp_m_axi_awaddr_converter_1->vector_in(m_m_axi_awaddr_converter_1_signal);
  mp_m_axi_awaddr_converter_1->vector_out(m_axi_concat_awaddr_out_1);
  mp_M01_AXI_transactor->AWADDR(m_m_axi_awaddr_converter_1_signal);
  mp_m_axi_awprot_converter_1 = new xsc::common::vector2vector_converter<3,6>("m_axi_awprot_converter_1");
  mp_m_axi_concat_awprot->in_port[1](m_axi_concat_awprot_out_1);
  mp_m_axi_concat_awprot->offset_port(1, 3);
  mp_m_axi_awprot_converter_1->vector_in(m_m_axi_awprot_converter_1_signal);
  mp_m_axi_awprot_converter_1->vector_out(m_axi_concat_awprot_out_1);
  mp_M01_AXI_transactor->AWPROT(m_m_axi_awprot_converter_1_signal);
  mp_m_axi_awvalid_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_awvalid_converter_1");
  mp_m_axi_concat_awvalid->in_port[1](m_axi_concat_awvalid_out_1);
  mp_m_axi_concat_awvalid->offset_port(1, 1);
  mp_m_axi_awvalid_converter_1->scalar_in(m_m_axi_awvalid_converter_1_signal);
  mp_m_axi_awvalid_converter_1->vector_out(m_axi_concat_awvalid_out_1);
  mp_M01_AXI_transactor->AWVALID(m_m_axi_awvalid_converter_1_signal);
  mp_m_axi_awready_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_awready_converter_1");
  
  mp_m_axi_split_awready->out_port[1](m_axi_split_awready_out_1);
    mp_m_axi_split_awready->add_mask(1,2,1);
  mp_m_axi_awready_converter_1->vector_in(m_axi_split_awready_out_1);
  mp_m_axi_awready_converter_1->scalar_out(m_m_axi_awready_converter_1_signal);
  mp_M01_AXI_transactor->AWREADY(m_m_axi_awready_converter_1_signal);
  mp_m_axi_wdata_converter_1 = new xsc::common::vector2vector_converter<32,64>("m_axi_wdata_converter_1");
  mp_m_axi_concat_wdata->in_port[1](m_axi_concat_wdata_out_1);
  mp_m_axi_concat_wdata->offset_port(1, 32);
  mp_m_axi_wdata_converter_1->vector_in(m_m_axi_wdata_converter_1_signal);
  mp_m_axi_wdata_converter_1->vector_out(m_axi_concat_wdata_out_1);
  mp_M01_AXI_transactor->WDATA(m_m_axi_wdata_converter_1_signal);
  mp_m_axi_wstrb_converter_1 = new xsc::common::vector2vector_converter<4,8>("m_axi_wstrb_converter_1");
  mp_m_axi_concat_wstrb->in_port[1](m_axi_concat_wstrb_out_1);
  mp_m_axi_concat_wstrb->offset_port(1, 4);
  mp_m_axi_wstrb_converter_1->vector_in(m_m_axi_wstrb_converter_1_signal);
  mp_m_axi_wstrb_converter_1->vector_out(m_axi_concat_wstrb_out_1);
  mp_M01_AXI_transactor->WSTRB(m_m_axi_wstrb_converter_1_signal);
  mp_m_axi_wvalid_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_wvalid_converter_1");
  mp_m_axi_concat_wvalid->in_port[1](m_axi_concat_wvalid_out_1);
  mp_m_axi_concat_wvalid->offset_port(1, 1);
  mp_m_axi_wvalid_converter_1->scalar_in(m_m_axi_wvalid_converter_1_signal);
  mp_m_axi_wvalid_converter_1->vector_out(m_axi_concat_wvalid_out_1);
  mp_M01_AXI_transactor->WVALID(m_m_axi_wvalid_converter_1_signal);
  mp_m_axi_wready_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_wready_converter_1");
  
  mp_m_axi_split_wready->out_port[1](m_axi_split_wready_out_1);
    mp_m_axi_split_wready->add_mask(1,2,1);
  mp_m_axi_wready_converter_1->vector_in(m_axi_split_wready_out_1);
  mp_m_axi_wready_converter_1->scalar_out(m_m_axi_wready_converter_1_signal);
  mp_M01_AXI_transactor->WREADY(m_m_axi_wready_converter_1_signal);
  mp_m_axi_bresp_converter_1 = new xsc::common::vector2vector_converter<4,2>("m_axi_bresp_converter_1");
  
  mp_m_axi_split_bresp->out_port[1](m_axi_split_bresp_out_1);
    mp_m_axi_split_bresp->add_mask(1,4,2);
  mp_m_axi_bresp_converter_1->vector_in(m_axi_split_bresp_out_1);
  mp_m_axi_bresp_converter_1->vector_out(m_m_axi_bresp_converter_1_signal);
  mp_M01_AXI_transactor->BRESP(m_m_axi_bresp_converter_1_signal);
  mp_m_axi_bvalid_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_bvalid_converter_1");
  
  mp_m_axi_split_bvalid->out_port[1](m_axi_split_bvalid_out_1);
    mp_m_axi_split_bvalid->add_mask(1,2,1);
  mp_m_axi_bvalid_converter_1->vector_in(m_axi_split_bvalid_out_1);
  mp_m_axi_bvalid_converter_1->scalar_out(m_m_axi_bvalid_converter_1_signal);
  mp_M01_AXI_transactor->BVALID(m_m_axi_bvalid_converter_1_signal);
  mp_m_axi_bready_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_bready_converter_1");
  mp_m_axi_concat_bready->in_port[1](m_axi_concat_bready_out_1);
  mp_m_axi_concat_bready->offset_port(1, 1);
  mp_m_axi_bready_converter_1->scalar_in(m_m_axi_bready_converter_1_signal);
  mp_m_axi_bready_converter_1->vector_out(m_axi_concat_bready_out_1);
  mp_M01_AXI_transactor->BREADY(m_m_axi_bready_converter_1_signal);
  mp_m_axi_araddr_converter_1 = new xsc::common::vector2vector_converter<32,64>("m_axi_araddr_converter_1");
  mp_m_axi_concat_araddr->in_port[1](m_axi_concat_araddr_out_1);
  mp_m_axi_concat_araddr->offset_port(1, 32);
  mp_m_axi_araddr_converter_1->vector_in(m_m_axi_araddr_converter_1_signal);
  mp_m_axi_araddr_converter_1->vector_out(m_axi_concat_araddr_out_1);
  mp_M01_AXI_transactor->ARADDR(m_m_axi_araddr_converter_1_signal);
  mp_m_axi_arprot_converter_1 = new xsc::common::vector2vector_converter<3,6>("m_axi_arprot_converter_1");
  mp_m_axi_concat_arprot->in_port[1](m_axi_concat_arprot_out_1);
  mp_m_axi_concat_arprot->offset_port(1, 3);
  mp_m_axi_arprot_converter_1->vector_in(m_m_axi_arprot_converter_1_signal);
  mp_m_axi_arprot_converter_1->vector_out(m_axi_concat_arprot_out_1);
  mp_M01_AXI_transactor->ARPROT(m_m_axi_arprot_converter_1_signal);
  mp_m_axi_arvalid_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_arvalid_converter_1");
  mp_m_axi_concat_arvalid->in_port[1](m_axi_concat_arvalid_out_1);
  mp_m_axi_concat_arvalid->offset_port(1, 1);
  mp_m_axi_arvalid_converter_1->scalar_in(m_m_axi_arvalid_converter_1_signal);
  mp_m_axi_arvalid_converter_1->vector_out(m_axi_concat_arvalid_out_1);
  mp_M01_AXI_transactor->ARVALID(m_m_axi_arvalid_converter_1_signal);
  mp_m_axi_arready_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_arready_converter_1");
  
  mp_m_axi_split_arready->out_port[1](m_axi_split_arready_out_1);
    mp_m_axi_split_arready->add_mask(1,2,1);
  mp_m_axi_arready_converter_1->vector_in(m_axi_split_arready_out_1);
  mp_m_axi_arready_converter_1->scalar_out(m_m_axi_arready_converter_1_signal);
  mp_M01_AXI_transactor->ARREADY(m_m_axi_arready_converter_1_signal);
  mp_m_axi_rdata_converter_1 = new xsc::common::vector2vector_converter<64,32>("m_axi_rdata_converter_1");
  
  mp_m_axi_split_rdata->out_port[1](m_axi_split_rdata_out_1);
    mp_m_axi_split_rdata->add_mask(1,64,32);
  mp_m_axi_rdata_converter_1->vector_in(m_axi_split_rdata_out_1);
  mp_m_axi_rdata_converter_1->vector_out(m_m_axi_rdata_converter_1_signal);
  mp_M01_AXI_transactor->RDATA(m_m_axi_rdata_converter_1_signal);
  mp_m_axi_rresp_converter_1 = new xsc::common::vector2vector_converter<4,2>("m_axi_rresp_converter_1");
  
  mp_m_axi_split_rresp->out_port[1](m_axi_split_rresp_out_1);
    mp_m_axi_split_rresp->add_mask(1,4,2);
  mp_m_axi_rresp_converter_1->vector_in(m_axi_split_rresp_out_1);
  mp_m_axi_rresp_converter_1->vector_out(m_m_axi_rresp_converter_1_signal);
  mp_M01_AXI_transactor->RRESP(m_m_axi_rresp_converter_1_signal);
  mp_m_axi_rvalid_converter_1 = new xsc::common::vectorN2scalar_converter<2>("m_axi_rvalid_converter_1");
  
  mp_m_axi_split_rvalid->out_port[1](m_axi_split_rvalid_out_1);
    mp_m_axi_split_rvalid->add_mask(1,2,1);
  mp_m_axi_rvalid_converter_1->vector_in(m_axi_split_rvalid_out_1);
  mp_m_axi_rvalid_converter_1->scalar_out(m_m_axi_rvalid_converter_1_signal);
  mp_M01_AXI_transactor->RVALID(m_m_axi_rvalid_converter_1_signal);
  mp_m_axi_rready_converter_1 = new xsc::common::scalar2vectorN_converter<2>("m_axi_rready_converter_1");
  mp_m_axi_concat_rready->in_port[1](m_axi_concat_rready_out_1);
  mp_m_axi_concat_rready->offset_port(1, 1);
  mp_m_axi_rready_converter_1->scalar_in(m_m_axi_rready_converter_1_signal);
  mp_m_axi_rready_converter_1->vector_out(m_axi_concat_rready_out_1);
  mp_M01_AXI_transactor->RREADY(m_m_axi_rready_converter_1_signal);
  mp_M01_AXI_transactor->CLK(aclk);
  mp_M01_AXI_transactor->RST(aresetn);

  // initialize transactors stubs
  S00_AXI_transactor_target_wr_socket_stub = nullptr;
  S00_AXI_transactor_target_rd_socket_stub = nullptr;
  M00_AXI_transactor_initiator_wr_socket_stub = nullptr;
  M00_AXI_transactor_initiator_rd_socket_stub = nullptr;
  M01_AXI_transactor_initiator_wr_socket_stub = nullptr;
  M01_AXI_transactor_initiator_rd_socket_stub = nullptr;

}

void cl_sda_axil_xbar::before_end_of_elaboration()
{
  // configure 'S00_AXI' transactor
  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_sda_axil_xbar", "S00_AXI_TLM_MODE") != 1)
  {
    mp_impl->target_0_rd_socket->bind(*(mp_S00_AXI_transactor->rd_socket));
    mp_impl->target_0_wr_socket->bind(*(mp_S00_AXI_transactor->wr_socket));
  
  }
  else
  {
    S00_AXI_transactor_target_wr_socket_stub = new xtlm::xtlm_aximm_target_stub("wr_socket",0);
    S00_AXI_transactor_target_wr_socket_stub->bind(*(mp_S00_AXI_transactor->wr_socket));
    S00_AXI_transactor_target_rd_socket_stub = new xtlm::xtlm_aximm_target_stub("rd_socket",0);
    S00_AXI_transactor_target_rd_socket_stub->bind(*(mp_S00_AXI_transactor->rd_socket));
    mp_S00_AXI_transactor->disable_transactor();
  }

  // configure 'M00_AXI' transactor
  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_sda_axil_xbar", "M00_AXI_TLM_MODE") != 1)
  {
    mp_impl->initiator_0_rd_socket->bind(*(mp_M00_AXI_transactor->rd_socket));
    mp_impl->initiator_0_wr_socket->bind(*(mp_M00_AXI_transactor->wr_socket));
  
  }
  else
  {
    M00_AXI_transactor_initiator_wr_socket_stub = new xtlm::xtlm_aximm_initiator_stub("wr_socket",0);
    M00_AXI_transactor_initiator_wr_socket_stub->bind(*(mp_M00_AXI_transactor->wr_socket));
    M00_AXI_transactor_initiator_rd_socket_stub = new xtlm::xtlm_aximm_initiator_stub("rd_socket",0);
    M00_AXI_transactor_initiator_rd_socket_stub->bind(*(mp_M00_AXI_transactor->rd_socket));
    mp_M00_AXI_transactor->disable_transactor();
  }

  // configure 'M01_AXI' transactor
  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_sda_axil_xbar", "M01_AXI_TLM_MODE") != 1)
  {
    mp_impl->initiator_1_rd_socket->bind(*(mp_M01_AXI_transactor->rd_socket));
    mp_impl->initiator_1_wr_socket->bind(*(mp_M01_AXI_transactor->wr_socket));
  
  }
  else
  {
    M01_AXI_transactor_initiator_wr_socket_stub = new xtlm::xtlm_aximm_initiator_stub("wr_socket",0);
    M01_AXI_transactor_initiator_wr_socket_stub->bind(*(mp_M01_AXI_transactor->wr_socket));
    M01_AXI_transactor_initiator_rd_socket_stub = new xtlm::xtlm_aximm_initiator_stub("rd_socket",0);
    M01_AXI_transactor_initiator_rd_socket_stub->bind(*(mp_M01_AXI_transactor->rd_socket));
    mp_M01_AXI_transactor->disable_transactor();
  }

}

#endif // MTI_SYSTEMC




cl_sda_axil_xbar::~cl_sda_axil_xbar()
{
  delete mp_S00_AXI_transactor;
  delete mp_s_axi_awvalid_converter;
  delete mp_s_axi_awready_converter;
  delete mp_s_axi_wvalid_converter;
  delete mp_s_axi_wready_converter;
  delete mp_s_axi_bvalid_converter;
  delete mp_s_axi_bready_converter;
  delete mp_s_axi_arvalid_converter;
  delete mp_s_axi_arready_converter;
  delete mp_s_axi_rvalid_converter;
  delete mp_s_axi_rready_converter;

  delete mp_M00_AXI_transactor;
  delete mp_m_axi_awaddr_converter_0;
  delete mp_m_axi_awprot_converter_0;
  delete mp_m_axi_awvalid_converter_0;
  delete mp_m_axi_awready_converter_0;
  delete mp_m_axi_wdata_converter_0;
  delete mp_m_axi_wstrb_converter_0;
  delete mp_m_axi_wvalid_converter_0;
  delete mp_m_axi_wready_converter_0;
  delete mp_m_axi_bresp_converter_0;
  delete mp_m_axi_bvalid_converter_0;
  delete mp_m_axi_bready_converter_0;
  delete mp_m_axi_araddr_converter_0;
  delete mp_m_axi_arprot_converter_0;
  delete mp_m_axi_arvalid_converter_0;
  delete mp_m_axi_arready_converter_0;
  delete mp_m_axi_rdata_converter_0;
  delete mp_m_axi_rresp_converter_0;
  delete mp_m_axi_rvalid_converter_0;
  delete mp_m_axi_rready_converter_0;

  delete mp_M01_AXI_transactor;
  delete mp_m_axi_awaddr_converter_1;
  delete mp_m_axi_awprot_converter_1;
  delete mp_m_axi_awvalid_converter_1;
  delete mp_m_axi_awready_converter_1;
  delete mp_m_axi_wdata_converter_1;
  delete mp_m_axi_wstrb_converter_1;
  delete mp_m_axi_wvalid_converter_1;
  delete mp_m_axi_wready_converter_1;
  delete mp_m_axi_bresp_converter_1;
  delete mp_m_axi_bvalid_converter_1;
  delete mp_m_axi_bready_converter_1;
  delete mp_m_axi_araddr_converter_1;
  delete mp_m_axi_arprot_converter_1;
  delete mp_m_axi_arvalid_converter_1;
  delete mp_m_axi_arready_converter_1;
  delete mp_m_axi_rdata_converter_1;
  delete mp_m_axi_rresp_converter_1;
  delete mp_m_axi_rvalid_converter_1;
  delete mp_m_axi_rready_converter_1;

  delete mp_m_axi_concat_araddr;
  delete mp_m_axi_concat_arprot;
  delete mp_m_axi_concat_arvalid;
  delete mp_m_axi_concat_awaddr;
  delete mp_m_axi_concat_awprot;
  delete mp_m_axi_concat_awvalid;
  delete mp_m_axi_concat_bready;
  delete mp_m_axi_concat_rready;
  delete mp_m_axi_concat_wdata;
  delete mp_m_axi_concat_wstrb;
  delete mp_m_axi_concat_wvalid;
  delete mp_m_axi_split_arready;
  delete mp_m_axi_split_awready;
  delete mp_m_axi_split_bresp;
  delete mp_m_axi_split_bvalid;
  delete mp_m_axi_split_rdata;
  delete mp_m_axi_split_rresp;
  delete mp_m_axi_split_rvalid;
  delete mp_m_axi_split_wready;
}

#ifdef MTI_SYSTEMC
SC_MODULE_EXPORT(cl_sda_axil_xbar);
#endif

#ifdef XM_SYSTEMC
XMSC_MODULE_EXPORT(cl_sda_axil_xbar);
#endif

#ifdef RIVIERA
SC_MODULE_EXPORT(cl_sda_axil_xbar);
SC_REGISTER_BV(64);
#endif

