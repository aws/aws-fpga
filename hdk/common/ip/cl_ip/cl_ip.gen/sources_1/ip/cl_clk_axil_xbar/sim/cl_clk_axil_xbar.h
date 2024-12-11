#ifndef IP_CL_CLK_AXIL_XBAR_H_
#define IP_CL_CLK_AXIL_XBAR_H_

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


#ifndef XTLM
#include "xtlm.h"
#endif
#ifndef SYSTEMC_INCLUDED
#include <systemc>
#endif

#if defined(_MSC_VER)
#define DllExport __declspec(dllexport)
#elif defined(__GNUC__)
#define DllExport __attribute__ ((visibility("default")))
#else
#define DllExport
#endif

#include "cl_clk_axil_xbar_sc.h"




#ifdef XILINX_SIMULATOR
class DllExport cl_clk_axil_xbar : public cl_clk_axil_xbar_sc
{
public:

  cl_clk_axil_xbar(const sc_core::sc_module_name& nm);
  virtual ~cl_clk_axil_xbar();

  // module pin-to-pin RTL interface

  sc_core::sc_in< bool > aclk;
  sc_core::sc_in< bool > aresetn;
  sc_core::sc_in< sc_dt::sc_bv<32> > s_axi_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<3> > s_axi_awprot;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_awvalid;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_awready;
  sc_core::sc_in< sc_dt::sc_bv<32> > s_axi_wdata;
  sc_core::sc_in< sc_dt::sc_bv<4> > s_axi_wstrb;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_wvalid;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_wready;
  sc_core::sc_out< sc_dt::sc_bv<2> > s_axi_bresp;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_bvalid;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_bready;
  sc_core::sc_in< sc_dt::sc_bv<32> > s_axi_araddr;
  sc_core::sc_in< sc_dt::sc_bv<3> > s_axi_arprot;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_arvalid;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_arready;
  sc_core::sc_out< sc_dt::sc_bv<32> > s_axi_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > s_axi_rresp;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_rvalid;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_rready;
  sc_core::sc_out< sc_dt::sc_bv<160> > m_axi_awaddr;
  sc_core::sc_out< sc_dt::sc_bv<15> > m_axi_awprot;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_awvalid;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_awready;
  sc_core::sc_out< sc_dt::sc_bv<160> > m_axi_wdata;
  sc_core::sc_out< sc_dt::sc_bv<20> > m_axi_wstrb;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_wvalid;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_wready;
  sc_core::sc_in< sc_dt::sc_bv<10> > m_axi_bresp;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_bvalid;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_bready;
  sc_core::sc_out< sc_dt::sc_bv<160> > m_axi_araddr;
  sc_core::sc_out< sc_dt::sc_bv<15> > m_axi_arprot;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_arvalid;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_arready;
  sc_core::sc_in< sc_dt::sc_bv<160> > m_axi_rdata;
  sc_core::sc_in< sc_dt::sc_bv<10> > m_axi_rresp;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_rvalid;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_rready;

  // Dummy Signals for IP Ports


protected:

  virtual void before_end_of_elaboration();

private:

  xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>* mp_S00_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_awvalid_converter;
  sc_signal< bool > m_s_axi_awvalid_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_awready_converter;
  sc_signal< bool > m_s_axi_awready_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_wvalid_converter;
  sc_signal< bool > m_s_axi_wvalid_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_wready_converter;
  sc_signal< bool > m_s_axi_wready_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_bvalid_converter;
  sc_signal< bool > m_s_axi_bvalid_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_bready_converter;
  sc_signal< bool > m_s_axi_bready_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_arvalid_converter;
  sc_signal< bool > m_s_axi_arvalid_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_arready_converter;
  sc_signal< bool > m_s_axi_arready_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_rvalid_converter;
  sc_signal< bool > m_s_axi_rvalid_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_rready_converter;
  sc_signal< bool > m_s_axi_rready_converter_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M00_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_0_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_0;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_0;
  sc_signal< bool > m_m_axi_awvalid_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_0;
  sc_signal< bool > m_m_axi_awready_converter_0_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_0_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_0;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_0;
  sc_signal< bool > m_m_axi_wvalid_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_0;
  sc_signal< bool > m_m_axi_wready_converter_0_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_0;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_0;
  sc_signal< bool > m_m_axi_bvalid_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_0;
  sc_signal< bool > m_m_axi_bready_converter_0_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_0_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_0;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_0;
  sc_signal< bool > m_m_axi_arvalid_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_0;
  sc_signal< bool > m_m_axi_arready_converter_0_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_0_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_0;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_0;
  sc_signal< bool > m_m_axi_rvalid_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_0;
  sc_signal< bool > m_m_axi_rready_converter_0_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M01_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_1_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_1;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_1;
  sc_signal< bool > m_m_axi_awvalid_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_1;
  sc_signal< bool > m_m_axi_awready_converter_1_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_1_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_1;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_1;
  sc_signal< bool > m_m_axi_wvalid_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_1;
  sc_signal< bool > m_m_axi_wready_converter_1_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_1;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_1;
  sc_signal< bool > m_m_axi_bvalid_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_1;
  sc_signal< bool > m_m_axi_bready_converter_1_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_1_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_1;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_1;
  sc_signal< bool > m_m_axi_arvalid_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_1;
  sc_signal< bool > m_m_axi_arready_converter_1_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_1_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_1;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_1;
  sc_signal< bool > m_m_axi_rvalid_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_1;
  sc_signal< bool > m_m_axi_rready_converter_1_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M02_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_2_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_2;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_2;
  sc_signal< bool > m_m_axi_awvalid_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_2;
  sc_signal< bool > m_m_axi_awready_converter_2_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_2_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_2;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_2;
  sc_signal< bool > m_m_axi_wvalid_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_2;
  sc_signal< bool > m_m_axi_wready_converter_2_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_2;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_2;
  sc_signal< bool > m_m_axi_bvalid_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_2;
  sc_signal< bool > m_m_axi_bready_converter_2_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_2_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_2;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_2;
  sc_signal< bool > m_m_axi_arvalid_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_2;
  sc_signal< bool > m_m_axi_arready_converter_2_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_2_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_2;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_2;
  sc_signal< bool > m_m_axi_rvalid_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_2;
  sc_signal< bool > m_m_axi_rready_converter_2_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M03_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_3_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_3;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_3;
  sc_signal< bool > m_m_axi_awvalid_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_3;
  sc_signal< bool > m_m_axi_awready_converter_3_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_3_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_3;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_3;
  sc_signal< bool > m_m_axi_wvalid_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_3;
  sc_signal< bool > m_m_axi_wready_converter_3_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_3;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_3;
  sc_signal< bool > m_m_axi_bvalid_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_3;
  sc_signal< bool > m_m_axi_bready_converter_3_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_3_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_3;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_3;
  sc_signal< bool > m_m_axi_arvalid_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_3;
  sc_signal< bool > m_m_axi_arready_converter_3_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_3_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_3;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_3;
  sc_signal< bool > m_m_axi_rvalid_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_3;
  sc_signal< bool > m_m_axi_rready_converter_3_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M04_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_4_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_4;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_4;
  sc_signal< bool > m_m_axi_awvalid_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_4;
  sc_signal< bool > m_m_axi_awready_converter_4_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_4_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_4;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_4;
  sc_signal< bool > m_m_axi_wvalid_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_4;
  sc_signal< bool > m_m_axi_wready_converter_4_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_4;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_4;
  sc_signal< bool > m_m_axi_bvalid_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_4;
  sc_signal< bool > m_m_axi_bready_converter_4_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_4_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_4;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_4;
  sc_signal< bool > m_m_axi_arvalid_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_4;
  sc_signal< bool > m_m_axi_arready_converter_4_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_4_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_4;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_4;
  sc_signal< bool > m_m_axi_rvalid_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_4;
  sc_signal< bool > m_m_axi_rready_converter_4_signal;

  xsc::xsc_concatenator<160, 5> * mp_m_axi_concat_araddr;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_4;






  xsc::xsc_concatenator<15, 5> * mp_m_axi_concat_arprot;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_0;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_1;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_2;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_3;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_arready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_4;




  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_arvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_4;

  xsc::xsc_concatenator<160, 5> * mp_m_axi_concat_awaddr;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_4;






  xsc::xsc_concatenator<15, 5> * mp_m_axi_concat_awprot;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_0;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_1;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_2;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_3;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_awready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_4;




  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_awvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_4;


  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_bready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_4;

  xsc::xsc_split<10, 5> * mp_m_axi_split_bresp;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_0;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_1;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_2;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_3;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_bvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_4;

  xsc::xsc_split<160, 5> * mp_m_axi_split_rdata;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_4;



  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_rready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_4;

  xsc::xsc_split<10, 5> * mp_m_axi_split_rresp;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_0;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_1;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_2;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_3;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_rvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_4;

  xsc::xsc_concatenator<160, 5> * mp_m_axi_concat_wdata;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_4;



  xsc::xsc_split<5, 5> * mp_m_axi_split_wready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_4;

  xsc::xsc_concatenator<20, 5> * mp_m_axi_concat_wstrb;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_0;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_1;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_2;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_3;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_4;


  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_wvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_4;

};
#endif // XILINX_SIMULATOR




#ifdef XM_SYSTEMC
class DllExport cl_clk_axil_xbar : public cl_clk_axil_xbar_sc
{
public:

  cl_clk_axil_xbar(const sc_core::sc_module_name& nm);
  virtual ~cl_clk_axil_xbar();

  // module pin-to-pin RTL interface

  sc_core::sc_in< bool > aclk;
  sc_core::sc_in< bool > aresetn;
  sc_core::sc_in< sc_dt::sc_bv<32> > s_axi_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<3> > s_axi_awprot;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_awvalid;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_awready;
  sc_core::sc_in< sc_dt::sc_bv<32> > s_axi_wdata;
  sc_core::sc_in< sc_dt::sc_bv<4> > s_axi_wstrb;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_wvalid;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_wready;
  sc_core::sc_out< sc_dt::sc_bv<2> > s_axi_bresp;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_bvalid;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_bready;
  sc_core::sc_in< sc_dt::sc_bv<32> > s_axi_araddr;
  sc_core::sc_in< sc_dt::sc_bv<3> > s_axi_arprot;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_arvalid;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_arready;
  sc_core::sc_out< sc_dt::sc_bv<32> > s_axi_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > s_axi_rresp;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_rvalid;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_rready;
  sc_core::sc_out< sc_dt::sc_bv<160> > m_axi_awaddr;
  sc_core::sc_out< sc_dt::sc_bv<15> > m_axi_awprot;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_awvalid;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_awready;
  sc_core::sc_out< sc_dt::sc_bv<160> > m_axi_wdata;
  sc_core::sc_out< sc_dt::sc_bv<20> > m_axi_wstrb;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_wvalid;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_wready;
  sc_core::sc_in< sc_dt::sc_bv<10> > m_axi_bresp;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_bvalid;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_bready;
  sc_core::sc_out< sc_dt::sc_bv<160> > m_axi_araddr;
  sc_core::sc_out< sc_dt::sc_bv<15> > m_axi_arprot;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_arvalid;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_arready;
  sc_core::sc_in< sc_dt::sc_bv<160> > m_axi_rdata;
  sc_core::sc_in< sc_dt::sc_bv<10> > m_axi_rresp;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_rvalid;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_rready;

  // Dummy Signals for IP Ports


protected:

  virtual void before_end_of_elaboration();

private:

  xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>* mp_S00_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_awvalid_converter;
  sc_signal< bool > m_s_axi_awvalid_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_awready_converter;
  sc_signal< bool > m_s_axi_awready_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_wvalid_converter;
  sc_signal< bool > m_s_axi_wvalid_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_wready_converter;
  sc_signal< bool > m_s_axi_wready_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_bvalid_converter;
  sc_signal< bool > m_s_axi_bvalid_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_bready_converter;
  sc_signal< bool > m_s_axi_bready_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_arvalid_converter;
  sc_signal< bool > m_s_axi_arvalid_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_arready_converter;
  sc_signal< bool > m_s_axi_arready_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_rvalid_converter;
  sc_signal< bool > m_s_axi_rvalid_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_rready_converter;
  sc_signal< bool > m_s_axi_rready_converter_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M00_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_0_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_0;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_0;
  sc_signal< bool > m_m_axi_awvalid_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_0;
  sc_signal< bool > m_m_axi_awready_converter_0_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_0_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_0;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_0;
  sc_signal< bool > m_m_axi_wvalid_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_0;
  sc_signal< bool > m_m_axi_wready_converter_0_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_0;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_0;
  sc_signal< bool > m_m_axi_bvalid_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_0;
  sc_signal< bool > m_m_axi_bready_converter_0_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_0_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_0;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_0;
  sc_signal< bool > m_m_axi_arvalid_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_0;
  sc_signal< bool > m_m_axi_arready_converter_0_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_0_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_0;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_0;
  sc_signal< bool > m_m_axi_rvalid_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_0;
  sc_signal< bool > m_m_axi_rready_converter_0_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M01_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_1_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_1;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_1;
  sc_signal< bool > m_m_axi_awvalid_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_1;
  sc_signal< bool > m_m_axi_awready_converter_1_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_1_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_1;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_1;
  sc_signal< bool > m_m_axi_wvalid_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_1;
  sc_signal< bool > m_m_axi_wready_converter_1_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_1;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_1;
  sc_signal< bool > m_m_axi_bvalid_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_1;
  sc_signal< bool > m_m_axi_bready_converter_1_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_1_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_1;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_1;
  sc_signal< bool > m_m_axi_arvalid_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_1;
  sc_signal< bool > m_m_axi_arready_converter_1_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_1_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_1;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_1;
  sc_signal< bool > m_m_axi_rvalid_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_1;
  sc_signal< bool > m_m_axi_rready_converter_1_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M02_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_2_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_2;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_2;
  sc_signal< bool > m_m_axi_awvalid_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_2;
  sc_signal< bool > m_m_axi_awready_converter_2_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_2_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_2;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_2;
  sc_signal< bool > m_m_axi_wvalid_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_2;
  sc_signal< bool > m_m_axi_wready_converter_2_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_2;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_2;
  sc_signal< bool > m_m_axi_bvalid_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_2;
  sc_signal< bool > m_m_axi_bready_converter_2_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_2_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_2;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_2;
  sc_signal< bool > m_m_axi_arvalid_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_2;
  sc_signal< bool > m_m_axi_arready_converter_2_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_2_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_2;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_2;
  sc_signal< bool > m_m_axi_rvalid_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_2;
  sc_signal< bool > m_m_axi_rready_converter_2_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M03_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_3_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_3;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_3;
  sc_signal< bool > m_m_axi_awvalid_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_3;
  sc_signal< bool > m_m_axi_awready_converter_3_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_3_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_3;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_3;
  sc_signal< bool > m_m_axi_wvalid_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_3;
  sc_signal< bool > m_m_axi_wready_converter_3_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_3;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_3;
  sc_signal< bool > m_m_axi_bvalid_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_3;
  sc_signal< bool > m_m_axi_bready_converter_3_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_3_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_3;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_3;
  sc_signal< bool > m_m_axi_arvalid_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_3;
  sc_signal< bool > m_m_axi_arready_converter_3_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_3_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_3;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_3;
  sc_signal< bool > m_m_axi_rvalid_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_3;
  sc_signal< bool > m_m_axi_rready_converter_3_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M04_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_4_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_4;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_4;
  sc_signal< bool > m_m_axi_awvalid_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_4;
  sc_signal< bool > m_m_axi_awready_converter_4_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_4_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_4;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_4;
  sc_signal< bool > m_m_axi_wvalid_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_4;
  sc_signal< bool > m_m_axi_wready_converter_4_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_4;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_4;
  sc_signal< bool > m_m_axi_bvalid_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_4;
  sc_signal< bool > m_m_axi_bready_converter_4_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_4_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_4;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_4;
  sc_signal< bool > m_m_axi_arvalid_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_4;
  sc_signal< bool > m_m_axi_arready_converter_4_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_4_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_4;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_4;
  sc_signal< bool > m_m_axi_rvalid_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_4;
  sc_signal< bool > m_m_axi_rready_converter_4_signal;

  xsc::xsc_concatenator<160, 5> * mp_m_axi_concat_araddr;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_4;






  xsc::xsc_concatenator<15, 5> * mp_m_axi_concat_arprot;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_0;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_1;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_2;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_3;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_arready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_4;




  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_arvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_4;

  xsc::xsc_concatenator<160, 5> * mp_m_axi_concat_awaddr;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_4;






  xsc::xsc_concatenator<15, 5> * mp_m_axi_concat_awprot;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_0;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_1;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_2;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_3;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_awready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_4;




  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_awvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_4;


  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_bready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_4;

  xsc::xsc_split<10, 5> * mp_m_axi_split_bresp;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_0;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_1;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_2;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_3;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_bvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_4;

  xsc::xsc_split<160, 5> * mp_m_axi_split_rdata;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_4;



  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_rready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_4;

  xsc::xsc_split<10, 5> * mp_m_axi_split_rresp;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_0;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_1;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_2;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_3;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_rvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_4;

  xsc::xsc_concatenator<160, 5> * mp_m_axi_concat_wdata;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_4;



  xsc::xsc_split<5, 5> * mp_m_axi_split_wready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_4;

  xsc::xsc_concatenator<20, 5> * mp_m_axi_concat_wstrb;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_0;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_1;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_2;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_3;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_4;


  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_wvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_4;

};
#endif // XM_SYSTEMC




#ifdef RIVIERA
class DllExport cl_clk_axil_xbar : public cl_clk_axil_xbar_sc
{
public:

  cl_clk_axil_xbar(const sc_core::sc_module_name& nm);
  virtual ~cl_clk_axil_xbar();

  // module pin-to-pin RTL interface

  sc_core::sc_in< bool > aclk;
  sc_core::sc_in< bool > aresetn;
  sc_core::sc_in< sc_dt::sc_bv<32> > s_axi_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<3> > s_axi_awprot;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_awvalid;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_awready;
  sc_core::sc_in< sc_dt::sc_bv<32> > s_axi_wdata;
  sc_core::sc_in< sc_dt::sc_bv<4> > s_axi_wstrb;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_wvalid;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_wready;
  sc_core::sc_out< sc_dt::sc_bv<2> > s_axi_bresp;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_bvalid;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_bready;
  sc_core::sc_in< sc_dt::sc_bv<32> > s_axi_araddr;
  sc_core::sc_in< sc_dt::sc_bv<3> > s_axi_arprot;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_arvalid;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_arready;
  sc_core::sc_out< sc_dt::sc_bv<32> > s_axi_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > s_axi_rresp;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_rvalid;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_rready;
  sc_core::sc_out< sc_dt::sc_bv<160> > m_axi_awaddr;
  sc_core::sc_out< sc_dt::sc_bv<15> > m_axi_awprot;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_awvalid;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_awready;
  sc_core::sc_out< sc_dt::sc_bv<160> > m_axi_wdata;
  sc_core::sc_out< sc_dt::sc_bv<20> > m_axi_wstrb;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_wvalid;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_wready;
  sc_core::sc_in< sc_dt::sc_bv<10> > m_axi_bresp;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_bvalid;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_bready;
  sc_core::sc_out< sc_dt::sc_bv<160> > m_axi_araddr;
  sc_core::sc_out< sc_dt::sc_bv<15> > m_axi_arprot;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_arvalid;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_arready;
  sc_core::sc_in< sc_dt::sc_bv<160> > m_axi_rdata;
  sc_core::sc_in< sc_dt::sc_bv<10> > m_axi_rresp;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_rvalid;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_rready;

  // Dummy Signals for IP Ports


protected:

  virtual void before_end_of_elaboration();

private:

  xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>* mp_S00_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_awvalid_converter;
  sc_signal< bool > m_s_axi_awvalid_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_awready_converter;
  sc_signal< bool > m_s_axi_awready_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_wvalid_converter;
  sc_signal< bool > m_s_axi_wvalid_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_wready_converter;
  sc_signal< bool > m_s_axi_wready_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_bvalid_converter;
  sc_signal< bool > m_s_axi_bvalid_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_bready_converter;
  sc_signal< bool > m_s_axi_bready_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_arvalid_converter;
  sc_signal< bool > m_s_axi_arvalid_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_arready_converter;
  sc_signal< bool > m_s_axi_arready_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_rvalid_converter;
  sc_signal< bool > m_s_axi_rvalid_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_rready_converter;
  sc_signal< bool > m_s_axi_rready_converter_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M00_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_0_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_0;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_0;
  sc_signal< bool > m_m_axi_awvalid_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_0;
  sc_signal< bool > m_m_axi_awready_converter_0_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_0_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_0;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_0;
  sc_signal< bool > m_m_axi_wvalid_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_0;
  sc_signal< bool > m_m_axi_wready_converter_0_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_0;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_0;
  sc_signal< bool > m_m_axi_bvalid_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_0;
  sc_signal< bool > m_m_axi_bready_converter_0_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_0_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_0;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_0;
  sc_signal< bool > m_m_axi_arvalid_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_0;
  sc_signal< bool > m_m_axi_arready_converter_0_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_0_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_0;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_0;
  sc_signal< bool > m_m_axi_rvalid_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_0;
  sc_signal< bool > m_m_axi_rready_converter_0_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M01_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_1_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_1;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_1;
  sc_signal< bool > m_m_axi_awvalid_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_1;
  sc_signal< bool > m_m_axi_awready_converter_1_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_1_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_1;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_1;
  sc_signal< bool > m_m_axi_wvalid_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_1;
  sc_signal< bool > m_m_axi_wready_converter_1_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_1;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_1;
  sc_signal< bool > m_m_axi_bvalid_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_1;
  sc_signal< bool > m_m_axi_bready_converter_1_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_1_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_1;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_1;
  sc_signal< bool > m_m_axi_arvalid_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_1;
  sc_signal< bool > m_m_axi_arready_converter_1_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_1_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_1;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_1;
  sc_signal< bool > m_m_axi_rvalid_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_1;
  sc_signal< bool > m_m_axi_rready_converter_1_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M02_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_2_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_2;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_2;
  sc_signal< bool > m_m_axi_awvalid_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_2;
  sc_signal< bool > m_m_axi_awready_converter_2_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_2_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_2;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_2;
  sc_signal< bool > m_m_axi_wvalid_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_2;
  sc_signal< bool > m_m_axi_wready_converter_2_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_2;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_2;
  sc_signal< bool > m_m_axi_bvalid_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_2;
  sc_signal< bool > m_m_axi_bready_converter_2_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_2_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_2;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_2;
  sc_signal< bool > m_m_axi_arvalid_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_2;
  sc_signal< bool > m_m_axi_arready_converter_2_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_2_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_2;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_2;
  sc_signal< bool > m_m_axi_rvalid_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_2;
  sc_signal< bool > m_m_axi_rready_converter_2_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M03_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_3_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_3;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_3;
  sc_signal< bool > m_m_axi_awvalid_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_3;
  sc_signal< bool > m_m_axi_awready_converter_3_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_3_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_3;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_3;
  sc_signal< bool > m_m_axi_wvalid_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_3;
  sc_signal< bool > m_m_axi_wready_converter_3_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_3;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_3;
  sc_signal< bool > m_m_axi_bvalid_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_3;
  sc_signal< bool > m_m_axi_bready_converter_3_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_3_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_3;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_3;
  sc_signal< bool > m_m_axi_arvalid_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_3;
  sc_signal< bool > m_m_axi_arready_converter_3_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_3_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_3;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_3;
  sc_signal< bool > m_m_axi_rvalid_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_3;
  sc_signal< bool > m_m_axi_rready_converter_3_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M04_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_4_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_4;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_4;
  sc_signal< bool > m_m_axi_awvalid_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_4;
  sc_signal< bool > m_m_axi_awready_converter_4_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_4_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_4;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_4;
  sc_signal< bool > m_m_axi_wvalid_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_4;
  sc_signal< bool > m_m_axi_wready_converter_4_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_4;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_4;
  sc_signal< bool > m_m_axi_bvalid_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_4;
  sc_signal< bool > m_m_axi_bready_converter_4_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_4_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_4;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_4;
  sc_signal< bool > m_m_axi_arvalid_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_4;
  sc_signal< bool > m_m_axi_arready_converter_4_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_4_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_4;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_4;
  sc_signal< bool > m_m_axi_rvalid_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_4;
  sc_signal< bool > m_m_axi_rready_converter_4_signal;

  xsc::xsc_concatenator<160, 5> * mp_m_axi_concat_araddr;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_4;






  xsc::xsc_concatenator<15, 5> * mp_m_axi_concat_arprot;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_0;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_1;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_2;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_3;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_arready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_4;




  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_arvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_4;

  xsc::xsc_concatenator<160, 5> * mp_m_axi_concat_awaddr;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_4;






  xsc::xsc_concatenator<15, 5> * mp_m_axi_concat_awprot;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_0;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_1;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_2;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_3;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_awready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_4;




  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_awvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_4;


  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_bready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_4;

  xsc::xsc_split<10, 5> * mp_m_axi_split_bresp;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_0;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_1;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_2;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_3;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_bvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_4;

  xsc::xsc_split<160, 5> * mp_m_axi_split_rdata;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_4;



  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_rready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_4;

  xsc::xsc_split<10, 5> * mp_m_axi_split_rresp;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_0;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_1;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_2;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_3;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_rvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_4;

  xsc::xsc_concatenator<160, 5> * mp_m_axi_concat_wdata;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_4;



  xsc::xsc_split<5, 5> * mp_m_axi_split_wready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_4;

  xsc::xsc_concatenator<20, 5> * mp_m_axi_concat_wstrb;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_0;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_1;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_2;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_3;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_4;


  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_wvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_4;

};
#endif // RIVIERA




#ifdef VCSSYSTEMC
#include "utils/xtlm_aximm_initiator_stub.h"

#include "utils/xtlm_aximm_target_stub.h"

class DllExport cl_clk_axil_xbar : public cl_clk_axil_xbar_sc
{
public:

  cl_clk_axil_xbar(const sc_core::sc_module_name& nm);
  virtual ~cl_clk_axil_xbar();

  // module pin-to-pin RTL interface

  sc_core::sc_in< bool > aclk;
  sc_core::sc_in< bool > aresetn;
  sc_core::sc_in< sc_dt::sc_bv<32> > s_axi_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<3> > s_axi_awprot;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_awvalid;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_awready;
  sc_core::sc_in< sc_dt::sc_bv<32> > s_axi_wdata;
  sc_core::sc_in< sc_dt::sc_bv<4> > s_axi_wstrb;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_wvalid;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_wready;
  sc_core::sc_out< sc_dt::sc_bv<2> > s_axi_bresp;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_bvalid;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_bready;
  sc_core::sc_in< sc_dt::sc_bv<32> > s_axi_araddr;
  sc_core::sc_in< sc_dt::sc_bv<3> > s_axi_arprot;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_arvalid;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_arready;
  sc_core::sc_out< sc_dt::sc_bv<32> > s_axi_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > s_axi_rresp;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_rvalid;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_rready;
  sc_core::sc_out< sc_dt::sc_bv<160> > m_axi_awaddr;
  sc_core::sc_out< sc_dt::sc_bv<15> > m_axi_awprot;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_awvalid;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_awready;
  sc_core::sc_out< sc_dt::sc_bv<160> > m_axi_wdata;
  sc_core::sc_out< sc_dt::sc_bv<20> > m_axi_wstrb;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_wvalid;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_wready;
  sc_core::sc_in< sc_dt::sc_bv<10> > m_axi_bresp;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_bvalid;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_bready;
  sc_core::sc_out< sc_dt::sc_bv<160> > m_axi_araddr;
  sc_core::sc_out< sc_dt::sc_bv<15> > m_axi_arprot;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_arvalid;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_arready;
  sc_core::sc_in< sc_dt::sc_bv<160> > m_axi_rdata;
  sc_core::sc_in< sc_dt::sc_bv<10> > m_axi_rresp;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_rvalid;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_rready;

  // Dummy Signals for IP Ports


protected:

  virtual void before_end_of_elaboration();

private:

  xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>* mp_S00_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_awvalid_converter;
  sc_signal< bool > m_s_axi_awvalid_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_awready_converter;
  sc_signal< bool > m_s_axi_awready_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_wvalid_converter;
  sc_signal< bool > m_s_axi_wvalid_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_wready_converter;
  sc_signal< bool > m_s_axi_wready_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_bvalid_converter;
  sc_signal< bool > m_s_axi_bvalid_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_bready_converter;
  sc_signal< bool > m_s_axi_bready_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_arvalid_converter;
  sc_signal< bool > m_s_axi_arvalid_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_arready_converter;
  sc_signal< bool > m_s_axi_arready_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_rvalid_converter;
  sc_signal< bool > m_s_axi_rvalid_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_rready_converter;
  sc_signal< bool > m_s_axi_rready_converter_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M00_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_0_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_0;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_0;
  sc_signal< bool > m_m_axi_awvalid_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_0;
  sc_signal< bool > m_m_axi_awready_converter_0_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_0_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_0;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_0;
  sc_signal< bool > m_m_axi_wvalid_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_0;
  sc_signal< bool > m_m_axi_wready_converter_0_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_0;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_0;
  sc_signal< bool > m_m_axi_bvalid_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_0;
  sc_signal< bool > m_m_axi_bready_converter_0_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_0_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_0;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_0;
  sc_signal< bool > m_m_axi_arvalid_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_0;
  sc_signal< bool > m_m_axi_arready_converter_0_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_0_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_0;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_0;
  sc_signal< bool > m_m_axi_rvalid_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_0;
  sc_signal< bool > m_m_axi_rready_converter_0_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M01_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_1_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_1;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_1;
  sc_signal< bool > m_m_axi_awvalid_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_1;
  sc_signal< bool > m_m_axi_awready_converter_1_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_1_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_1;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_1;
  sc_signal< bool > m_m_axi_wvalid_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_1;
  sc_signal< bool > m_m_axi_wready_converter_1_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_1;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_1;
  sc_signal< bool > m_m_axi_bvalid_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_1;
  sc_signal< bool > m_m_axi_bready_converter_1_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_1_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_1;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_1;
  sc_signal< bool > m_m_axi_arvalid_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_1;
  sc_signal< bool > m_m_axi_arready_converter_1_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_1_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_1;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_1;
  sc_signal< bool > m_m_axi_rvalid_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_1;
  sc_signal< bool > m_m_axi_rready_converter_1_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M02_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_2_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_2;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_2;
  sc_signal< bool > m_m_axi_awvalid_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_2;
  sc_signal< bool > m_m_axi_awready_converter_2_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_2_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_2;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_2;
  sc_signal< bool > m_m_axi_wvalid_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_2;
  sc_signal< bool > m_m_axi_wready_converter_2_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_2;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_2;
  sc_signal< bool > m_m_axi_bvalid_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_2;
  sc_signal< bool > m_m_axi_bready_converter_2_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_2_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_2;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_2;
  sc_signal< bool > m_m_axi_arvalid_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_2;
  sc_signal< bool > m_m_axi_arready_converter_2_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_2_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_2;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_2;
  sc_signal< bool > m_m_axi_rvalid_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_2;
  sc_signal< bool > m_m_axi_rready_converter_2_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M03_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_3_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_3;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_3;
  sc_signal< bool > m_m_axi_awvalid_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_3;
  sc_signal< bool > m_m_axi_awready_converter_3_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_3_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_3;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_3;
  sc_signal< bool > m_m_axi_wvalid_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_3;
  sc_signal< bool > m_m_axi_wready_converter_3_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_3;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_3;
  sc_signal< bool > m_m_axi_bvalid_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_3;
  sc_signal< bool > m_m_axi_bready_converter_3_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_3_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_3;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_3;
  sc_signal< bool > m_m_axi_arvalid_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_3;
  sc_signal< bool > m_m_axi_arready_converter_3_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_3_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_3;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_3;
  sc_signal< bool > m_m_axi_rvalid_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_3;
  sc_signal< bool > m_m_axi_rready_converter_3_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M04_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_4_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_4;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_4;
  sc_signal< bool > m_m_axi_awvalid_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_4;
  sc_signal< bool > m_m_axi_awready_converter_4_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_4_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_4;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_4;
  sc_signal< bool > m_m_axi_wvalid_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_4;
  sc_signal< bool > m_m_axi_wready_converter_4_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_4;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_4;
  sc_signal< bool > m_m_axi_bvalid_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_4;
  sc_signal< bool > m_m_axi_bready_converter_4_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_4_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_4;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_4;
  sc_signal< bool > m_m_axi_arvalid_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_4;
  sc_signal< bool > m_m_axi_arready_converter_4_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_4_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_4;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_4;
  sc_signal< bool > m_m_axi_rvalid_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_4;
  sc_signal< bool > m_m_axi_rready_converter_4_signal;

  xsc::xsc_concatenator<160, 5> * mp_m_axi_concat_araddr;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_4;






  xsc::xsc_concatenator<15, 5> * mp_m_axi_concat_arprot;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_0;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_1;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_2;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_3;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_arready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_4;




  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_arvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_4;

  xsc::xsc_concatenator<160, 5> * mp_m_axi_concat_awaddr;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_4;






  xsc::xsc_concatenator<15, 5> * mp_m_axi_concat_awprot;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_0;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_1;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_2;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_3;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_awready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_4;




  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_awvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_4;


  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_bready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_4;

  xsc::xsc_split<10, 5> * mp_m_axi_split_bresp;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_0;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_1;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_2;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_3;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_bvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_4;

  xsc::xsc_split<160, 5> * mp_m_axi_split_rdata;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_4;



  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_rready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_4;

  xsc::xsc_split<10, 5> * mp_m_axi_split_rresp;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_0;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_1;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_2;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_3;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_rvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_4;

  xsc::xsc_concatenator<160, 5> * mp_m_axi_concat_wdata;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_4;



  xsc::xsc_split<5, 5> * mp_m_axi_split_wready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_4;

  xsc::xsc_concatenator<20, 5> * mp_m_axi_concat_wstrb;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_0;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_1;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_2;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_3;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_4;


  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_wvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_4;

  // Transactor stubs
  xtlm::xtlm_aximm_initiator_stub * M00_AXI_transactor_initiator_rd_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M00_AXI_transactor_initiator_wr_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M01_AXI_transactor_initiator_rd_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M01_AXI_transactor_initiator_wr_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M02_AXI_transactor_initiator_rd_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M02_AXI_transactor_initiator_wr_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M03_AXI_transactor_initiator_rd_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M03_AXI_transactor_initiator_wr_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M04_AXI_transactor_initiator_rd_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M04_AXI_transactor_initiator_wr_socket_stub;
  xtlm::xtlm_aximm_target_stub * S00_AXI_transactor_target_rd_socket_stub;
  xtlm::xtlm_aximm_target_stub * S00_AXI_transactor_target_wr_socket_stub;

  // Socket stubs

};
#endif // VCSSYSTEMC




#ifdef MTI_SYSTEMC
#include "utils/xtlm_aximm_initiator_stub.h"

#include "utils/xtlm_aximm_target_stub.h"

class DllExport cl_clk_axil_xbar : public cl_clk_axil_xbar_sc
{
public:

  cl_clk_axil_xbar(const sc_core::sc_module_name& nm);
  virtual ~cl_clk_axil_xbar();

  // module pin-to-pin RTL interface

  sc_core::sc_in< bool > aclk;
  sc_core::sc_in< bool > aresetn;
  sc_core::sc_in< sc_dt::sc_bv<32> > s_axi_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<3> > s_axi_awprot;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_awvalid;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_awready;
  sc_core::sc_in< sc_dt::sc_bv<32> > s_axi_wdata;
  sc_core::sc_in< sc_dt::sc_bv<4> > s_axi_wstrb;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_wvalid;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_wready;
  sc_core::sc_out< sc_dt::sc_bv<2> > s_axi_bresp;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_bvalid;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_bready;
  sc_core::sc_in< sc_dt::sc_bv<32> > s_axi_araddr;
  sc_core::sc_in< sc_dt::sc_bv<3> > s_axi_arprot;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_arvalid;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_arready;
  sc_core::sc_out< sc_dt::sc_bv<32> > s_axi_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > s_axi_rresp;
  sc_core::sc_out< sc_dt::sc_bv<1> > s_axi_rvalid;
  sc_core::sc_in< sc_dt::sc_bv<1> > s_axi_rready;
  sc_core::sc_out< sc_dt::sc_bv<160> > m_axi_awaddr;
  sc_core::sc_out< sc_dt::sc_bv<15> > m_axi_awprot;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_awvalid;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_awready;
  sc_core::sc_out< sc_dt::sc_bv<160> > m_axi_wdata;
  sc_core::sc_out< sc_dt::sc_bv<20> > m_axi_wstrb;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_wvalid;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_wready;
  sc_core::sc_in< sc_dt::sc_bv<10> > m_axi_bresp;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_bvalid;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_bready;
  sc_core::sc_out< sc_dt::sc_bv<160> > m_axi_araddr;
  sc_core::sc_out< sc_dt::sc_bv<15> > m_axi_arprot;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_arvalid;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_arready;
  sc_core::sc_in< sc_dt::sc_bv<160> > m_axi_rdata;
  sc_core::sc_in< sc_dt::sc_bv<10> > m_axi_rresp;
  sc_core::sc_in< sc_dt::sc_bv<5> > m_axi_rvalid;
  sc_core::sc_out< sc_dt::sc_bv<5> > m_axi_rready;

  // Dummy Signals for IP Ports


protected:

  virtual void before_end_of_elaboration();

private:

  xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>* mp_S00_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_awvalid_converter;
  sc_signal< bool > m_s_axi_awvalid_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_awready_converter;
  sc_signal< bool > m_s_axi_awready_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_wvalid_converter;
  sc_signal< bool > m_s_axi_wvalid_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_wready_converter;
  sc_signal< bool > m_s_axi_wready_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_bvalid_converter;
  sc_signal< bool > m_s_axi_bvalid_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_bready_converter;
  sc_signal< bool > m_s_axi_bready_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_arvalid_converter;
  sc_signal< bool > m_s_axi_arvalid_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_arready_converter;
  sc_signal< bool > m_s_axi_arready_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_s_axi_rvalid_converter;
  sc_signal< bool > m_s_axi_rvalid_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_s_axi_rready_converter;
  sc_signal< bool > m_s_axi_rready_converter_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M00_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_0_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_0;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_0;
  sc_signal< bool > m_m_axi_awvalid_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_0;
  sc_signal< bool > m_m_axi_awready_converter_0_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_0_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_0;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_0;
  sc_signal< bool > m_m_axi_wvalid_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_0;
  sc_signal< bool > m_m_axi_wready_converter_0_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_0;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_0;
  sc_signal< bool > m_m_axi_bvalid_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_0;
  sc_signal< bool > m_m_axi_bready_converter_0_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_0_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_0;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_0;
  sc_signal< bool > m_m_axi_arvalid_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_0;
  sc_signal< bool > m_m_axi_arready_converter_0_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_0;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_0_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_0;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_0_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_0;
  sc_signal< bool > m_m_axi_rvalid_converter_0_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_0;
  sc_signal< bool > m_m_axi_rready_converter_0_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M01_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_1_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_1;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_1;
  sc_signal< bool > m_m_axi_awvalid_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_1;
  sc_signal< bool > m_m_axi_awready_converter_1_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_1_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_1;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_1;
  sc_signal< bool > m_m_axi_wvalid_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_1;
  sc_signal< bool > m_m_axi_wready_converter_1_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_1;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_1;
  sc_signal< bool > m_m_axi_bvalid_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_1;
  sc_signal< bool > m_m_axi_bready_converter_1_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_1_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_1;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_1;
  sc_signal< bool > m_m_axi_arvalid_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_1;
  sc_signal< bool > m_m_axi_arready_converter_1_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_1;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_1_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_1;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_1_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_1;
  sc_signal< bool > m_m_axi_rvalid_converter_1_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_1;
  sc_signal< bool > m_m_axi_rready_converter_1_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M02_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_2_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_2;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_2;
  sc_signal< bool > m_m_axi_awvalid_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_2;
  sc_signal< bool > m_m_axi_awready_converter_2_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_2_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_2;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_2;
  sc_signal< bool > m_m_axi_wvalid_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_2;
  sc_signal< bool > m_m_axi_wready_converter_2_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_2;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_2;
  sc_signal< bool > m_m_axi_bvalid_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_2;
  sc_signal< bool > m_m_axi_bready_converter_2_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_2_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_2;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_2;
  sc_signal< bool > m_m_axi_arvalid_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_2;
  sc_signal< bool > m_m_axi_arready_converter_2_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_2;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_2_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_2;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_2_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_2;
  sc_signal< bool > m_m_axi_rvalid_converter_2_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_2;
  sc_signal< bool > m_m_axi_rready_converter_2_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M03_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_3_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_3;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_3;
  sc_signal< bool > m_m_axi_awvalid_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_3;
  sc_signal< bool > m_m_axi_awready_converter_3_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_3_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_3;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_3;
  sc_signal< bool > m_m_axi_wvalid_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_3;
  sc_signal< bool > m_m_axi_wready_converter_3_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_3;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_3;
  sc_signal< bool > m_m_axi_bvalid_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_3;
  sc_signal< bool > m_m_axi_bready_converter_3_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_3_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_3;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_3;
  sc_signal< bool > m_m_axi_arvalid_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_3;
  sc_signal< bool > m_m_axi_arready_converter_3_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_3;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_3_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_3;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_3_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_3;
  sc_signal< bool > m_m_axi_rvalid_converter_3_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_3;
  sc_signal< bool > m_m_axi_rready_converter_3_signal;
  xtlm::xaximm_xtlm2pin_t<32,32,1,1,1,1,1,1>* mp_M04_AXI_transactor;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_awaddr_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_awaddr_converter_4_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_awprot_converter_4;
  sc_signal< sc_bv<3> > m_m_axi_awprot_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_awvalid_converter_4;
  sc_signal< bool > m_m_axi_awvalid_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_awready_converter_4;
  sc_signal< bool > m_m_axi_awready_converter_4_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_wdata_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_wdata_converter_4_signal;
  xsc::common::vector2vector_converter<4,20>* mp_m_axi_wstrb_converter_4;
  sc_signal< sc_bv<4> > m_m_axi_wstrb_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_wvalid_converter_4;
  sc_signal< bool > m_m_axi_wvalid_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_wready_converter_4;
  sc_signal< bool > m_m_axi_wready_converter_4_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_bresp_converter_4;
  sc_signal< sc_bv<2> > m_m_axi_bresp_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_bvalid_converter_4;
  sc_signal< bool > m_m_axi_bvalid_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_bready_converter_4;
  sc_signal< bool > m_m_axi_bready_converter_4_signal;
  xsc::common::vector2vector_converter<32,160>* mp_m_axi_araddr_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_araddr_converter_4_signal;
  xsc::common::vector2vector_converter<3,15>* mp_m_axi_arprot_converter_4;
  sc_signal< sc_bv<3> > m_m_axi_arprot_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_arvalid_converter_4;
  sc_signal< bool > m_m_axi_arvalid_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_arready_converter_4;
  sc_signal< bool > m_m_axi_arready_converter_4_signal;
  xsc::common::vector2vector_converter<160,32>* mp_m_axi_rdata_converter_4;
  sc_signal< sc_bv<32> > m_m_axi_rdata_converter_4_signal;
  xsc::common::vector2vector_converter<10,2>* mp_m_axi_rresp_converter_4;
  sc_signal< sc_bv<2> > m_m_axi_rresp_converter_4_signal;
  xsc::common::vectorN2scalar_converter<5>* mp_m_axi_rvalid_converter_4;
  sc_signal< bool > m_m_axi_rvalid_converter_4_signal;
  xsc::common::scalar2vectorN_converter<5>* mp_m_axi_rready_converter_4;
  sc_signal< bool > m_m_axi_rready_converter_4_signal;

  xsc::xsc_concatenator<160, 5> * mp_m_axi_concat_araddr;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_araddr_out_4;






  xsc::xsc_concatenator<15, 5> * mp_m_axi_concat_arprot;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_0;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_1;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_2;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_3;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_arprot_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_arready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_arready_out_4;




  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_arvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_arvalid_out_4;

  xsc::xsc_concatenator<160, 5> * mp_m_axi_concat_awaddr;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_awaddr_out_4;






  xsc::xsc_concatenator<15, 5> * mp_m_axi_concat_awprot;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_0;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_1;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_2;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_3;
  sc_signal<sc_dt::sc_bv<15> > m_axi_concat_awprot_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_awready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_awready_out_4;




  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_awvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_awvalid_out_4;


  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_bready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_bready_out_4;

  xsc::xsc_split<10, 5> * mp_m_axi_split_bresp;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_0;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_1;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_2;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_3;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_bresp_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_bvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_bvalid_out_4;

  xsc::xsc_split<160, 5> * mp_m_axi_split_rdata;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_split_rdata_out_4;



  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_rready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_rready_out_4;

  xsc::xsc_split<10, 5> * mp_m_axi_split_rresp;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_0;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_1;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_2;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_3;
  sc_signal<sc_dt::sc_bv<10> > m_axi_split_rresp_out_4;


  xsc::xsc_split<5, 5> * mp_m_axi_split_rvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_rvalid_out_4;

  xsc::xsc_concatenator<160, 5> * mp_m_axi_concat_wdata;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_0;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_1;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_2;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_3;
  sc_signal<sc_dt::sc_bv<160> > m_axi_concat_wdata_out_4;



  xsc::xsc_split<5, 5> * mp_m_axi_split_wready;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_split_wready_out_4;

  xsc::xsc_concatenator<20, 5> * mp_m_axi_concat_wstrb;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_0;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_1;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_2;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_3;
  sc_signal<sc_dt::sc_bv<20> > m_axi_concat_wstrb_out_4;


  xsc::xsc_concatenator<5, 5> * mp_m_axi_concat_wvalid;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_0;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_1;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_2;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_3;
  sc_signal<sc_dt::sc_bv<5> > m_axi_concat_wvalid_out_4;

  // Transactor stubs
  xtlm::xtlm_aximm_initiator_stub * M00_AXI_transactor_initiator_rd_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M00_AXI_transactor_initiator_wr_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M01_AXI_transactor_initiator_rd_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M01_AXI_transactor_initiator_wr_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M02_AXI_transactor_initiator_rd_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M02_AXI_transactor_initiator_wr_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M03_AXI_transactor_initiator_rd_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M03_AXI_transactor_initiator_wr_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M04_AXI_transactor_initiator_rd_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M04_AXI_transactor_initiator_wr_socket_stub;
  xtlm::xtlm_aximm_target_stub * S00_AXI_transactor_target_rd_socket_stub;
  xtlm::xtlm_aximm_target_stub * S00_AXI_transactor_target_wr_socket_stub;

  // Socket stubs

};
#endif // MTI_SYSTEMC
#endif // IP_CL_CLK_AXIL_XBAR_H_
