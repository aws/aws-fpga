#ifndef IP_CL_AXI_SC_2X2_SMARTCONNECT_0_0_H_
#define IP_CL_AXI_SC_2X2_SMARTCONNECT_0_0_H_

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

#include "cl_axi_sc_2x2_smartconnect_0_0_sc.h"




#ifdef XILINX_SIMULATOR
class DllExport cl_axi_sc_2x2_smartconnect_0_0 : public cl_axi_sc_2x2_smartconnect_0_0_sc
{
public:

  cl_axi_sc_2x2_smartconnect_0_0(const sc_core::sc_module_name& nm);
  virtual ~cl_axi_sc_2x2_smartconnect_0_0();

  // module pin-to-pin RTL interface

  sc_core::sc_in< bool > aclk;
  sc_core::sc_in< bool > aresetn;
  sc_core::sc_in< sc_dt::sc_bv<16> > S00_AXI_awid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S00_AXI_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S00_AXI_awlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_awsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S00_AXI_awburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S00_AXI_awlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_awcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_awprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_awqos;
  sc_core::sc_in< bool > S00_AXI_awvalid;
  sc_core::sc_out< bool > S00_AXI_awready;
  sc_core::sc_in< sc_dt::sc_bv<512> > S00_AXI_wdata;
  sc_core::sc_in< sc_dt::sc_bv<64> > S00_AXI_wstrb;
  sc_core::sc_in< bool > S00_AXI_wlast;
  sc_core::sc_in< bool > S00_AXI_wvalid;
  sc_core::sc_out< bool > S00_AXI_wready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S00_AXI_bid;
  sc_core::sc_out< sc_dt::sc_bv<2> > S00_AXI_bresp;
  sc_core::sc_out< bool > S00_AXI_bvalid;
  sc_core::sc_in< bool > S00_AXI_bready;
  sc_core::sc_in< sc_dt::sc_bv<16> > S00_AXI_arid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S00_AXI_araddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S00_AXI_arlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_arsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S00_AXI_arburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S00_AXI_arlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_arcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_arprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_arqos;
  sc_core::sc_in< bool > S00_AXI_arvalid;
  sc_core::sc_out< bool > S00_AXI_arready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S00_AXI_rid;
  sc_core::sc_out< sc_dt::sc_bv<512> > S00_AXI_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > S00_AXI_rresp;
  sc_core::sc_out< bool > S00_AXI_rlast;
  sc_core::sc_out< bool > S00_AXI_rvalid;
  sc_core::sc_in< bool > S00_AXI_rready;
  sc_core::sc_in< sc_dt::sc_bv<16> > S01_AXI_awid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S01_AXI_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S01_AXI_awlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_awsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S01_AXI_awburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S01_AXI_awlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_awcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_awprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_awqos;
  sc_core::sc_in< bool > S01_AXI_awvalid;
  sc_core::sc_out< bool > S01_AXI_awready;
  sc_core::sc_in< sc_dt::sc_bv<512> > S01_AXI_wdata;
  sc_core::sc_in< sc_dt::sc_bv<64> > S01_AXI_wstrb;
  sc_core::sc_in< bool > S01_AXI_wlast;
  sc_core::sc_in< bool > S01_AXI_wvalid;
  sc_core::sc_out< bool > S01_AXI_wready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S01_AXI_bid;
  sc_core::sc_out< sc_dt::sc_bv<2> > S01_AXI_bresp;
  sc_core::sc_out< bool > S01_AXI_bvalid;
  sc_core::sc_in< bool > S01_AXI_bready;
  sc_core::sc_in< sc_dt::sc_bv<16> > S01_AXI_arid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S01_AXI_araddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S01_AXI_arlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_arsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S01_AXI_arburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S01_AXI_arlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_arcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_arprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_arqos;
  sc_core::sc_in< bool > S01_AXI_arvalid;
  sc_core::sc_out< bool > S01_AXI_arready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S01_AXI_rid;
  sc_core::sc_out< sc_dt::sc_bv<512> > S01_AXI_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > S01_AXI_rresp;
  sc_core::sc_out< bool > S01_AXI_rlast;
  sc_core::sc_out< bool > S01_AXI_rvalid;
  sc_core::sc_in< bool > S01_AXI_rready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M00_AXI_awaddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M00_AXI_awlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_awsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M00_AXI_awburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M00_AXI_awlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_awcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_awprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_awqos;
  sc_core::sc_out< bool > M00_AXI_awvalid;
  sc_core::sc_in< bool > M00_AXI_awready;
  sc_core::sc_out< sc_dt::sc_bv<512> > M00_AXI_wdata;
  sc_core::sc_out< sc_dt::sc_bv<64> > M00_AXI_wstrb;
  sc_core::sc_out< bool > M00_AXI_wlast;
  sc_core::sc_out< bool > M00_AXI_wvalid;
  sc_core::sc_in< bool > M00_AXI_wready;
  sc_core::sc_in< sc_dt::sc_bv<2> > M00_AXI_bresp;
  sc_core::sc_in< bool > M00_AXI_bvalid;
  sc_core::sc_out< bool > M00_AXI_bready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M00_AXI_araddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M00_AXI_arlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_arsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M00_AXI_arburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M00_AXI_arlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_arcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_arprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_arqos;
  sc_core::sc_out< bool > M00_AXI_arvalid;
  sc_core::sc_in< bool > M00_AXI_arready;
  sc_core::sc_in< sc_dt::sc_bv<512> > M00_AXI_rdata;
  sc_core::sc_in< sc_dt::sc_bv<2> > M00_AXI_rresp;
  sc_core::sc_in< bool > M00_AXI_rlast;
  sc_core::sc_in< bool > M00_AXI_rvalid;
  sc_core::sc_out< bool > M00_AXI_rready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M01_AXI_awaddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M01_AXI_awlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_awsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M01_AXI_awburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M01_AXI_awlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_awcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_awprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_awqos;
  sc_core::sc_out< bool > M01_AXI_awvalid;
  sc_core::sc_in< bool > M01_AXI_awready;
  sc_core::sc_out< sc_dt::sc_bv<512> > M01_AXI_wdata;
  sc_core::sc_out< sc_dt::sc_bv<64> > M01_AXI_wstrb;
  sc_core::sc_out< bool > M01_AXI_wlast;
  sc_core::sc_out< bool > M01_AXI_wvalid;
  sc_core::sc_in< bool > M01_AXI_wready;
  sc_core::sc_in< sc_dt::sc_bv<2> > M01_AXI_bresp;
  sc_core::sc_in< bool > M01_AXI_bvalid;
  sc_core::sc_out< bool > M01_AXI_bready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M01_AXI_araddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M01_AXI_arlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_arsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M01_AXI_arburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M01_AXI_arlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_arcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_arprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_arqos;
  sc_core::sc_out< bool > M01_AXI_arvalid;
  sc_core::sc_in< bool > M01_AXI_arready;
  sc_core::sc_in< sc_dt::sc_bv<512> > M01_AXI_rdata;
  sc_core::sc_in< sc_dt::sc_bv<2> > M01_AXI_rresp;
  sc_core::sc_in< bool > M01_AXI_rlast;
  sc_core::sc_in< bool > M01_AXI_rvalid;
  sc_core::sc_out< bool > M01_AXI_rready;

  // Dummy Signals for IP Ports


protected:

  virtual void before_end_of_elaboration();

private:

  xtlm::xaximm_pin2xtlm_t<512,64,16,1,1,1,1,1>* mp_S00_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_S00_AXI_awlock_converter;
  sc_signal< bool > m_S00_AXI_awlock_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_S00_AXI_arlock_converter;
  sc_signal< bool > m_S00_AXI_arlock_converter_signal;
  xtlm::xaximm_pin2xtlm_t<512,64,16,1,1,1,1,1>* mp_S01_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_S01_AXI_awlock_converter;
  sc_signal< bool > m_S01_AXI_awlock_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_S01_AXI_arlock_converter;
  sc_signal< bool > m_S01_AXI_arlock_converter_signal;
  xtlm::xaximm_xtlm2pin_t<512,64,1,1,1,1,1,1>* mp_M00_AXI_transactor;
  xsc::common::scalar2vectorN_converter<1>* mp_M00_AXI_awlock_converter;
  sc_signal< bool > m_M00_AXI_awlock_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_M00_AXI_arlock_converter;
  sc_signal< bool > m_M00_AXI_arlock_converter_signal;
  xtlm::xaximm_xtlm2pin_t<512,64,1,1,1,1,1,1>* mp_M01_AXI_transactor;
  xsc::common::scalar2vectorN_converter<1>* mp_M01_AXI_awlock_converter;
  sc_signal< bool > m_M01_AXI_awlock_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_M01_AXI_arlock_converter;
  sc_signal< bool > m_M01_AXI_arlock_converter_signal;

};
#endif // XILINX_SIMULATOR




#ifdef XM_SYSTEMC
class DllExport cl_axi_sc_2x2_smartconnect_0_0 : public cl_axi_sc_2x2_smartconnect_0_0_sc
{
public:

  cl_axi_sc_2x2_smartconnect_0_0(const sc_core::sc_module_name& nm);
  virtual ~cl_axi_sc_2x2_smartconnect_0_0();

  // module pin-to-pin RTL interface

  sc_core::sc_in< bool > aclk;
  sc_core::sc_in< bool > aresetn;
  sc_core::sc_in< sc_dt::sc_bv<16> > S00_AXI_awid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S00_AXI_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S00_AXI_awlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_awsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S00_AXI_awburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S00_AXI_awlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_awcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_awprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_awqos;
  sc_core::sc_in< bool > S00_AXI_awvalid;
  sc_core::sc_out< bool > S00_AXI_awready;
  sc_core::sc_in< sc_dt::sc_bv<512> > S00_AXI_wdata;
  sc_core::sc_in< sc_dt::sc_bv<64> > S00_AXI_wstrb;
  sc_core::sc_in< bool > S00_AXI_wlast;
  sc_core::sc_in< bool > S00_AXI_wvalid;
  sc_core::sc_out< bool > S00_AXI_wready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S00_AXI_bid;
  sc_core::sc_out< sc_dt::sc_bv<2> > S00_AXI_bresp;
  sc_core::sc_out< bool > S00_AXI_bvalid;
  sc_core::sc_in< bool > S00_AXI_bready;
  sc_core::sc_in< sc_dt::sc_bv<16> > S00_AXI_arid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S00_AXI_araddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S00_AXI_arlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_arsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S00_AXI_arburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S00_AXI_arlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_arcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_arprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_arqos;
  sc_core::sc_in< bool > S00_AXI_arvalid;
  sc_core::sc_out< bool > S00_AXI_arready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S00_AXI_rid;
  sc_core::sc_out< sc_dt::sc_bv<512> > S00_AXI_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > S00_AXI_rresp;
  sc_core::sc_out< bool > S00_AXI_rlast;
  sc_core::sc_out< bool > S00_AXI_rvalid;
  sc_core::sc_in< bool > S00_AXI_rready;
  sc_core::sc_in< sc_dt::sc_bv<16> > S01_AXI_awid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S01_AXI_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S01_AXI_awlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_awsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S01_AXI_awburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S01_AXI_awlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_awcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_awprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_awqos;
  sc_core::sc_in< bool > S01_AXI_awvalid;
  sc_core::sc_out< bool > S01_AXI_awready;
  sc_core::sc_in< sc_dt::sc_bv<512> > S01_AXI_wdata;
  sc_core::sc_in< sc_dt::sc_bv<64> > S01_AXI_wstrb;
  sc_core::sc_in< bool > S01_AXI_wlast;
  sc_core::sc_in< bool > S01_AXI_wvalid;
  sc_core::sc_out< bool > S01_AXI_wready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S01_AXI_bid;
  sc_core::sc_out< sc_dt::sc_bv<2> > S01_AXI_bresp;
  sc_core::sc_out< bool > S01_AXI_bvalid;
  sc_core::sc_in< bool > S01_AXI_bready;
  sc_core::sc_in< sc_dt::sc_bv<16> > S01_AXI_arid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S01_AXI_araddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S01_AXI_arlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_arsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S01_AXI_arburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S01_AXI_arlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_arcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_arprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_arqos;
  sc_core::sc_in< bool > S01_AXI_arvalid;
  sc_core::sc_out< bool > S01_AXI_arready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S01_AXI_rid;
  sc_core::sc_out< sc_dt::sc_bv<512> > S01_AXI_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > S01_AXI_rresp;
  sc_core::sc_out< bool > S01_AXI_rlast;
  sc_core::sc_out< bool > S01_AXI_rvalid;
  sc_core::sc_in< bool > S01_AXI_rready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M00_AXI_awaddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M00_AXI_awlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_awsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M00_AXI_awburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M00_AXI_awlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_awcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_awprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_awqos;
  sc_core::sc_out< bool > M00_AXI_awvalid;
  sc_core::sc_in< bool > M00_AXI_awready;
  sc_core::sc_out< sc_dt::sc_bv<512> > M00_AXI_wdata;
  sc_core::sc_out< sc_dt::sc_bv<64> > M00_AXI_wstrb;
  sc_core::sc_out< bool > M00_AXI_wlast;
  sc_core::sc_out< bool > M00_AXI_wvalid;
  sc_core::sc_in< bool > M00_AXI_wready;
  sc_core::sc_in< sc_dt::sc_bv<2> > M00_AXI_bresp;
  sc_core::sc_in< bool > M00_AXI_bvalid;
  sc_core::sc_out< bool > M00_AXI_bready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M00_AXI_araddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M00_AXI_arlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_arsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M00_AXI_arburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M00_AXI_arlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_arcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_arprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_arqos;
  sc_core::sc_out< bool > M00_AXI_arvalid;
  sc_core::sc_in< bool > M00_AXI_arready;
  sc_core::sc_in< sc_dt::sc_bv<512> > M00_AXI_rdata;
  sc_core::sc_in< sc_dt::sc_bv<2> > M00_AXI_rresp;
  sc_core::sc_in< bool > M00_AXI_rlast;
  sc_core::sc_in< bool > M00_AXI_rvalid;
  sc_core::sc_out< bool > M00_AXI_rready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M01_AXI_awaddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M01_AXI_awlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_awsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M01_AXI_awburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M01_AXI_awlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_awcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_awprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_awqos;
  sc_core::sc_out< bool > M01_AXI_awvalid;
  sc_core::sc_in< bool > M01_AXI_awready;
  sc_core::sc_out< sc_dt::sc_bv<512> > M01_AXI_wdata;
  sc_core::sc_out< sc_dt::sc_bv<64> > M01_AXI_wstrb;
  sc_core::sc_out< bool > M01_AXI_wlast;
  sc_core::sc_out< bool > M01_AXI_wvalid;
  sc_core::sc_in< bool > M01_AXI_wready;
  sc_core::sc_in< sc_dt::sc_bv<2> > M01_AXI_bresp;
  sc_core::sc_in< bool > M01_AXI_bvalid;
  sc_core::sc_out< bool > M01_AXI_bready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M01_AXI_araddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M01_AXI_arlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_arsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M01_AXI_arburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M01_AXI_arlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_arcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_arprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_arqos;
  sc_core::sc_out< bool > M01_AXI_arvalid;
  sc_core::sc_in< bool > M01_AXI_arready;
  sc_core::sc_in< sc_dt::sc_bv<512> > M01_AXI_rdata;
  sc_core::sc_in< sc_dt::sc_bv<2> > M01_AXI_rresp;
  sc_core::sc_in< bool > M01_AXI_rlast;
  sc_core::sc_in< bool > M01_AXI_rvalid;
  sc_core::sc_out< bool > M01_AXI_rready;

  // Dummy Signals for IP Ports


protected:

  virtual void before_end_of_elaboration();

private:

  xtlm::xaximm_pin2xtlm_t<512,64,16,1,1,1,1,1>* mp_S00_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_S00_AXI_awlock_converter;
  sc_signal< bool > m_S00_AXI_awlock_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_S00_AXI_arlock_converter;
  sc_signal< bool > m_S00_AXI_arlock_converter_signal;
  xtlm::xaximm_pin2xtlm_t<512,64,16,1,1,1,1,1>* mp_S01_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_S01_AXI_awlock_converter;
  sc_signal< bool > m_S01_AXI_awlock_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_S01_AXI_arlock_converter;
  sc_signal< bool > m_S01_AXI_arlock_converter_signal;
  xtlm::xaximm_xtlm2pin_t<512,64,1,1,1,1,1,1>* mp_M00_AXI_transactor;
  xsc::common::scalar2vectorN_converter<1>* mp_M00_AXI_awlock_converter;
  sc_signal< bool > m_M00_AXI_awlock_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_M00_AXI_arlock_converter;
  sc_signal< bool > m_M00_AXI_arlock_converter_signal;
  xtlm::xaximm_xtlm2pin_t<512,64,1,1,1,1,1,1>* mp_M01_AXI_transactor;
  xsc::common::scalar2vectorN_converter<1>* mp_M01_AXI_awlock_converter;
  sc_signal< bool > m_M01_AXI_awlock_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_M01_AXI_arlock_converter;
  sc_signal< bool > m_M01_AXI_arlock_converter_signal;

};
#endif // XM_SYSTEMC




#ifdef RIVIERA
class DllExport cl_axi_sc_2x2_smartconnect_0_0 : public cl_axi_sc_2x2_smartconnect_0_0_sc
{
public:

  cl_axi_sc_2x2_smartconnect_0_0(const sc_core::sc_module_name& nm);
  virtual ~cl_axi_sc_2x2_smartconnect_0_0();

  // module pin-to-pin RTL interface

  sc_core::sc_in< bool > aclk;
  sc_core::sc_in< bool > aresetn;
  sc_core::sc_in< sc_dt::sc_bv<16> > S00_AXI_awid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S00_AXI_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S00_AXI_awlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_awsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S00_AXI_awburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S00_AXI_awlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_awcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_awprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_awqos;
  sc_core::sc_in< bool > S00_AXI_awvalid;
  sc_core::sc_out< bool > S00_AXI_awready;
  sc_core::sc_in< sc_dt::sc_bv<512> > S00_AXI_wdata;
  sc_core::sc_in< sc_dt::sc_bv<64> > S00_AXI_wstrb;
  sc_core::sc_in< bool > S00_AXI_wlast;
  sc_core::sc_in< bool > S00_AXI_wvalid;
  sc_core::sc_out< bool > S00_AXI_wready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S00_AXI_bid;
  sc_core::sc_out< sc_dt::sc_bv<2> > S00_AXI_bresp;
  sc_core::sc_out< bool > S00_AXI_bvalid;
  sc_core::sc_in< bool > S00_AXI_bready;
  sc_core::sc_in< sc_dt::sc_bv<16> > S00_AXI_arid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S00_AXI_araddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S00_AXI_arlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_arsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S00_AXI_arburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S00_AXI_arlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_arcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_arprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_arqos;
  sc_core::sc_in< bool > S00_AXI_arvalid;
  sc_core::sc_out< bool > S00_AXI_arready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S00_AXI_rid;
  sc_core::sc_out< sc_dt::sc_bv<512> > S00_AXI_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > S00_AXI_rresp;
  sc_core::sc_out< bool > S00_AXI_rlast;
  sc_core::sc_out< bool > S00_AXI_rvalid;
  sc_core::sc_in< bool > S00_AXI_rready;
  sc_core::sc_in< sc_dt::sc_bv<16> > S01_AXI_awid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S01_AXI_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S01_AXI_awlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_awsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S01_AXI_awburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S01_AXI_awlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_awcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_awprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_awqos;
  sc_core::sc_in< bool > S01_AXI_awvalid;
  sc_core::sc_out< bool > S01_AXI_awready;
  sc_core::sc_in< sc_dt::sc_bv<512> > S01_AXI_wdata;
  sc_core::sc_in< sc_dt::sc_bv<64> > S01_AXI_wstrb;
  sc_core::sc_in< bool > S01_AXI_wlast;
  sc_core::sc_in< bool > S01_AXI_wvalid;
  sc_core::sc_out< bool > S01_AXI_wready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S01_AXI_bid;
  sc_core::sc_out< sc_dt::sc_bv<2> > S01_AXI_bresp;
  sc_core::sc_out< bool > S01_AXI_bvalid;
  sc_core::sc_in< bool > S01_AXI_bready;
  sc_core::sc_in< sc_dt::sc_bv<16> > S01_AXI_arid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S01_AXI_araddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S01_AXI_arlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_arsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S01_AXI_arburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S01_AXI_arlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_arcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_arprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_arqos;
  sc_core::sc_in< bool > S01_AXI_arvalid;
  sc_core::sc_out< bool > S01_AXI_arready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S01_AXI_rid;
  sc_core::sc_out< sc_dt::sc_bv<512> > S01_AXI_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > S01_AXI_rresp;
  sc_core::sc_out< bool > S01_AXI_rlast;
  sc_core::sc_out< bool > S01_AXI_rvalid;
  sc_core::sc_in< bool > S01_AXI_rready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M00_AXI_awaddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M00_AXI_awlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_awsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M00_AXI_awburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M00_AXI_awlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_awcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_awprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_awqos;
  sc_core::sc_out< bool > M00_AXI_awvalid;
  sc_core::sc_in< bool > M00_AXI_awready;
  sc_core::sc_out< sc_dt::sc_bv<512> > M00_AXI_wdata;
  sc_core::sc_out< sc_dt::sc_bv<64> > M00_AXI_wstrb;
  sc_core::sc_out< bool > M00_AXI_wlast;
  sc_core::sc_out< bool > M00_AXI_wvalid;
  sc_core::sc_in< bool > M00_AXI_wready;
  sc_core::sc_in< sc_dt::sc_bv<2> > M00_AXI_bresp;
  sc_core::sc_in< bool > M00_AXI_bvalid;
  sc_core::sc_out< bool > M00_AXI_bready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M00_AXI_araddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M00_AXI_arlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_arsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M00_AXI_arburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M00_AXI_arlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_arcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_arprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_arqos;
  sc_core::sc_out< bool > M00_AXI_arvalid;
  sc_core::sc_in< bool > M00_AXI_arready;
  sc_core::sc_in< sc_dt::sc_bv<512> > M00_AXI_rdata;
  sc_core::sc_in< sc_dt::sc_bv<2> > M00_AXI_rresp;
  sc_core::sc_in< bool > M00_AXI_rlast;
  sc_core::sc_in< bool > M00_AXI_rvalid;
  sc_core::sc_out< bool > M00_AXI_rready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M01_AXI_awaddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M01_AXI_awlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_awsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M01_AXI_awburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M01_AXI_awlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_awcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_awprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_awqos;
  sc_core::sc_out< bool > M01_AXI_awvalid;
  sc_core::sc_in< bool > M01_AXI_awready;
  sc_core::sc_out< sc_dt::sc_bv<512> > M01_AXI_wdata;
  sc_core::sc_out< sc_dt::sc_bv<64> > M01_AXI_wstrb;
  sc_core::sc_out< bool > M01_AXI_wlast;
  sc_core::sc_out< bool > M01_AXI_wvalid;
  sc_core::sc_in< bool > M01_AXI_wready;
  sc_core::sc_in< sc_dt::sc_bv<2> > M01_AXI_bresp;
  sc_core::sc_in< bool > M01_AXI_bvalid;
  sc_core::sc_out< bool > M01_AXI_bready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M01_AXI_araddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M01_AXI_arlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_arsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M01_AXI_arburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M01_AXI_arlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_arcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_arprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_arqos;
  sc_core::sc_out< bool > M01_AXI_arvalid;
  sc_core::sc_in< bool > M01_AXI_arready;
  sc_core::sc_in< sc_dt::sc_bv<512> > M01_AXI_rdata;
  sc_core::sc_in< sc_dt::sc_bv<2> > M01_AXI_rresp;
  sc_core::sc_in< bool > M01_AXI_rlast;
  sc_core::sc_in< bool > M01_AXI_rvalid;
  sc_core::sc_out< bool > M01_AXI_rready;

  // Dummy Signals for IP Ports


protected:

  virtual void before_end_of_elaboration();

private:

  xtlm::xaximm_pin2xtlm_t<512,64,16,1,1,1,1,1>* mp_S00_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_S00_AXI_awlock_converter;
  sc_signal< bool > m_S00_AXI_awlock_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_S00_AXI_arlock_converter;
  sc_signal< bool > m_S00_AXI_arlock_converter_signal;
  xtlm::xaximm_pin2xtlm_t<512,64,16,1,1,1,1,1>* mp_S01_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_S01_AXI_awlock_converter;
  sc_signal< bool > m_S01_AXI_awlock_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_S01_AXI_arlock_converter;
  sc_signal< bool > m_S01_AXI_arlock_converter_signal;
  xtlm::xaximm_xtlm2pin_t<512,64,1,1,1,1,1,1>* mp_M00_AXI_transactor;
  xsc::common::scalar2vectorN_converter<1>* mp_M00_AXI_awlock_converter;
  sc_signal< bool > m_M00_AXI_awlock_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_M00_AXI_arlock_converter;
  sc_signal< bool > m_M00_AXI_arlock_converter_signal;
  xtlm::xaximm_xtlm2pin_t<512,64,1,1,1,1,1,1>* mp_M01_AXI_transactor;
  xsc::common::scalar2vectorN_converter<1>* mp_M01_AXI_awlock_converter;
  sc_signal< bool > m_M01_AXI_awlock_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_M01_AXI_arlock_converter;
  sc_signal< bool > m_M01_AXI_arlock_converter_signal;

};
#endif // RIVIERA




#ifdef VCSSYSTEMC
#include "utils/xtlm_aximm_initiator_stub.h"

#include "utils/xtlm_aximm_target_stub.h"

class DllExport cl_axi_sc_2x2_smartconnect_0_0 : public cl_axi_sc_2x2_smartconnect_0_0_sc
{
public:

  cl_axi_sc_2x2_smartconnect_0_0(const sc_core::sc_module_name& nm);
  virtual ~cl_axi_sc_2x2_smartconnect_0_0();

  // module pin-to-pin RTL interface

  sc_core::sc_in< bool > aclk;
  sc_core::sc_in< bool > aresetn;
  sc_core::sc_in< sc_dt::sc_bv<16> > S00_AXI_awid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S00_AXI_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S00_AXI_awlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_awsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S00_AXI_awburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S00_AXI_awlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_awcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_awprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_awqos;
  sc_core::sc_in< bool > S00_AXI_awvalid;
  sc_core::sc_out< bool > S00_AXI_awready;
  sc_core::sc_in< sc_dt::sc_bv<512> > S00_AXI_wdata;
  sc_core::sc_in< sc_dt::sc_bv<64> > S00_AXI_wstrb;
  sc_core::sc_in< bool > S00_AXI_wlast;
  sc_core::sc_in< bool > S00_AXI_wvalid;
  sc_core::sc_out< bool > S00_AXI_wready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S00_AXI_bid;
  sc_core::sc_out< sc_dt::sc_bv<2> > S00_AXI_bresp;
  sc_core::sc_out< bool > S00_AXI_bvalid;
  sc_core::sc_in< bool > S00_AXI_bready;
  sc_core::sc_in< sc_dt::sc_bv<16> > S00_AXI_arid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S00_AXI_araddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S00_AXI_arlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_arsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S00_AXI_arburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S00_AXI_arlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_arcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_arprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_arqos;
  sc_core::sc_in< bool > S00_AXI_arvalid;
  sc_core::sc_out< bool > S00_AXI_arready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S00_AXI_rid;
  sc_core::sc_out< sc_dt::sc_bv<512> > S00_AXI_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > S00_AXI_rresp;
  sc_core::sc_out< bool > S00_AXI_rlast;
  sc_core::sc_out< bool > S00_AXI_rvalid;
  sc_core::sc_in< bool > S00_AXI_rready;
  sc_core::sc_in< sc_dt::sc_bv<16> > S01_AXI_awid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S01_AXI_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S01_AXI_awlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_awsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S01_AXI_awburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S01_AXI_awlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_awcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_awprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_awqos;
  sc_core::sc_in< bool > S01_AXI_awvalid;
  sc_core::sc_out< bool > S01_AXI_awready;
  sc_core::sc_in< sc_dt::sc_bv<512> > S01_AXI_wdata;
  sc_core::sc_in< sc_dt::sc_bv<64> > S01_AXI_wstrb;
  sc_core::sc_in< bool > S01_AXI_wlast;
  sc_core::sc_in< bool > S01_AXI_wvalid;
  sc_core::sc_out< bool > S01_AXI_wready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S01_AXI_bid;
  sc_core::sc_out< sc_dt::sc_bv<2> > S01_AXI_bresp;
  sc_core::sc_out< bool > S01_AXI_bvalid;
  sc_core::sc_in< bool > S01_AXI_bready;
  sc_core::sc_in< sc_dt::sc_bv<16> > S01_AXI_arid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S01_AXI_araddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S01_AXI_arlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_arsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S01_AXI_arburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S01_AXI_arlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_arcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_arprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_arqos;
  sc_core::sc_in< bool > S01_AXI_arvalid;
  sc_core::sc_out< bool > S01_AXI_arready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S01_AXI_rid;
  sc_core::sc_out< sc_dt::sc_bv<512> > S01_AXI_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > S01_AXI_rresp;
  sc_core::sc_out< bool > S01_AXI_rlast;
  sc_core::sc_out< bool > S01_AXI_rvalid;
  sc_core::sc_in< bool > S01_AXI_rready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M00_AXI_awaddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M00_AXI_awlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_awsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M00_AXI_awburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M00_AXI_awlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_awcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_awprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_awqos;
  sc_core::sc_out< bool > M00_AXI_awvalid;
  sc_core::sc_in< bool > M00_AXI_awready;
  sc_core::sc_out< sc_dt::sc_bv<512> > M00_AXI_wdata;
  sc_core::sc_out< sc_dt::sc_bv<64> > M00_AXI_wstrb;
  sc_core::sc_out< bool > M00_AXI_wlast;
  sc_core::sc_out< bool > M00_AXI_wvalid;
  sc_core::sc_in< bool > M00_AXI_wready;
  sc_core::sc_in< sc_dt::sc_bv<2> > M00_AXI_bresp;
  sc_core::sc_in< bool > M00_AXI_bvalid;
  sc_core::sc_out< bool > M00_AXI_bready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M00_AXI_araddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M00_AXI_arlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_arsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M00_AXI_arburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M00_AXI_arlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_arcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_arprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_arqos;
  sc_core::sc_out< bool > M00_AXI_arvalid;
  sc_core::sc_in< bool > M00_AXI_arready;
  sc_core::sc_in< sc_dt::sc_bv<512> > M00_AXI_rdata;
  sc_core::sc_in< sc_dt::sc_bv<2> > M00_AXI_rresp;
  sc_core::sc_in< bool > M00_AXI_rlast;
  sc_core::sc_in< bool > M00_AXI_rvalid;
  sc_core::sc_out< bool > M00_AXI_rready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M01_AXI_awaddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M01_AXI_awlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_awsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M01_AXI_awburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M01_AXI_awlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_awcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_awprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_awqos;
  sc_core::sc_out< bool > M01_AXI_awvalid;
  sc_core::sc_in< bool > M01_AXI_awready;
  sc_core::sc_out< sc_dt::sc_bv<512> > M01_AXI_wdata;
  sc_core::sc_out< sc_dt::sc_bv<64> > M01_AXI_wstrb;
  sc_core::sc_out< bool > M01_AXI_wlast;
  sc_core::sc_out< bool > M01_AXI_wvalid;
  sc_core::sc_in< bool > M01_AXI_wready;
  sc_core::sc_in< sc_dt::sc_bv<2> > M01_AXI_bresp;
  sc_core::sc_in< bool > M01_AXI_bvalid;
  sc_core::sc_out< bool > M01_AXI_bready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M01_AXI_araddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M01_AXI_arlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_arsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M01_AXI_arburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M01_AXI_arlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_arcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_arprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_arqos;
  sc_core::sc_out< bool > M01_AXI_arvalid;
  sc_core::sc_in< bool > M01_AXI_arready;
  sc_core::sc_in< sc_dt::sc_bv<512> > M01_AXI_rdata;
  sc_core::sc_in< sc_dt::sc_bv<2> > M01_AXI_rresp;
  sc_core::sc_in< bool > M01_AXI_rlast;
  sc_core::sc_in< bool > M01_AXI_rvalid;
  sc_core::sc_out< bool > M01_AXI_rready;

  // Dummy Signals for IP Ports


protected:

  virtual void before_end_of_elaboration();

private:

  xtlm::xaximm_pin2xtlm_t<512,64,16,1,1,1,1,1>* mp_S00_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_S00_AXI_awlock_converter;
  sc_signal< bool > m_S00_AXI_awlock_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_S00_AXI_arlock_converter;
  sc_signal< bool > m_S00_AXI_arlock_converter_signal;
  xtlm::xaximm_pin2xtlm_t<512,64,16,1,1,1,1,1>* mp_S01_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_S01_AXI_awlock_converter;
  sc_signal< bool > m_S01_AXI_awlock_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_S01_AXI_arlock_converter;
  sc_signal< bool > m_S01_AXI_arlock_converter_signal;
  xtlm::xaximm_xtlm2pin_t<512,64,1,1,1,1,1,1>* mp_M00_AXI_transactor;
  xsc::common::scalar2vectorN_converter<1>* mp_M00_AXI_awlock_converter;
  sc_signal< bool > m_M00_AXI_awlock_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_M00_AXI_arlock_converter;
  sc_signal< bool > m_M00_AXI_arlock_converter_signal;
  xtlm::xaximm_xtlm2pin_t<512,64,1,1,1,1,1,1>* mp_M01_AXI_transactor;
  xsc::common::scalar2vectorN_converter<1>* mp_M01_AXI_awlock_converter;
  sc_signal< bool > m_M01_AXI_awlock_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_M01_AXI_arlock_converter;
  sc_signal< bool > m_M01_AXI_arlock_converter_signal;

  // Transactor stubs
  xtlm::xtlm_aximm_initiator_stub * M00_AXI_transactor_initiator_rd_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M00_AXI_transactor_initiator_wr_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M01_AXI_transactor_initiator_rd_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M01_AXI_transactor_initiator_wr_socket_stub;
  xtlm::xtlm_aximm_target_stub * S00_AXI_transactor_target_rd_socket_stub;
  xtlm::xtlm_aximm_target_stub * S00_AXI_transactor_target_wr_socket_stub;
  xtlm::xtlm_aximm_target_stub * S01_AXI_transactor_target_rd_socket_stub;
  xtlm::xtlm_aximm_target_stub * S01_AXI_transactor_target_wr_socket_stub;

  // Socket stubs

};
#endif // VCSSYSTEMC




#ifdef MTI_SYSTEMC
#include "utils/xtlm_aximm_initiator_stub.h"

#include "utils/xtlm_aximm_target_stub.h"

class DllExport cl_axi_sc_2x2_smartconnect_0_0 : public cl_axi_sc_2x2_smartconnect_0_0_sc
{
public:

  cl_axi_sc_2x2_smartconnect_0_0(const sc_core::sc_module_name& nm);
  virtual ~cl_axi_sc_2x2_smartconnect_0_0();

  // module pin-to-pin RTL interface

  sc_core::sc_in< bool > aclk;
  sc_core::sc_in< bool > aresetn;
  sc_core::sc_in< sc_dt::sc_bv<16> > S00_AXI_awid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S00_AXI_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S00_AXI_awlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_awsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S00_AXI_awburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S00_AXI_awlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_awcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_awprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_awqos;
  sc_core::sc_in< bool > S00_AXI_awvalid;
  sc_core::sc_out< bool > S00_AXI_awready;
  sc_core::sc_in< sc_dt::sc_bv<512> > S00_AXI_wdata;
  sc_core::sc_in< sc_dt::sc_bv<64> > S00_AXI_wstrb;
  sc_core::sc_in< bool > S00_AXI_wlast;
  sc_core::sc_in< bool > S00_AXI_wvalid;
  sc_core::sc_out< bool > S00_AXI_wready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S00_AXI_bid;
  sc_core::sc_out< sc_dt::sc_bv<2> > S00_AXI_bresp;
  sc_core::sc_out< bool > S00_AXI_bvalid;
  sc_core::sc_in< bool > S00_AXI_bready;
  sc_core::sc_in< sc_dt::sc_bv<16> > S00_AXI_arid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S00_AXI_araddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S00_AXI_arlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_arsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S00_AXI_arburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S00_AXI_arlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_arcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S00_AXI_arprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S00_AXI_arqos;
  sc_core::sc_in< bool > S00_AXI_arvalid;
  sc_core::sc_out< bool > S00_AXI_arready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S00_AXI_rid;
  sc_core::sc_out< sc_dt::sc_bv<512> > S00_AXI_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > S00_AXI_rresp;
  sc_core::sc_out< bool > S00_AXI_rlast;
  sc_core::sc_out< bool > S00_AXI_rvalid;
  sc_core::sc_in< bool > S00_AXI_rready;
  sc_core::sc_in< sc_dt::sc_bv<16> > S01_AXI_awid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S01_AXI_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S01_AXI_awlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_awsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S01_AXI_awburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S01_AXI_awlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_awcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_awprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_awqos;
  sc_core::sc_in< bool > S01_AXI_awvalid;
  sc_core::sc_out< bool > S01_AXI_awready;
  sc_core::sc_in< sc_dt::sc_bv<512> > S01_AXI_wdata;
  sc_core::sc_in< sc_dt::sc_bv<64> > S01_AXI_wstrb;
  sc_core::sc_in< bool > S01_AXI_wlast;
  sc_core::sc_in< bool > S01_AXI_wvalid;
  sc_core::sc_out< bool > S01_AXI_wready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S01_AXI_bid;
  sc_core::sc_out< sc_dt::sc_bv<2> > S01_AXI_bresp;
  sc_core::sc_out< bool > S01_AXI_bvalid;
  sc_core::sc_in< bool > S01_AXI_bready;
  sc_core::sc_in< sc_dt::sc_bv<16> > S01_AXI_arid;
  sc_core::sc_in< sc_dt::sc_bv<64> > S01_AXI_araddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > S01_AXI_arlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_arsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > S01_AXI_arburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > S01_AXI_arlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_arcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > S01_AXI_arprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > S01_AXI_arqos;
  sc_core::sc_in< bool > S01_AXI_arvalid;
  sc_core::sc_out< bool > S01_AXI_arready;
  sc_core::sc_out< sc_dt::sc_bv<16> > S01_AXI_rid;
  sc_core::sc_out< sc_dt::sc_bv<512> > S01_AXI_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > S01_AXI_rresp;
  sc_core::sc_out< bool > S01_AXI_rlast;
  sc_core::sc_out< bool > S01_AXI_rvalid;
  sc_core::sc_in< bool > S01_AXI_rready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M00_AXI_awaddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M00_AXI_awlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_awsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M00_AXI_awburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M00_AXI_awlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_awcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_awprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_awqos;
  sc_core::sc_out< bool > M00_AXI_awvalid;
  sc_core::sc_in< bool > M00_AXI_awready;
  sc_core::sc_out< sc_dt::sc_bv<512> > M00_AXI_wdata;
  sc_core::sc_out< sc_dt::sc_bv<64> > M00_AXI_wstrb;
  sc_core::sc_out< bool > M00_AXI_wlast;
  sc_core::sc_out< bool > M00_AXI_wvalid;
  sc_core::sc_in< bool > M00_AXI_wready;
  sc_core::sc_in< sc_dt::sc_bv<2> > M00_AXI_bresp;
  sc_core::sc_in< bool > M00_AXI_bvalid;
  sc_core::sc_out< bool > M00_AXI_bready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M00_AXI_araddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M00_AXI_arlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_arsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M00_AXI_arburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M00_AXI_arlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_arcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M00_AXI_arprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M00_AXI_arqos;
  sc_core::sc_out< bool > M00_AXI_arvalid;
  sc_core::sc_in< bool > M00_AXI_arready;
  sc_core::sc_in< sc_dt::sc_bv<512> > M00_AXI_rdata;
  sc_core::sc_in< sc_dt::sc_bv<2> > M00_AXI_rresp;
  sc_core::sc_in< bool > M00_AXI_rlast;
  sc_core::sc_in< bool > M00_AXI_rvalid;
  sc_core::sc_out< bool > M00_AXI_rready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M01_AXI_awaddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M01_AXI_awlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_awsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M01_AXI_awburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M01_AXI_awlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_awcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_awprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_awqos;
  sc_core::sc_out< bool > M01_AXI_awvalid;
  sc_core::sc_in< bool > M01_AXI_awready;
  sc_core::sc_out< sc_dt::sc_bv<512> > M01_AXI_wdata;
  sc_core::sc_out< sc_dt::sc_bv<64> > M01_AXI_wstrb;
  sc_core::sc_out< bool > M01_AXI_wlast;
  sc_core::sc_out< bool > M01_AXI_wvalid;
  sc_core::sc_in< bool > M01_AXI_wready;
  sc_core::sc_in< sc_dt::sc_bv<2> > M01_AXI_bresp;
  sc_core::sc_in< bool > M01_AXI_bvalid;
  sc_core::sc_out< bool > M01_AXI_bready;
  sc_core::sc_out< sc_dt::sc_bv<64> > M01_AXI_araddr;
  sc_core::sc_out< sc_dt::sc_bv<8> > M01_AXI_arlen;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_arsize;
  sc_core::sc_out< sc_dt::sc_bv<2> > M01_AXI_arburst;
  sc_core::sc_out< sc_dt::sc_bv<1> > M01_AXI_arlock;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_arcache;
  sc_core::sc_out< sc_dt::sc_bv<3> > M01_AXI_arprot;
  sc_core::sc_out< sc_dt::sc_bv<4> > M01_AXI_arqos;
  sc_core::sc_out< bool > M01_AXI_arvalid;
  sc_core::sc_in< bool > M01_AXI_arready;
  sc_core::sc_in< sc_dt::sc_bv<512> > M01_AXI_rdata;
  sc_core::sc_in< sc_dt::sc_bv<2> > M01_AXI_rresp;
  sc_core::sc_in< bool > M01_AXI_rlast;
  sc_core::sc_in< bool > M01_AXI_rvalid;
  sc_core::sc_out< bool > M01_AXI_rready;

  // Dummy Signals for IP Ports


protected:

  virtual void before_end_of_elaboration();

private:

  xtlm::xaximm_pin2xtlm_t<512,64,16,1,1,1,1,1>* mp_S00_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_S00_AXI_awlock_converter;
  sc_signal< bool > m_S00_AXI_awlock_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_S00_AXI_arlock_converter;
  sc_signal< bool > m_S00_AXI_arlock_converter_signal;
  xtlm::xaximm_pin2xtlm_t<512,64,16,1,1,1,1,1>* mp_S01_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_S01_AXI_awlock_converter;
  sc_signal< bool > m_S01_AXI_awlock_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_S01_AXI_arlock_converter;
  sc_signal< bool > m_S01_AXI_arlock_converter_signal;
  xtlm::xaximm_xtlm2pin_t<512,64,1,1,1,1,1,1>* mp_M00_AXI_transactor;
  xsc::common::scalar2vectorN_converter<1>* mp_M00_AXI_awlock_converter;
  sc_signal< bool > m_M00_AXI_awlock_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_M00_AXI_arlock_converter;
  sc_signal< bool > m_M00_AXI_arlock_converter_signal;
  xtlm::xaximm_xtlm2pin_t<512,64,1,1,1,1,1,1>* mp_M01_AXI_transactor;
  xsc::common::scalar2vectorN_converter<1>* mp_M01_AXI_awlock_converter;
  sc_signal< bool > m_M01_AXI_awlock_converter_signal;
  xsc::common::scalar2vectorN_converter<1>* mp_M01_AXI_arlock_converter;
  sc_signal< bool > m_M01_AXI_arlock_converter_signal;

  // Transactor stubs
  xtlm::xtlm_aximm_initiator_stub * M00_AXI_transactor_initiator_rd_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M00_AXI_transactor_initiator_wr_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M01_AXI_transactor_initiator_rd_socket_stub;
  xtlm::xtlm_aximm_initiator_stub * M01_AXI_transactor_initiator_wr_socket_stub;
  xtlm::xtlm_aximm_target_stub * S00_AXI_transactor_target_rd_socket_stub;
  xtlm::xtlm_aximm_target_stub * S00_AXI_transactor_target_wr_socket_stub;
  xtlm::xtlm_aximm_target_stub * S01_AXI_transactor_target_rd_socket_stub;
  xtlm::xtlm_aximm_target_stub * S01_AXI_transactor_target_wr_socket_stub;

  // Socket stubs

};
#endif // MTI_SYSTEMC
#endif // IP_CL_AXI_SC_2X2_SMARTCONNECT_0_0_H_
