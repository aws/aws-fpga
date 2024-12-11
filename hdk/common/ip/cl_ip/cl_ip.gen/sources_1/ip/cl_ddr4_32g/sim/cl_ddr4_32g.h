#ifndef IP_CL_DDR4_32G_H_
#define IP_CL_DDR4_32G_H_

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

#include "cl_ddr4_32g_sc.h"




#ifdef XILINX_SIMULATOR
class DllExport cl_ddr4_32g : public cl_ddr4_32g_sc
{
public:

  cl_ddr4_32g(const sc_core::sc_module_name& nm);
  virtual ~cl_ddr4_32g();

  // module pin-to-pin RTL interface

  sc_core::sc_out< bool > c0_init_calib_complete;
  sc_core::sc_out< bool > dbg_clk;
  sc_core::sc_in< bool > c0_sys_clk_p;
  sc_core::sc_in< bool > c0_sys_clk_n;
  sc_core::sc_out< sc_dt::sc_bv<512> > dbg_bus;
  sc_core::sc_out< sc_dt::sc_bv<17> > c0_ddr4_adr;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_ba;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_cke;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_cs_n;
  sc_core::sc_out< sc_dt::sc_bv<72> > c0_ddr4_dq;
  sc_core::sc_out< sc_dt::sc_bv<18> > c0_ddr4_dqs_c;
  sc_core::sc_out< sc_dt::sc_bv<18> > c0_ddr4_dqs_t;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_odt;
  sc_core::sc_out< bool > c0_ddr4_parity;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_bg;
  sc_core::sc_out< bool > c0_ddr4_reset_n;
  sc_core::sc_out< bool > c0_ddr4_act_n;
  sc_core::sc_out< sc_dt::sc_bv<1> > c0_ddr4_ck_c;
  sc_core::sc_out< sc_dt::sc_bv<1> > c0_ddr4_ck_t;
  sc_core::sc_out< bool > c0_ddr4_ui_clk;
  sc_core::sc_out< bool > c0_ddr4_ui_clk_sync_rst;
  sc_core::sc_in< bool > c0_ddr4_app_sref_req;
  sc_core::sc_out< bool > c0_ddr4_app_sref_ack;
  sc_core::sc_in< bool > c0_ddr4_app_restore_en;
  sc_core::sc_in< bool > c0_ddr4_app_restore_complete;
  sc_core::sc_in< bool > c0_ddr4_app_mem_init_skip;
  sc_core::sc_in< bool > c0_ddr4_app_xsdb_select;
  sc_core::sc_in< bool > c0_ddr4_app_xsdb_rd_en;
  sc_core::sc_in< bool > c0_ddr4_app_xsdb_wr_en;
  sc_core::sc_in< sc_dt::sc_bv<16> > c0_ddr4_app_xsdb_addr;
  sc_core::sc_in< sc_dt::sc_bv<9> > c0_ddr4_app_xsdb_wr_data;
  sc_core::sc_out< sc_dt::sc_bv<9> > c0_ddr4_app_xsdb_rd_data;
  sc_core::sc_out< bool > c0_ddr4_app_xsdb_rdy;
  sc_core::sc_out< sc_dt::sc_bv<32> > c0_ddr4_app_dbg_out;
  sc_core::sc_in< bool > c0_ddr4_aresetn;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_awvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_awready;
  sc_core::sc_in< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_awaddr;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_wvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_wready;
  sc_core::sc_in< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_wdata;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_bvalid;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_bready;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_ctrl_bresp;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_arvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_arready;
  sc_core::sc_in< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_araddr;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_rvalid;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_rready;
  sc_core::sc_out< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_ctrl_rresp;
  sc_core::sc_out< bool > c0_ddr4_interrupt;
  sc_core::sc_in< sc_dt::sc_bv<16> > c0_ddr4_s_axi_awid;
  sc_core::sc_in< sc_dt::sc_bv<35> > c0_ddr4_s_axi_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > c0_ddr4_s_axi_awlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_awsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > c0_ddr4_s_axi_awburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > c0_ddr4_s_axi_awlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_awcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_awprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_awqos;
  sc_core::sc_in< bool > c0_ddr4_s_axi_awvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_awready;
  sc_core::sc_in< sc_dt::sc_bv<512> > c0_ddr4_s_axi_wdata;
  sc_core::sc_in< sc_dt::sc_bv<64> > c0_ddr4_s_axi_wstrb;
  sc_core::sc_in< bool > c0_ddr4_s_axi_wlast;
  sc_core::sc_in< bool > c0_ddr4_s_axi_wvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_wready;
  sc_core::sc_in< bool > c0_ddr4_s_axi_bready;
  sc_core::sc_out< sc_dt::sc_bv<16> > c0_ddr4_s_axi_bid;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_bresp;
  sc_core::sc_out< bool > c0_ddr4_s_axi_bvalid;
  sc_core::sc_in< sc_dt::sc_bv<16> > c0_ddr4_s_axi_arid;
  sc_core::sc_in< sc_dt::sc_bv<35> > c0_ddr4_s_axi_araddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > c0_ddr4_s_axi_arlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_arsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > c0_ddr4_s_axi_arburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > c0_ddr4_s_axi_arlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_arcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_arprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_arqos;
  sc_core::sc_in< bool > c0_ddr4_s_axi_arvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_arready;
  sc_core::sc_in< bool > c0_ddr4_s_axi_rready;
  sc_core::sc_out< bool > c0_ddr4_s_axi_rlast;
  sc_core::sc_out< bool > c0_ddr4_s_axi_rvalid;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_rresp;
  sc_core::sc_out< sc_dt::sc_bv<16> > c0_ddr4_s_axi_rid;
  sc_core::sc_out< sc_dt::sc_bv<512> > c0_ddr4_s_axi_rdata;
  sc_core::sc_in< bool > sys_rst;

  // Dummy Signals for IP Ports


protected:

  virtual void before_end_of_elaboration();

private:

  xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>* mp_C0_DDR4_S_AXI_CTRL_transactor;
  xtlm::xaximm_pin2xtlm_t<512,35,16,1,1,1,1,1>* mp_C0_DDR4_S_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_c0_ddr4_s_axi_arlock_converter;
  sc_signal< bool > m_c0_ddr4_s_axi_arlock_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_c0_ddr4_s_axi_awlock_converter;
  sc_signal< bool > m_c0_ddr4_s_axi_awlock_converter_signal;

};
#endif // XILINX_SIMULATOR




#ifdef XM_SYSTEMC
class DllExport cl_ddr4_32g : public cl_ddr4_32g_sc
{
public:

  cl_ddr4_32g(const sc_core::sc_module_name& nm);
  virtual ~cl_ddr4_32g();

  // module pin-to-pin RTL interface

  sc_core::sc_out< bool > c0_init_calib_complete;
  sc_core::sc_out< bool > dbg_clk;
  sc_core::sc_in< bool > c0_sys_clk_p;
  sc_core::sc_in< bool > c0_sys_clk_n;
  sc_core::sc_out< sc_dt::sc_bv<512> > dbg_bus;
  sc_core::sc_out< sc_dt::sc_bv<17> > c0_ddr4_adr;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_ba;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_cke;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_cs_n;
  sc_core::sc_inout< sc_dt::sc_bv<72> > c0_ddr4_dq;
  sc_core::sc_inout< sc_dt::sc_bv<18> > c0_ddr4_dqs_c;
  sc_core::sc_inout< sc_dt::sc_bv<18> > c0_ddr4_dqs_t;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_odt;
  sc_core::sc_out< bool > c0_ddr4_parity;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_bg;
  sc_core::sc_out< bool > c0_ddr4_reset_n;
  sc_core::sc_out< bool > c0_ddr4_act_n;
  sc_core::sc_out< sc_dt::sc_bv<1> > c0_ddr4_ck_c;
  sc_core::sc_out< sc_dt::sc_bv<1> > c0_ddr4_ck_t;
  sc_core::sc_out< bool > c0_ddr4_ui_clk;
  sc_core::sc_out< bool > c0_ddr4_ui_clk_sync_rst;
  sc_core::sc_in< bool > c0_ddr4_app_sref_req;
  sc_core::sc_out< bool > c0_ddr4_app_sref_ack;
  sc_core::sc_in< bool > c0_ddr4_app_restore_en;
  sc_core::sc_in< bool > c0_ddr4_app_restore_complete;
  sc_core::sc_in< bool > c0_ddr4_app_mem_init_skip;
  sc_core::sc_in< bool > c0_ddr4_app_xsdb_select;
  sc_core::sc_in< bool > c0_ddr4_app_xsdb_rd_en;
  sc_core::sc_in< bool > c0_ddr4_app_xsdb_wr_en;
  sc_core::sc_in< sc_dt::sc_bv<16> > c0_ddr4_app_xsdb_addr;
  sc_core::sc_in< sc_dt::sc_bv<9> > c0_ddr4_app_xsdb_wr_data;
  sc_core::sc_out< sc_dt::sc_bv<9> > c0_ddr4_app_xsdb_rd_data;
  sc_core::sc_out< bool > c0_ddr4_app_xsdb_rdy;
  sc_core::sc_out< sc_dt::sc_bv<32> > c0_ddr4_app_dbg_out;
  sc_core::sc_in< bool > c0_ddr4_aresetn;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_awvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_awready;
  sc_core::sc_in< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_awaddr;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_wvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_wready;
  sc_core::sc_in< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_wdata;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_bvalid;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_bready;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_ctrl_bresp;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_arvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_arready;
  sc_core::sc_in< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_araddr;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_rvalid;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_rready;
  sc_core::sc_out< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_ctrl_rresp;
  sc_core::sc_out< bool > c0_ddr4_interrupt;
  sc_core::sc_in< sc_dt::sc_bv<16> > c0_ddr4_s_axi_awid;
  sc_core::sc_in< sc_dt::sc_bv<35> > c0_ddr4_s_axi_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > c0_ddr4_s_axi_awlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_awsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > c0_ddr4_s_axi_awburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > c0_ddr4_s_axi_awlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_awcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_awprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_awqos;
  sc_core::sc_in< bool > c0_ddr4_s_axi_awvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_awready;
  sc_core::sc_in< sc_dt::sc_bv<512> > c0_ddr4_s_axi_wdata;
  sc_core::sc_in< sc_dt::sc_bv<64> > c0_ddr4_s_axi_wstrb;
  sc_core::sc_in< bool > c0_ddr4_s_axi_wlast;
  sc_core::sc_in< bool > c0_ddr4_s_axi_wvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_wready;
  sc_core::sc_in< bool > c0_ddr4_s_axi_bready;
  sc_core::sc_out< sc_dt::sc_bv<16> > c0_ddr4_s_axi_bid;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_bresp;
  sc_core::sc_out< bool > c0_ddr4_s_axi_bvalid;
  sc_core::sc_in< sc_dt::sc_bv<16> > c0_ddr4_s_axi_arid;
  sc_core::sc_in< sc_dt::sc_bv<35> > c0_ddr4_s_axi_araddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > c0_ddr4_s_axi_arlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_arsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > c0_ddr4_s_axi_arburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > c0_ddr4_s_axi_arlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_arcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_arprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_arqos;
  sc_core::sc_in< bool > c0_ddr4_s_axi_arvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_arready;
  sc_core::sc_in< bool > c0_ddr4_s_axi_rready;
  sc_core::sc_out< bool > c0_ddr4_s_axi_rlast;
  sc_core::sc_out< bool > c0_ddr4_s_axi_rvalid;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_rresp;
  sc_core::sc_out< sc_dt::sc_bv<16> > c0_ddr4_s_axi_rid;
  sc_core::sc_out< sc_dt::sc_bv<512> > c0_ddr4_s_axi_rdata;
  sc_core::sc_in< bool > sys_rst;

  // Dummy Signals for IP Ports


protected:

  virtual void before_end_of_elaboration();

private:

  xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>* mp_C0_DDR4_S_AXI_CTRL_transactor;
  xtlm::xaximm_pin2xtlm_t<512,35,16,1,1,1,1,1>* mp_C0_DDR4_S_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_c0_ddr4_s_axi_arlock_converter;
  sc_signal< bool > m_c0_ddr4_s_axi_arlock_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_c0_ddr4_s_axi_awlock_converter;
  sc_signal< bool > m_c0_ddr4_s_axi_awlock_converter_signal;

};
#endif // XM_SYSTEMC




#ifdef RIVIERA
class DllExport cl_ddr4_32g : public cl_ddr4_32g_sc
{
public:

  cl_ddr4_32g(const sc_core::sc_module_name& nm);
  virtual ~cl_ddr4_32g();

  // module pin-to-pin RTL interface

  sc_core::sc_out< bool > c0_init_calib_complete;
  sc_core::sc_out< bool > dbg_clk;
  sc_core::sc_in< bool > c0_sys_clk_p;
  sc_core::sc_in< bool > c0_sys_clk_n;
  sc_core::sc_out< sc_dt::sc_bv<512> > dbg_bus;
  sc_core::sc_out< sc_dt::sc_bv<17> > c0_ddr4_adr;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_ba;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_cke;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_cs_n;
  sc_core::sc_out< sc_dt::sc_bv<72> > c0_ddr4_dq;
  sc_core::sc_out< sc_dt::sc_bv<18> > c0_ddr4_dqs_c;
  sc_core::sc_out< sc_dt::sc_bv<18> > c0_ddr4_dqs_t;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_odt;
  sc_core::sc_out< bool > c0_ddr4_parity;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_bg;
  sc_core::sc_out< bool > c0_ddr4_reset_n;
  sc_core::sc_out< bool > c0_ddr4_act_n;
  sc_core::sc_out< sc_dt::sc_bv<1> > c0_ddr4_ck_c;
  sc_core::sc_out< sc_dt::sc_bv<1> > c0_ddr4_ck_t;
  sc_core::sc_out< bool > c0_ddr4_ui_clk;
  sc_core::sc_out< bool > c0_ddr4_ui_clk_sync_rst;
  sc_core::sc_in< bool > c0_ddr4_app_sref_req;
  sc_core::sc_out< bool > c0_ddr4_app_sref_ack;
  sc_core::sc_in< bool > c0_ddr4_app_restore_en;
  sc_core::sc_in< bool > c0_ddr4_app_restore_complete;
  sc_core::sc_in< bool > c0_ddr4_app_mem_init_skip;
  sc_core::sc_in< bool > c0_ddr4_app_xsdb_select;
  sc_core::sc_in< bool > c0_ddr4_app_xsdb_rd_en;
  sc_core::sc_in< bool > c0_ddr4_app_xsdb_wr_en;
  sc_core::sc_in< sc_dt::sc_bv<16> > c0_ddr4_app_xsdb_addr;
  sc_core::sc_in< sc_dt::sc_bv<9> > c0_ddr4_app_xsdb_wr_data;
  sc_core::sc_out< sc_dt::sc_bv<9> > c0_ddr4_app_xsdb_rd_data;
  sc_core::sc_out< bool > c0_ddr4_app_xsdb_rdy;
  sc_core::sc_out< sc_dt::sc_bv<32> > c0_ddr4_app_dbg_out;
  sc_core::sc_in< bool > c0_ddr4_aresetn;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_awvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_awready;
  sc_core::sc_in< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_awaddr;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_wvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_wready;
  sc_core::sc_in< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_wdata;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_bvalid;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_bready;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_ctrl_bresp;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_arvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_arready;
  sc_core::sc_in< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_araddr;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_rvalid;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_rready;
  sc_core::sc_out< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_ctrl_rresp;
  sc_core::sc_out< bool > c0_ddr4_interrupt;
  sc_core::sc_in< sc_dt::sc_bv<16> > c0_ddr4_s_axi_awid;
  sc_core::sc_in< sc_dt::sc_bv<35> > c0_ddr4_s_axi_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > c0_ddr4_s_axi_awlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_awsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > c0_ddr4_s_axi_awburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > c0_ddr4_s_axi_awlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_awcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_awprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_awqos;
  sc_core::sc_in< bool > c0_ddr4_s_axi_awvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_awready;
  sc_core::sc_in< sc_dt::sc_bv<512> > c0_ddr4_s_axi_wdata;
  sc_core::sc_in< sc_dt::sc_bv<64> > c0_ddr4_s_axi_wstrb;
  sc_core::sc_in< bool > c0_ddr4_s_axi_wlast;
  sc_core::sc_in< bool > c0_ddr4_s_axi_wvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_wready;
  sc_core::sc_in< bool > c0_ddr4_s_axi_bready;
  sc_core::sc_out< sc_dt::sc_bv<16> > c0_ddr4_s_axi_bid;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_bresp;
  sc_core::sc_out< bool > c0_ddr4_s_axi_bvalid;
  sc_core::sc_in< sc_dt::sc_bv<16> > c0_ddr4_s_axi_arid;
  sc_core::sc_in< sc_dt::sc_bv<35> > c0_ddr4_s_axi_araddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > c0_ddr4_s_axi_arlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_arsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > c0_ddr4_s_axi_arburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > c0_ddr4_s_axi_arlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_arcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_arprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_arqos;
  sc_core::sc_in< bool > c0_ddr4_s_axi_arvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_arready;
  sc_core::sc_in< bool > c0_ddr4_s_axi_rready;
  sc_core::sc_out< bool > c0_ddr4_s_axi_rlast;
  sc_core::sc_out< bool > c0_ddr4_s_axi_rvalid;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_rresp;
  sc_core::sc_out< sc_dt::sc_bv<16> > c0_ddr4_s_axi_rid;
  sc_core::sc_out< sc_dt::sc_bv<512> > c0_ddr4_s_axi_rdata;
  sc_core::sc_in< bool > sys_rst;

  // Dummy Signals for IP Ports


protected:

  virtual void before_end_of_elaboration();

private:

  xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>* mp_C0_DDR4_S_AXI_CTRL_transactor;
  xtlm::xaximm_pin2xtlm_t<512,35,16,1,1,1,1,1>* mp_C0_DDR4_S_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_c0_ddr4_s_axi_arlock_converter;
  sc_signal< bool > m_c0_ddr4_s_axi_arlock_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_c0_ddr4_s_axi_awlock_converter;
  sc_signal< bool > m_c0_ddr4_s_axi_awlock_converter_signal;

};
#endif // RIVIERA




#ifdef VCSSYSTEMC
#include "utils/xtlm_aximm_target_stub.h"

class DllExport cl_ddr4_32g : public cl_ddr4_32g_sc
{
public:

  cl_ddr4_32g(const sc_core::sc_module_name& nm);
  virtual ~cl_ddr4_32g();

  // module pin-to-pin RTL interface

  sc_core::sc_out< bool > c0_init_calib_complete;
  sc_core::sc_out< bool > dbg_clk;
  sc_core::sc_in< bool > c0_sys_clk_p;
  sc_core::sc_in< bool > c0_sys_clk_n;
  sc_core::sc_out< sc_dt::sc_bv<512> > dbg_bus;
  sc_core::sc_out< sc_dt::sc_bv<17> > c0_ddr4_adr;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_ba;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_cke;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_cs_n;
  sc_core::sc_out< sc_dt::sc_bv<72> > c0_ddr4_dq;
  sc_core::sc_out< sc_dt::sc_bv<18> > c0_ddr4_dqs_c;
  sc_core::sc_out< sc_dt::sc_bv<18> > c0_ddr4_dqs_t;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_odt;
  sc_core::sc_out< bool > c0_ddr4_parity;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_bg;
  sc_core::sc_out< bool > c0_ddr4_reset_n;
  sc_core::sc_out< bool > c0_ddr4_act_n;
  sc_core::sc_out< sc_dt::sc_bv<1> > c0_ddr4_ck_c;
  sc_core::sc_out< sc_dt::sc_bv<1> > c0_ddr4_ck_t;
  sc_core::sc_out< bool > c0_ddr4_ui_clk;
  sc_core::sc_out< bool > c0_ddr4_ui_clk_sync_rst;
  sc_core::sc_in< bool > c0_ddr4_app_sref_req;
  sc_core::sc_out< bool > c0_ddr4_app_sref_ack;
  sc_core::sc_in< bool > c0_ddr4_app_restore_en;
  sc_core::sc_in< bool > c0_ddr4_app_restore_complete;
  sc_core::sc_in< bool > c0_ddr4_app_mem_init_skip;
  sc_core::sc_in< bool > c0_ddr4_app_xsdb_select;
  sc_core::sc_in< bool > c0_ddr4_app_xsdb_rd_en;
  sc_core::sc_in< bool > c0_ddr4_app_xsdb_wr_en;
  sc_core::sc_in< sc_dt::sc_bv<16> > c0_ddr4_app_xsdb_addr;
  sc_core::sc_in< sc_dt::sc_bv<9> > c0_ddr4_app_xsdb_wr_data;
  sc_core::sc_out< sc_dt::sc_bv<9> > c0_ddr4_app_xsdb_rd_data;
  sc_core::sc_out< bool > c0_ddr4_app_xsdb_rdy;
  sc_core::sc_out< sc_dt::sc_bv<32> > c0_ddr4_app_dbg_out;
  sc_core::sc_in< bool > c0_ddr4_aresetn;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_awvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_awready;
  sc_core::sc_in< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_awaddr;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_wvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_wready;
  sc_core::sc_in< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_wdata;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_bvalid;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_bready;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_ctrl_bresp;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_arvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_arready;
  sc_core::sc_in< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_araddr;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_rvalid;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_rready;
  sc_core::sc_out< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_ctrl_rresp;
  sc_core::sc_out< bool > c0_ddr4_interrupt;
  sc_core::sc_in< sc_dt::sc_bv<16> > c0_ddr4_s_axi_awid;
  sc_core::sc_in< sc_dt::sc_bv<35> > c0_ddr4_s_axi_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > c0_ddr4_s_axi_awlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_awsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > c0_ddr4_s_axi_awburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > c0_ddr4_s_axi_awlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_awcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_awprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_awqos;
  sc_core::sc_in< bool > c0_ddr4_s_axi_awvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_awready;
  sc_core::sc_in< sc_dt::sc_bv<512> > c0_ddr4_s_axi_wdata;
  sc_core::sc_in< sc_dt::sc_bv<64> > c0_ddr4_s_axi_wstrb;
  sc_core::sc_in< bool > c0_ddr4_s_axi_wlast;
  sc_core::sc_in< bool > c0_ddr4_s_axi_wvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_wready;
  sc_core::sc_in< bool > c0_ddr4_s_axi_bready;
  sc_core::sc_out< sc_dt::sc_bv<16> > c0_ddr4_s_axi_bid;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_bresp;
  sc_core::sc_out< bool > c0_ddr4_s_axi_bvalid;
  sc_core::sc_in< sc_dt::sc_bv<16> > c0_ddr4_s_axi_arid;
  sc_core::sc_in< sc_dt::sc_bv<35> > c0_ddr4_s_axi_araddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > c0_ddr4_s_axi_arlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_arsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > c0_ddr4_s_axi_arburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > c0_ddr4_s_axi_arlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_arcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_arprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_arqos;
  sc_core::sc_in< bool > c0_ddr4_s_axi_arvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_arready;
  sc_core::sc_in< bool > c0_ddr4_s_axi_rready;
  sc_core::sc_out< bool > c0_ddr4_s_axi_rlast;
  sc_core::sc_out< bool > c0_ddr4_s_axi_rvalid;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_rresp;
  sc_core::sc_out< sc_dt::sc_bv<16> > c0_ddr4_s_axi_rid;
  sc_core::sc_out< sc_dt::sc_bv<512> > c0_ddr4_s_axi_rdata;
  sc_core::sc_in< bool > sys_rst;

  // Dummy Signals for IP Ports


protected:

  virtual void before_end_of_elaboration();

private:

  xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>* mp_C0_DDR4_S_AXI_CTRL_transactor;
  xtlm::xaximm_pin2xtlm_t<512,35,16,1,1,1,1,1>* mp_C0_DDR4_S_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_c0_ddr4_s_axi_arlock_converter;
  sc_signal< bool > m_c0_ddr4_s_axi_arlock_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_c0_ddr4_s_axi_awlock_converter;
  sc_signal< bool > m_c0_ddr4_s_axi_awlock_converter_signal;

  // Transactor stubs
  xtlm::xtlm_aximm_target_stub * C0_DDR4_S_AXI_CTRL_transactor_target_rd_socket_stub;
  xtlm::xtlm_aximm_target_stub * C0_DDR4_S_AXI_CTRL_transactor_target_wr_socket_stub;
  xtlm::xtlm_aximm_target_stub * C0_DDR4_S_AXI_transactor_target_rd_socket_stub;
  xtlm::xtlm_aximm_target_stub * C0_DDR4_S_AXI_transactor_target_wr_socket_stub;

  // Socket stubs

};
#endif // VCSSYSTEMC




#ifdef MTI_SYSTEMC
#include "utils/xtlm_aximm_target_stub.h"

class DllExport cl_ddr4_32g : public cl_ddr4_32g_sc
{
public:

  cl_ddr4_32g(const sc_core::sc_module_name& nm);
  virtual ~cl_ddr4_32g();

  // module pin-to-pin RTL interface

  sc_core::sc_out< bool > c0_init_calib_complete;
  sc_core::sc_out< bool > dbg_clk;
  sc_core::sc_in< bool > c0_sys_clk_p;
  sc_core::sc_in< bool > c0_sys_clk_n;
  sc_core::sc_out< sc_dt::sc_bv<512> > dbg_bus;
  sc_core::sc_out< sc_dt::sc_bv<17> > c0_ddr4_adr;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_ba;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_cke;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_cs_n;
  sc_core::sc_out< sc_dt::sc_bv<72> > c0_ddr4_dq;
  sc_core::sc_out< sc_dt::sc_bv<18> > c0_ddr4_dqs_c;
  sc_core::sc_out< sc_dt::sc_bv<18> > c0_ddr4_dqs_t;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_odt;
  sc_core::sc_out< bool > c0_ddr4_parity;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_bg;
  sc_core::sc_out< bool > c0_ddr4_reset_n;
  sc_core::sc_out< bool > c0_ddr4_act_n;
  sc_core::sc_out< sc_dt::sc_bv<1> > c0_ddr4_ck_c;
  sc_core::sc_out< sc_dt::sc_bv<1> > c0_ddr4_ck_t;
  sc_core::sc_out< bool > c0_ddr4_ui_clk;
  sc_core::sc_out< bool > c0_ddr4_ui_clk_sync_rst;
  sc_core::sc_in< bool > c0_ddr4_app_sref_req;
  sc_core::sc_out< bool > c0_ddr4_app_sref_ack;
  sc_core::sc_in< bool > c0_ddr4_app_restore_en;
  sc_core::sc_in< bool > c0_ddr4_app_restore_complete;
  sc_core::sc_in< bool > c0_ddr4_app_mem_init_skip;
  sc_core::sc_in< bool > c0_ddr4_app_xsdb_select;
  sc_core::sc_in< bool > c0_ddr4_app_xsdb_rd_en;
  sc_core::sc_in< bool > c0_ddr4_app_xsdb_wr_en;
  sc_core::sc_in< sc_dt::sc_bv<16> > c0_ddr4_app_xsdb_addr;
  sc_core::sc_in< sc_dt::sc_bv<9> > c0_ddr4_app_xsdb_wr_data;
  sc_core::sc_out< sc_dt::sc_bv<9> > c0_ddr4_app_xsdb_rd_data;
  sc_core::sc_out< bool > c0_ddr4_app_xsdb_rdy;
  sc_core::sc_out< sc_dt::sc_bv<32> > c0_ddr4_app_dbg_out;
  sc_core::sc_in< bool > c0_ddr4_aresetn;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_awvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_awready;
  sc_core::sc_in< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_awaddr;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_wvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_wready;
  sc_core::sc_in< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_wdata;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_bvalid;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_bready;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_ctrl_bresp;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_arvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_arready;
  sc_core::sc_in< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_araddr;
  sc_core::sc_out< bool > c0_ddr4_s_axi_ctrl_rvalid;
  sc_core::sc_in< bool > c0_ddr4_s_axi_ctrl_rready;
  sc_core::sc_out< sc_dt::sc_bv<32> > c0_ddr4_s_axi_ctrl_rdata;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_ctrl_rresp;
  sc_core::sc_out< bool > c0_ddr4_interrupt;
  sc_core::sc_in< sc_dt::sc_bv<16> > c0_ddr4_s_axi_awid;
  sc_core::sc_in< sc_dt::sc_bv<35> > c0_ddr4_s_axi_awaddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > c0_ddr4_s_axi_awlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_awsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > c0_ddr4_s_axi_awburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > c0_ddr4_s_axi_awlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_awcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_awprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_awqos;
  sc_core::sc_in< bool > c0_ddr4_s_axi_awvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_awready;
  sc_core::sc_in< sc_dt::sc_bv<512> > c0_ddr4_s_axi_wdata;
  sc_core::sc_in< sc_dt::sc_bv<64> > c0_ddr4_s_axi_wstrb;
  sc_core::sc_in< bool > c0_ddr4_s_axi_wlast;
  sc_core::sc_in< bool > c0_ddr4_s_axi_wvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_wready;
  sc_core::sc_in< bool > c0_ddr4_s_axi_bready;
  sc_core::sc_out< sc_dt::sc_bv<16> > c0_ddr4_s_axi_bid;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_bresp;
  sc_core::sc_out< bool > c0_ddr4_s_axi_bvalid;
  sc_core::sc_in< sc_dt::sc_bv<16> > c0_ddr4_s_axi_arid;
  sc_core::sc_in< sc_dt::sc_bv<35> > c0_ddr4_s_axi_araddr;
  sc_core::sc_in< sc_dt::sc_bv<8> > c0_ddr4_s_axi_arlen;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_arsize;
  sc_core::sc_in< sc_dt::sc_bv<2> > c0_ddr4_s_axi_arburst;
  sc_core::sc_in< sc_dt::sc_bv<1> > c0_ddr4_s_axi_arlock;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_arcache;
  sc_core::sc_in< sc_dt::sc_bv<3> > c0_ddr4_s_axi_arprot;
  sc_core::sc_in< sc_dt::sc_bv<4> > c0_ddr4_s_axi_arqos;
  sc_core::sc_in< bool > c0_ddr4_s_axi_arvalid;
  sc_core::sc_out< bool > c0_ddr4_s_axi_arready;
  sc_core::sc_in< bool > c0_ddr4_s_axi_rready;
  sc_core::sc_out< bool > c0_ddr4_s_axi_rlast;
  sc_core::sc_out< bool > c0_ddr4_s_axi_rvalid;
  sc_core::sc_out< sc_dt::sc_bv<2> > c0_ddr4_s_axi_rresp;
  sc_core::sc_out< sc_dt::sc_bv<16> > c0_ddr4_s_axi_rid;
  sc_core::sc_out< sc_dt::sc_bv<512> > c0_ddr4_s_axi_rdata;
  sc_core::sc_in< bool > sys_rst;

  // Dummy Signals for IP Ports


protected:

  virtual void before_end_of_elaboration();

private:

  xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>* mp_C0_DDR4_S_AXI_CTRL_transactor;
  xtlm::xaximm_pin2xtlm_t<512,35,16,1,1,1,1,1>* mp_C0_DDR4_S_AXI_transactor;
  xsc::common::vectorN2scalar_converter<1>* mp_c0_ddr4_s_axi_arlock_converter;
  sc_signal< bool > m_c0_ddr4_s_axi_arlock_converter_signal;
  xsc::common::vectorN2scalar_converter<1>* mp_c0_ddr4_s_axi_awlock_converter;
  sc_signal< bool > m_c0_ddr4_s_axi_awlock_converter_signal;

  // Transactor stubs
  xtlm::xtlm_aximm_target_stub * C0_DDR4_S_AXI_CTRL_transactor_target_rd_socket_stub;
  xtlm::xtlm_aximm_target_stub * C0_DDR4_S_AXI_CTRL_transactor_target_wr_socket_stub;
  xtlm::xtlm_aximm_target_stub * C0_DDR4_S_AXI_transactor_target_rd_socket_stub;
  xtlm::xtlm_aximm_target_stub * C0_DDR4_S_AXI_transactor_target_wr_socket_stub;

  // Socket stubs

};
#endif // MTI_SYSTEMC
#endif // IP_CL_DDR4_32G_H_
