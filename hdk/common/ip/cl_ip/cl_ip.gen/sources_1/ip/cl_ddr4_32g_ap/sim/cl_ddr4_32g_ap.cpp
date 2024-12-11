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


#include "cl_ddr4_32g_ap_sc.h"

#include "cl_ddr4_32g_ap.h"

#include "sim_ddr_v2_0.h"

#include <map>
#include <string>





#ifdef XILINX_SIMULATOR
cl_ddr4_32g_ap::cl_ddr4_32g_ap(const sc_core::sc_module_name& nm) : cl_ddr4_32g_ap_sc(nm), c0_init_calib_complete("c0_init_calib_complete"), dbg_clk("dbg_clk"), c0_sys_clk_p("c0_sys_clk_p"), c0_sys_clk_n("c0_sys_clk_n"), dbg_bus("dbg_bus"), c0_ddr4_adr("c0_ddr4_adr"), c0_ddr4_ba("c0_ddr4_ba"), c0_ddr4_cke("c0_ddr4_cke"), c0_ddr4_cs_n("c0_ddr4_cs_n"), c0_ddr4_dq("c0_ddr4_dq"), c0_ddr4_dqs_c("c0_ddr4_dqs_c"), c0_ddr4_dqs_t("c0_ddr4_dqs_t"), c0_ddr4_odt("c0_ddr4_odt"), c0_ddr4_parity("c0_ddr4_parity"), c0_ddr4_bg("c0_ddr4_bg"), c0_ddr4_reset_n("c0_ddr4_reset_n"), c0_ddr4_act_n("c0_ddr4_act_n"), c0_ddr4_ck_c("c0_ddr4_ck_c"), c0_ddr4_ck_t("c0_ddr4_ck_t"), c0_ddr4_ui_clk("c0_ddr4_ui_clk"), c0_ddr4_ui_clk_sync_rst("c0_ddr4_ui_clk_sync_rst"), c0_ddr4_app_sref_req("c0_ddr4_app_sref_req"), c0_ddr4_app_sref_ack("c0_ddr4_app_sref_ack"), c0_ddr4_app_restore_en("c0_ddr4_app_restore_en"), c0_ddr4_app_restore_complete("c0_ddr4_app_restore_complete"), c0_ddr4_app_mem_init_skip("c0_ddr4_app_mem_init_skip"), c0_ddr4_app_xsdb_select("c0_ddr4_app_xsdb_select"), c0_ddr4_app_xsdb_rd_en("c0_ddr4_app_xsdb_rd_en"), c0_ddr4_app_xsdb_wr_en("c0_ddr4_app_xsdb_wr_en"), c0_ddr4_app_xsdb_addr("c0_ddr4_app_xsdb_addr"), c0_ddr4_app_xsdb_wr_data("c0_ddr4_app_xsdb_wr_data"), c0_ddr4_app_xsdb_rd_data("c0_ddr4_app_xsdb_rd_data"), c0_ddr4_app_xsdb_rdy("c0_ddr4_app_xsdb_rdy"), c0_ddr4_app_dbg_out("c0_ddr4_app_dbg_out"), c0_ddr4_aresetn("c0_ddr4_aresetn"), c0_ddr4_s_axi_ctrl_awvalid("c0_ddr4_s_axi_ctrl_awvalid"), c0_ddr4_s_axi_ctrl_awready("c0_ddr4_s_axi_ctrl_awready"), c0_ddr4_s_axi_ctrl_awaddr("c0_ddr4_s_axi_ctrl_awaddr"), c0_ddr4_s_axi_ctrl_wvalid("c0_ddr4_s_axi_ctrl_wvalid"), c0_ddr4_s_axi_ctrl_wready("c0_ddr4_s_axi_ctrl_wready"), c0_ddr4_s_axi_ctrl_wdata("c0_ddr4_s_axi_ctrl_wdata"), c0_ddr4_s_axi_ctrl_bvalid("c0_ddr4_s_axi_ctrl_bvalid"), c0_ddr4_s_axi_ctrl_bready("c0_ddr4_s_axi_ctrl_bready"), c0_ddr4_s_axi_ctrl_bresp("c0_ddr4_s_axi_ctrl_bresp"), c0_ddr4_s_axi_ctrl_arvalid("c0_ddr4_s_axi_ctrl_arvalid"), c0_ddr4_s_axi_ctrl_arready("c0_ddr4_s_axi_ctrl_arready"), c0_ddr4_s_axi_ctrl_araddr("c0_ddr4_s_axi_ctrl_araddr"), c0_ddr4_s_axi_ctrl_rvalid("c0_ddr4_s_axi_ctrl_rvalid"), c0_ddr4_s_axi_ctrl_rready("c0_ddr4_s_axi_ctrl_rready"), c0_ddr4_s_axi_ctrl_rdata("c0_ddr4_s_axi_ctrl_rdata"), c0_ddr4_s_axi_ctrl_rresp("c0_ddr4_s_axi_ctrl_rresp"), c0_ddr4_interrupt("c0_ddr4_interrupt"), c0_ddr4_s_axi_awid("c0_ddr4_s_axi_awid"), c0_ddr4_s_axi_awaddr("c0_ddr4_s_axi_awaddr"), c0_ddr4_s_axi_awlen("c0_ddr4_s_axi_awlen"), c0_ddr4_s_axi_awsize("c0_ddr4_s_axi_awsize"), c0_ddr4_s_axi_awburst("c0_ddr4_s_axi_awburst"), c0_ddr4_s_axi_awlock("c0_ddr4_s_axi_awlock"), c0_ddr4_s_axi_awcache("c0_ddr4_s_axi_awcache"), c0_ddr4_s_axi_awprot("c0_ddr4_s_axi_awprot"), c0_ddr4_s_axi_awqos("c0_ddr4_s_axi_awqos"), c0_ddr4_s_axi_awvalid("c0_ddr4_s_axi_awvalid"), c0_ddr4_s_axi_awready("c0_ddr4_s_axi_awready"), c0_ddr4_s_axi_wdata("c0_ddr4_s_axi_wdata"), c0_ddr4_s_axi_wstrb("c0_ddr4_s_axi_wstrb"), c0_ddr4_s_axi_wlast("c0_ddr4_s_axi_wlast"), c0_ddr4_s_axi_wvalid("c0_ddr4_s_axi_wvalid"), c0_ddr4_s_axi_wready("c0_ddr4_s_axi_wready"), c0_ddr4_s_axi_bready("c0_ddr4_s_axi_bready"), c0_ddr4_s_axi_bid("c0_ddr4_s_axi_bid"), c0_ddr4_s_axi_bresp("c0_ddr4_s_axi_bresp"), c0_ddr4_s_axi_bvalid("c0_ddr4_s_axi_bvalid"), c0_ddr4_s_axi_arid("c0_ddr4_s_axi_arid"), c0_ddr4_s_axi_araddr("c0_ddr4_s_axi_araddr"), c0_ddr4_s_axi_arlen("c0_ddr4_s_axi_arlen"), c0_ddr4_s_axi_arsize("c0_ddr4_s_axi_arsize"), c0_ddr4_s_axi_arburst("c0_ddr4_s_axi_arburst"), c0_ddr4_s_axi_arlock("c0_ddr4_s_axi_arlock"), c0_ddr4_s_axi_arcache("c0_ddr4_s_axi_arcache"), c0_ddr4_s_axi_arprot("c0_ddr4_s_axi_arprot"), c0_ddr4_s_axi_arqos("c0_ddr4_s_axi_arqos"), c0_ddr4_s_axi_arvalid("c0_ddr4_s_axi_arvalid"), c0_ddr4_s_axi_arready("c0_ddr4_s_axi_arready"), c0_ddr4_s_axi_rready("c0_ddr4_s_axi_rready"), c0_ddr4_s_axi_rlast("c0_ddr4_s_axi_rlast"), c0_ddr4_s_axi_rvalid("c0_ddr4_s_axi_rvalid"), c0_ddr4_s_axi_rresp("c0_ddr4_s_axi_rresp"), c0_ddr4_s_axi_rid("c0_ddr4_s_axi_rid"), c0_ddr4_s_axi_rdata("c0_ddr4_s_axi_rdata"), c0_ddr4_s_axi_aruser("c0_ddr4_s_axi_aruser"), c0_ddr4_s_axi_awuser("c0_ddr4_s_axi_awuser"), sys_rst("sys_rst")
{

  // initialize pins
  mp_impl->c0_init_calib_complete(c0_init_calib_complete);
  mp_impl->dbg_clk(dbg_clk);
  mp_impl->c0_sys_clk_p(c0_sys_clk_p);
  mp_impl->c0_sys_clk_n(c0_sys_clk_n);
  mp_impl->dbg_bus(dbg_bus);
  mp_impl->c0_ddr4_adr(c0_ddr4_adr);
  mp_impl->c0_ddr4_ba(c0_ddr4_ba);
  mp_impl->c0_ddr4_cke(c0_ddr4_cke);
  mp_impl->c0_ddr4_cs_n(c0_ddr4_cs_n);
  mp_impl->c0_ddr4_dq(c0_ddr4_dq);
  mp_impl->c0_ddr4_dqs_c(c0_ddr4_dqs_c);
  mp_impl->c0_ddr4_dqs_t(c0_ddr4_dqs_t);
  mp_impl->c0_ddr4_odt(c0_ddr4_odt);
  mp_impl->c0_ddr4_parity(c0_ddr4_parity);
  mp_impl->c0_ddr4_bg(c0_ddr4_bg);
  mp_impl->c0_ddr4_reset_n(c0_ddr4_reset_n);
  mp_impl->c0_ddr4_act_n(c0_ddr4_act_n);
  mp_impl->c0_ddr4_ck_c(c0_ddr4_ck_c);
  mp_impl->c0_ddr4_ck_t(c0_ddr4_ck_t);
  mp_impl->c0_ddr4_ui_clk(c0_ddr4_ui_clk);
  mp_impl->c0_ddr4_ui_clk_sync_rst(c0_ddr4_ui_clk_sync_rst);
  mp_impl->c0_ddr4_app_sref_req(c0_ddr4_app_sref_req);
  mp_impl->c0_ddr4_app_sref_ack(c0_ddr4_app_sref_ack);
  mp_impl->c0_ddr4_app_restore_en(c0_ddr4_app_restore_en);
  mp_impl->c0_ddr4_app_restore_complete(c0_ddr4_app_restore_complete);
  mp_impl->c0_ddr4_app_mem_init_skip(c0_ddr4_app_mem_init_skip);
  mp_impl->c0_ddr4_app_xsdb_select(c0_ddr4_app_xsdb_select);
  mp_impl->c0_ddr4_app_xsdb_rd_en(c0_ddr4_app_xsdb_rd_en);
  mp_impl->c0_ddr4_app_xsdb_wr_en(c0_ddr4_app_xsdb_wr_en);
  mp_impl->c0_ddr4_app_xsdb_addr(c0_ddr4_app_xsdb_addr);
  mp_impl->c0_ddr4_app_xsdb_wr_data(c0_ddr4_app_xsdb_wr_data);
  mp_impl->c0_ddr4_app_xsdb_rd_data(c0_ddr4_app_xsdb_rd_data);
  mp_impl->c0_ddr4_app_xsdb_rdy(c0_ddr4_app_xsdb_rdy);
  mp_impl->c0_ddr4_app_dbg_out(c0_ddr4_app_dbg_out);
  mp_impl->c0_ddr4_aresetn(c0_ddr4_aresetn);
  mp_impl->c0_ddr4_interrupt(c0_ddr4_interrupt);
  mp_impl->sys_rst(sys_rst);

  // initialize transactors
  mp_C0_DDR4_S_AXI_CTRL_transactor = NULL;
  mp_C0_DDR4_S_AXI_transactor = NULL;
  mp_c0_ddr4_s_axi_arlock_converter = NULL;
  mp_c0_ddr4_s_axi_aruser_converter = NULL;
  mp_c0_ddr4_s_axi_awlock_converter = NULL;
  mp_c0_ddr4_s_axi_awuser_converter = NULL;

  // initialize socket stubs

}

void cl_ddr4_32g_ap::before_end_of_elaboration()
{
  // configure 'C0_DDR4_S_AXI_CTRL' transactor

  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_ddr4_32g_ap", "C0_DDR4_S_AXI_CTRL_TLM_MODE") != 1)
  {
    // Instantiate Socket Stubs

  // 'C0_DDR4_S_AXI_CTRL' transactor parameters
    xsc::common_cpp::properties C0_DDR4_S_AXI_CTRL_transactor_param_props;
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("DATA_WIDTH", "32");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("ID_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("ADDR_WIDTH", "32");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("WUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("RUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("BUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_BURST", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_LOCK", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_PROT", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_CACHE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_QOS", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_REGION", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_WSTRB", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_BRESP", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_RRESP", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_SIZE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_RESET", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addFloat("FREQ_HZ", "2.665e+08");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addFloat("PHASE", "0.0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_C0_DDR4_S_AXI_CTRL_transactor = new xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>("C0_DDR4_S_AXI_CTRL_transactor", C0_DDR4_S_AXI_CTRL_transactor_param_props);

    // C0_DDR4_S_AXI_CTRL' transactor ports

    mp_C0_DDR4_S_AXI_CTRL_transactor->ARADDR(c0_ddr4_s_axi_ctrl_araddr);
    mp_C0_DDR4_S_AXI_CTRL_transactor->ARREADY(c0_ddr4_s_axi_ctrl_arready);
    mp_C0_DDR4_S_AXI_CTRL_transactor->ARVALID(c0_ddr4_s_axi_ctrl_arvalid);
    mp_C0_DDR4_S_AXI_CTRL_transactor->AWADDR(c0_ddr4_s_axi_ctrl_awaddr);
    mp_C0_DDR4_S_AXI_CTRL_transactor->AWREADY(c0_ddr4_s_axi_ctrl_awready);
    mp_C0_DDR4_S_AXI_CTRL_transactor->AWVALID(c0_ddr4_s_axi_ctrl_awvalid);
    mp_C0_DDR4_S_AXI_CTRL_transactor->BREADY(c0_ddr4_s_axi_ctrl_bready);
    mp_C0_DDR4_S_AXI_CTRL_transactor->BRESP(c0_ddr4_s_axi_ctrl_bresp);
    mp_C0_DDR4_S_AXI_CTRL_transactor->BVALID(c0_ddr4_s_axi_ctrl_bvalid);
    mp_C0_DDR4_S_AXI_CTRL_transactor->RDATA(c0_ddr4_s_axi_ctrl_rdata);
    mp_C0_DDR4_S_AXI_CTRL_transactor->RREADY(c0_ddr4_s_axi_ctrl_rready);
    mp_C0_DDR4_S_AXI_CTRL_transactor->RRESP(c0_ddr4_s_axi_ctrl_rresp);
    mp_C0_DDR4_S_AXI_CTRL_transactor->RVALID(c0_ddr4_s_axi_ctrl_rvalid);
    mp_C0_DDR4_S_AXI_CTRL_transactor->WDATA(c0_ddr4_s_axi_ctrl_wdata);
    mp_C0_DDR4_S_AXI_CTRL_transactor->WREADY(c0_ddr4_s_axi_ctrl_wready);
    mp_C0_DDR4_S_AXI_CTRL_transactor->WVALID(c0_ddr4_s_axi_ctrl_wvalid);
    mp_C0_DDR4_S_AXI_CTRL_transactor->CLK(c0_ddr4_ui_clk);
    mp_C0_DDR4_S_AXI_CTRL_transactor->RST(c0_ddr4_aresetn);

    // C0_DDR4_S_AXI_CTRL' transactor sockets

    mp_impl->C0_DDR_SAXI_CTRL_rd_socket->bind(*(mp_C0_DDR4_S_AXI_CTRL_transactor->rd_socket));
    mp_impl->C0_DDR_SAXI_CTRL_wr_socket->bind(*(mp_C0_DDR4_S_AXI_CTRL_transactor->wr_socket));
  }
  else
  {
  }

  // configure 'C0_DDR4_S_AXI' transactor

  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_ddr4_32g_ap", "C0_DDR4_S_AXI_TLM_MODE") != 1)
  {
    // Instantiate Socket Stubs

  // 'C0_DDR4_S_AXI' transactor parameters
    xsc::common_cpp::properties C0_DDR4_S_AXI_transactor_param_props;
    C0_DDR4_S_AXI_transactor_param_props.addLong("DATA_WIDTH", "512");
    C0_DDR4_S_AXI_transactor_param_props.addLong("ID_WIDTH", "16");
    C0_DDR4_S_AXI_transactor_param_props.addLong("ADDR_WIDTH", "35");
    C0_DDR4_S_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_BURST", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_LOCK", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_CACHE", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_QOS", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "2");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "2");
    C0_DDR4_S_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "256");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_SIZE", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    C0_DDR4_S_AXI_transactor_param_props.addFloat("FREQ_HZ", "2.665e+08");
    C0_DDR4_S_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    C0_DDR4_S_AXI_transactor_param_props.addString("PROTOCOL", "AXI4");
    C0_DDR4_S_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    C0_DDR4_S_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_C0_DDR4_S_AXI_transactor = new xtlm::xaximm_pin2xtlm_t<512,35,16,1,1,1,1,1>("C0_DDR4_S_AXI_transactor", C0_DDR4_S_AXI_transactor_param_props);

    // C0_DDR4_S_AXI' transactor ports

    mp_C0_DDR4_S_AXI_transactor->ARADDR(c0_ddr4_s_axi_araddr);
    mp_C0_DDR4_S_AXI_transactor->ARBURST(c0_ddr4_s_axi_arburst);
    mp_C0_DDR4_S_AXI_transactor->ARCACHE(c0_ddr4_s_axi_arcache);
    mp_C0_DDR4_S_AXI_transactor->ARID(c0_ddr4_s_axi_arid);
    mp_C0_DDR4_S_AXI_transactor->ARLEN(c0_ddr4_s_axi_arlen);
    mp_c0_ddr4_s_axi_arlock_converter = new xsc::common::vectorN2scalar_converter<1>("c0_ddr4_s_axi_arlock_converter");
    mp_c0_ddr4_s_axi_arlock_converter->vector_in(c0_ddr4_s_axi_arlock);
    mp_c0_ddr4_s_axi_arlock_converter->scalar_out(m_c0_ddr4_s_axi_arlock_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->ARLOCK(m_c0_ddr4_s_axi_arlock_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->ARPROT(c0_ddr4_s_axi_arprot);
    mp_C0_DDR4_S_AXI_transactor->ARQOS(c0_ddr4_s_axi_arqos);
    mp_C0_DDR4_S_AXI_transactor->ARREADY(c0_ddr4_s_axi_arready);
    mp_C0_DDR4_S_AXI_transactor->ARSIZE(c0_ddr4_s_axi_arsize);
    mp_c0_ddr4_s_axi_aruser_converter = new xsc::common::scalar2vectorN_converter<1>("c0_ddr4_s_axi_aruser_converter");
    mp_c0_ddr4_s_axi_aruser_converter->scalar_in(c0_ddr4_s_axi_aruser);
    mp_c0_ddr4_s_axi_aruser_converter->vector_out(m_c0_ddr4_s_axi_aruser_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->ARUSER(m_c0_ddr4_s_axi_aruser_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->ARVALID(c0_ddr4_s_axi_arvalid);
    mp_C0_DDR4_S_AXI_transactor->AWADDR(c0_ddr4_s_axi_awaddr);
    mp_C0_DDR4_S_AXI_transactor->AWBURST(c0_ddr4_s_axi_awburst);
    mp_C0_DDR4_S_AXI_transactor->AWCACHE(c0_ddr4_s_axi_awcache);
    mp_C0_DDR4_S_AXI_transactor->AWID(c0_ddr4_s_axi_awid);
    mp_C0_DDR4_S_AXI_transactor->AWLEN(c0_ddr4_s_axi_awlen);
    mp_c0_ddr4_s_axi_awlock_converter = new xsc::common::vectorN2scalar_converter<1>("c0_ddr4_s_axi_awlock_converter");
    mp_c0_ddr4_s_axi_awlock_converter->vector_in(c0_ddr4_s_axi_awlock);
    mp_c0_ddr4_s_axi_awlock_converter->scalar_out(m_c0_ddr4_s_axi_awlock_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->AWLOCK(m_c0_ddr4_s_axi_awlock_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->AWPROT(c0_ddr4_s_axi_awprot);
    mp_C0_DDR4_S_AXI_transactor->AWQOS(c0_ddr4_s_axi_awqos);
    mp_C0_DDR4_S_AXI_transactor->AWREADY(c0_ddr4_s_axi_awready);
    mp_C0_DDR4_S_AXI_transactor->AWSIZE(c0_ddr4_s_axi_awsize);
    mp_c0_ddr4_s_axi_awuser_converter = new xsc::common::scalar2vectorN_converter<1>("c0_ddr4_s_axi_awuser_converter");
    mp_c0_ddr4_s_axi_awuser_converter->scalar_in(c0_ddr4_s_axi_awuser);
    mp_c0_ddr4_s_axi_awuser_converter->vector_out(m_c0_ddr4_s_axi_awuser_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->AWUSER(m_c0_ddr4_s_axi_awuser_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->AWVALID(c0_ddr4_s_axi_awvalid);
    mp_C0_DDR4_S_AXI_transactor->BID(c0_ddr4_s_axi_bid);
    mp_C0_DDR4_S_AXI_transactor->BREADY(c0_ddr4_s_axi_bready);
    mp_C0_DDR4_S_AXI_transactor->BRESP(c0_ddr4_s_axi_bresp);
    mp_C0_DDR4_S_AXI_transactor->BVALID(c0_ddr4_s_axi_bvalid);
    mp_C0_DDR4_S_AXI_transactor->RDATA(c0_ddr4_s_axi_rdata);
    mp_C0_DDR4_S_AXI_transactor->RID(c0_ddr4_s_axi_rid);
    mp_C0_DDR4_S_AXI_transactor->RLAST(c0_ddr4_s_axi_rlast);
    mp_C0_DDR4_S_AXI_transactor->RREADY(c0_ddr4_s_axi_rready);
    mp_C0_DDR4_S_AXI_transactor->RRESP(c0_ddr4_s_axi_rresp);
    mp_C0_DDR4_S_AXI_transactor->RVALID(c0_ddr4_s_axi_rvalid);
    mp_C0_DDR4_S_AXI_transactor->WDATA(c0_ddr4_s_axi_wdata);
    mp_C0_DDR4_S_AXI_transactor->WLAST(c0_ddr4_s_axi_wlast);
    mp_C0_DDR4_S_AXI_transactor->WREADY(c0_ddr4_s_axi_wready);
    mp_C0_DDR4_S_AXI_transactor->WSTRB(c0_ddr4_s_axi_wstrb);
    mp_C0_DDR4_S_AXI_transactor->WVALID(c0_ddr4_s_axi_wvalid);
    mp_C0_DDR4_S_AXI_transactor->CLK(c0_ddr4_ui_clk);
    mp_C0_DDR4_S_AXI_transactor->RST(c0_ddr4_aresetn);

    // C0_DDR4_S_AXI' transactor sockets

    mp_impl->C0_DDR_SAXI_rd_socket->bind(*(mp_C0_DDR4_S_AXI_transactor->rd_socket));
    mp_impl->C0_DDR_SAXI_wr_socket->bind(*(mp_C0_DDR4_S_AXI_transactor->wr_socket));
  }
  else
  {
  }

}

#endif // XILINX_SIMULATOR




#ifdef XM_SYSTEMC
cl_ddr4_32g_ap::cl_ddr4_32g_ap(const sc_core::sc_module_name& nm) : cl_ddr4_32g_ap_sc(nm), c0_init_calib_complete("c0_init_calib_complete"), dbg_clk("dbg_clk"), c0_sys_clk_p("c0_sys_clk_p"), c0_sys_clk_n("c0_sys_clk_n"), dbg_bus("dbg_bus"), c0_ddr4_adr("c0_ddr4_adr"), c0_ddr4_ba("c0_ddr4_ba"), c0_ddr4_cke("c0_ddr4_cke"), c0_ddr4_cs_n("c0_ddr4_cs_n"), c0_ddr4_dq("c0_ddr4_dq"), c0_ddr4_dqs_c("c0_ddr4_dqs_c"), c0_ddr4_dqs_t("c0_ddr4_dqs_t"), c0_ddr4_odt("c0_ddr4_odt"), c0_ddr4_parity("c0_ddr4_parity"), c0_ddr4_bg("c0_ddr4_bg"), c0_ddr4_reset_n("c0_ddr4_reset_n"), c0_ddr4_act_n("c0_ddr4_act_n"), c0_ddr4_ck_c("c0_ddr4_ck_c"), c0_ddr4_ck_t("c0_ddr4_ck_t"), c0_ddr4_ui_clk("c0_ddr4_ui_clk"), c0_ddr4_ui_clk_sync_rst("c0_ddr4_ui_clk_sync_rst"), c0_ddr4_app_sref_req("c0_ddr4_app_sref_req"), c0_ddr4_app_sref_ack("c0_ddr4_app_sref_ack"), c0_ddr4_app_restore_en("c0_ddr4_app_restore_en"), c0_ddr4_app_restore_complete("c0_ddr4_app_restore_complete"), c0_ddr4_app_mem_init_skip("c0_ddr4_app_mem_init_skip"), c0_ddr4_app_xsdb_select("c0_ddr4_app_xsdb_select"), c0_ddr4_app_xsdb_rd_en("c0_ddr4_app_xsdb_rd_en"), c0_ddr4_app_xsdb_wr_en("c0_ddr4_app_xsdb_wr_en"), c0_ddr4_app_xsdb_addr("c0_ddr4_app_xsdb_addr"), c0_ddr4_app_xsdb_wr_data("c0_ddr4_app_xsdb_wr_data"), c0_ddr4_app_xsdb_rd_data("c0_ddr4_app_xsdb_rd_data"), c0_ddr4_app_xsdb_rdy("c0_ddr4_app_xsdb_rdy"), c0_ddr4_app_dbg_out("c0_ddr4_app_dbg_out"), c0_ddr4_aresetn("c0_ddr4_aresetn"), c0_ddr4_s_axi_ctrl_awvalid("c0_ddr4_s_axi_ctrl_awvalid"), c0_ddr4_s_axi_ctrl_awready("c0_ddr4_s_axi_ctrl_awready"), c0_ddr4_s_axi_ctrl_awaddr("c0_ddr4_s_axi_ctrl_awaddr"), c0_ddr4_s_axi_ctrl_wvalid("c0_ddr4_s_axi_ctrl_wvalid"), c0_ddr4_s_axi_ctrl_wready("c0_ddr4_s_axi_ctrl_wready"), c0_ddr4_s_axi_ctrl_wdata("c0_ddr4_s_axi_ctrl_wdata"), c0_ddr4_s_axi_ctrl_bvalid("c0_ddr4_s_axi_ctrl_bvalid"), c0_ddr4_s_axi_ctrl_bready("c0_ddr4_s_axi_ctrl_bready"), c0_ddr4_s_axi_ctrl_bresp("c0_ddr4_s_axi_ctrl_bresp"), c0_ddr4_s_axi_ctrl_arvalid("c0_ddr4_s_axi_ctrl_arvalid"), c0_ddr4_s_axi_ctrl_arready("c0_ddr4_s_axi_ctrl_arready"), c0_ddr4_s_axi_ctrl_araddr("c0_ddr4_s_axi_ctrl_araddr"), c0_ddr4_s_axi_ctrl_rvalid("c0_ddr4_s_axi_ctrl_rvalid"), c0_ddr4_s_axi_ctrl_rready("c0_ddr4_s_axi_ctrl_rready"), c0_ddr4_s_axi_ctrl_rdata("c0_ddr4_s_axi_ctrl_rdata"), c0_ddr4_s_axi_ctrl_rresp("c0_ddr4_s_axi_ctrl_rresp"), c0_ddr4_interrupt("c0_ddr4_interrupt"), c0_ddr4_s_axi_awid("c0_ddr4_s_axi_awid"), c0_ddr4_s_axi_awaddr("c0_ddr4_s_axi_awaddr"), c0_ddr4_s_axi_awlen("c0_ddr4_s_axi_awlen"), c0_ddr4_s_axi_awsize("c0_ddr4_s_axi_awsize"), c0_ddr4_s_axi_awburst("c0_ddr4_s_axi_awburst"), c0_ddr4_s_axi_awlock("c0_ddr4_s_axi_awlock"), c0_ddr4_s_axi_awcache("c0_ddr4_s_axi_awcache"), c0_ddr4_s_axi_awprot("c0_ddr4_s_axi_awprot"), c0_ddr4_s_axi_awqos("c0_ddr4_s_axi_awqos"), c0_ddr4_s_axi_awvalid("c0_ddr4_s_axi_awvalid"), c0_ddr4_s_axi_awready("c0_ddr4_s_axi_awready"), c0_ddr4_s_axi_wdata("c0_ddr4_s_axi_wdata"), c0_ddr4_s_axi_wstrb("c0_ddr4_s_axi_wstrb"), c0_ddr4_s_axi_wlast("c0_ddr4_s_axi_wlast"), c0_ddr4_s_axi_wvalid("c0_ddr4_s_axi_wvalid"), c0_ddr4_s_axi_wready("c0_ddr4_s_axi_wready"), c0_ddr4_s_axi_bready("c0_ddr4_s_axi_bready"), c0_ddr4_s_axi_bid("c0_ddr4_s_axi_bid"), c0_ddr4_s_axi_bresp("c0_ddr4_s_axi_bresp"), c0_ddr4_s_axi_bvalid("c0_ddr4_s_axi_bvalid"), c0_ddr4_s_axi_arid("c0_ddr4_s_axi_arid"), c0_ddr4_s_axi_araddr("c0_ddr4_s_axi_araddr"), c0_ddr4_s_axi_arlen("c0_ddr4_s_axi_arlen"), c0_ddr4_s_axi_arsize("c0_ddr4_s_axi_arsize"), c0_ddr4_s_axi_arburst("c0_ddr4_s_axi_arburst"), c0_ddr4_s_axi_arlock("c0_ddr4_s_axi_arlock"), c0_ddr4_s_axi_arcache("c0_ddr4_s_axi_arcache"), c0_ddr4_s_axi_arprot("c0_ddr4_s_axi_arprot"), c0_ddr4_s_axi_arqos("c0_ddr4_s_axi_arqos"), c0_ddr4_s_axi_arvalid("c0_ddr4_s_axi_arvalid"), c0_ddr4_s_axi_arready("c0_ddr4_s_axi_arready"), c0_ddr4_s_axi_rready("c0_ddr4_s_axi_rready"), c0_ddr4_s_axi_rlast("c0_ddr4_s_axi_rlast"), c0_ddr4_s_axi_rvalid("c0_ddr4_s_axi_rvalid"), c0_ddr4_s_axi_rresp("c0_ddr4_s_axi_rresp"), c0_ddr4_s_axi_rid("c0_ddr4_s_axi_rid"), c0_ddr4_s_axi_rdata("c0_ddr4_s_axi_rdata"), c0_ddr4_s_axi_aruser("c0_ddr4_s_axi_aruser"), c0_ddr4_s_axi_awuser("c0_ddr4_s_axi_awuser"), sys_rst("sys_rst")
{

  // initialize pins
  mp_impl->c0_init_calib_complete(c0_init_calib_complete);
  mp_impl->dbg_clk(dbg_clk);
  mp_impl->c0_sys_clk_p(c0_sys_clk_p);
  mp_impl->c0_sys_clk_n(c0_sys_clk_n);
  mp_impl->dbg_bus(dbg_bus);
  mp_impl->c0_ddr4_adr(c0_ddr4_adr);
  mp_impl->c0_ddr4_ba(c0_ddr4_ba);
  mp_impl->c0_ddr4_cke(c0_ddr4_cke);
  mp_impl->c0_ddr4_cs_n(c0_ddr4_cs_n);
  mp_impl->c0_ddr4_dq(c0_ddr4_dq);
  mp_impl->c0_ddr4_dqs_c(c0_ddr4_dqs_c);
  mp_impl->c0_ddr4_dqs_t(c0_ddr4_dqs_t);
  mp_impl->c0_ddr4_odt(c0_ddr4_odt);
  mp_impl->c0_ddr4_parity(c0_ddr4_parity);
  mp_impl->c0_ddr4_bg(c0_ddr4_bg);
  mp_impl->c0_ddr4_reset_n(c0_ddr4_reset_n);
  mp_impl->c0_ddr4_act_n(c0_ddr4_act_n);
  mp_impl->c0_ddr4_ck_c(c0_ddr4_ck_c);
  mp_impl->c0_ddr4_ck_t(c0_ddr4_ck_t);
  mp_impl->c0_ddr4_ui_clk(c0_ddr4_ui_clk);
  mp_impl->c0_ddr4_ui_clk_sync_rst(c0_ddr4_ui_clk_sync_rst);
  mp_impl->c0_ddr4_app_sref_req(c0_ddr4_app_sref_req);
  mp_impl->c0_ddr4_app_sref_ack(c0_ddr4_app_sref_ack);
  mp_impl->c0_ddr4_app_restore_en(c0_ddr4_app_restore_en);
  mp_impl->c0_ddr4_app_restore_complete(c0_ddr4_app_restore_complete);
  mp_impl->c0_ddr4_app_mem_init_skip(c0_ddr4_app_mem_init_skip);
  mp_impl->c0_ddr4_app_xsdb_select(c0_ddr4_app_xsdb_select);
  mp_impl->c0_ddr4_app_xsdb_rd_en(c0_ddr4_app_xsdb_rd_en);
  mp_impl->c0_ddr4_app_xsdb_wr_en(c0_ddr4_app_xsdb_wr_en);
  mp_impl->c0_ddr4_app_xsdb_addr(c0_ddr4_app_xsdb_addr);
  mp_impl->c0_ddr4_app_xsdb_wr_data(c0_ddr4_app_xsdb_wr_data);
  mp_impl->c0_ddr4_app_xsdb_rd_data(c0_ddr4_app_xsdb_rd_data);
  mp_impl->c0_ddr4_app_xsdb_rdy(c0_ddr4_app_xsdb_rdy);
  mp_impl->c0_ddr4_app_dbg_out(c0_ddr4_app_dbg_out);
  mp_impl->c0_ddr4_aresetn(c0_ddr4_aresetn);
  mp_impl->c0_ddr4_interrupt(c0_ddr4_interrupt);
  mp_impl->sys_rst(sys_rst);

  // initialize transactors
  mp_C0_DDR4_S_AXI_CTRL_transactor = NULL;
  mp_C0_DDR4_S_AXI_transactor = NULL;
  mp_c0_ddr4_s_axi_arlock_converter = NULL;
  mp_c0_ddr4_s_axi_aruser_converter = NULL;
  mp_c0_ddr4_s_axi_awlock_converter = NULL;
  mp_c0_ddr4_s_axi_awuser_converter = NULL;

  // initialize socket stubs

}

void cl_ddr4_32g_ap::before_end_of_elaboration()
{
  // configure 'C0_DDR4_S_AXI_CTRL' transactor

  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_ddr4_32g_ap", "C0_DDR4_S_AXI_CTRL_TLM_MODE") != 1)
  {
    // Instantiate Socket Stubs

  // 'C0_DDR4_S_AXI_CTRL' transactor parameters
    xsc::common_cpp::properties C0_DDR4_S_AXI_CTRL_transactor_param_props;
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("DATA_WIDTH", "32");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("ID_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("ADDR_WIDTH", "32");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("WUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("RUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("BUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_BURST", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_LOCK", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_PROT", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_CACHE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_QOS", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_REGION", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_WSTRB", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_BRESP", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_RRESP", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_SIZE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_RESET", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addFloat("FREQ_HZ", "2.665e+08");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addFloat("PHASE", "0.0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_C0_DDR4_S_AXI_CTRL_transactor = new xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>("C0_DDR4_S_AXI_CTRL_transactor", C0_DDR4_S_AXI_CTRL_transactor_param_props);

    // C0_DDR4_S_AXI_CTRL' transactor ports

    mp_C0_DDR4_S_AXI_CTRL_transactor->ARADDR(c0_ddr4_s_axi_ctrl_araddr);
    mp_C0_DDR4_S_AXI_CTRL_transactor->ARREADY(c0_ddr4_s_axi_ctrl_arready);
    mp_C0_DDR4_S_AXI_CTRL_transactor->ARVALID(c0_ddr4_s_axi_ctrl_arvalid);
    mp_C0_DDR4_S_AXI_CTRL_transactor->AWADDR(c0_ddr4_s_axi_ctrl_awaddr);
    mp_C0_DDR4_S_AXI_CTRL_transactor->AWREADY(c0_ddr4_s_axi_ctrl_awready);
    mp_C0_DDR4_S_AXI_CTRL_transactor->AWVALID(c0_ddr4_s_axi_ctrl_awvalid);
    mp_C0_DDR4_S_AXI_CTRL_transactor->BREADY(c0_ddr4_s_axi_ctrl_bready);
    mp_C0_DDR4_S_AXI_CTRL_transactor->BRESP(c0_ddr4_s_axi_ctrl_bresp);
    mp_C0_DDR4_S_AXI_CTRL_transactor->BVALID(c0_ddr4_s_axi_ctrl_bvalid);
    mp_C0_DDR4_S_AXI_CTRL_transactor->RDATA(c0_ddr4_s_axi_ctrl_rdata);
    mp_C0_DDR4_S_AXI_CTRL_transactor->RREADY(c0_ddr4_s_axi_ctrl_rready);
    mp_C0_DDR4_S_AXI_CTRL_transactor->RRESP(c0_ddr4_s_axi_ctrl_rresp);
    mp_C0_DDR4_S_AXI_CTRL_transactor->RVALID(c0_ddr4_s_axi_ctrl_rvalid);
    mp_C0_DDR4_S_AXI_CTRL_transactor->WDATA(c0_ddr4_s_axi_ctrl_wdata);
    mp_C0_DDR4_S_AXI_CTRL_transactor->WREADY(c0_ddr4_s_axi_ctrl_wready);
    mp_C0_DDR4_S_AXI_CTRL_transactor->WVALID(c0_ddr4_s_axi_ctrl_wvalid);
    mp_C0_DDR4_S_AXI_CTRL_transactor->CLK(c0_ddr4_ui_clk);
    mp_C0_DDR4_S_AXI_CTRL_transactor->RST(c0_ddr4_aresetn);

    // C0_DDR4_S_AXI_CTRL' transactor sockets

    mp_impl->C0_DDR_SAXI_CTRL_rd_socket->bind(*(mp_C0_DDR4_S_AXI_CTRL_transactor->rd_socket));
    mp_impl->C0_DDR_SAXI_CTRL_wr_socket->bind(*(mp_C0_DDR4_S_AXI_CTRL_transactor->wr_socket));
  }
  else
  {
  }

  // configure 'C0_DDR4_S_AXI' transactor

  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_ddr4_32g_ap", "C0_DDR4_S_AXI_TLM_MODE") != 1)
  {
    // Instantiate Socket Stubs

  // 'C0_DDR4_S_AXI' transactor parameters
    xsc::common_cpp::properties C0_DDR4_S_AXI_transactor_param_props;
    C0_DDR4_S_AXI_transactor_param_props.addLong("DATA_WIDTH", "512");
    C0_DDR4_S_AXI_transactor_param_props.addLong("ID_WIDTH", "16");
    C0_DDR4_S_AXI_transactor_param_props.addLong("ADDR_WIDTH", "35");
    C0_DDR4_S_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_BURST", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_LOCK", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_CACHE", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_QOS", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "2");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "2");
    C0_DDR4_S_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "256");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_SIZE", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    C0_DDR4_S_AXI_transactor_param_props.addFloat("FREQ_HZ", "2.665e+08");
    C0_DDR4_S_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    C0_DDR4_S_AXI_transactor_param_props.addString("PROTOCOL", "AXI4");
    C0_DDR4_S_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    C0_DDR4_S_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_C0_DDR4_S_AXI_transactor = new xtlm::xaximm_pin2xtlm_t<512,35,16,1,1,1,1,1>("C0_DDR4_S_AXI_transactor", C0_DDR4_S_AXI_transactor_param_props);

    // C0_DDR4_S_AXI' transactor ports

    mp_C0_DDR4_S_AXI_transactor->ARADDR(c0_ddr4_s_axi_araddr);
    mp_C0_DDR4_S_AXI_transactor->ARBURST(c0_ddr4_s_axi_arburst);
    mp_C0_DDR4_S_AXI_transactor->ARCACHE(c0_ddr4_s_axi_arcache);
    mp_C0_DDR4_S_AXI_transactor->ARID(c0_ddr4_s_axi_arid);
    mp_C0_DDR4_S_AXI_transactor->ARLEN(c0_ddr4_s_axi_arlen);
    mp_c0_ddr4_s_axi_arlock_converter = new xsc::common::vectorN2scalar_converter<1>("c0_ddr4_s_axi_arlock_converter");
    mp_c0_ddr4_s_axi_arlock_converter->vector_in(c0_ddr4_s_axi_arlock);
    mp_c0_ddr4_s_axi_arlock_converter->scalar_out(m_c0_ddr4_s_axi_arlock_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->ARLOCK(m_c0_ddr4_s_axi_arlock_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->ARPROT(c0_ddr4_s_axi_arprot);
    mp_C0_DDR4_S_AXI_transactor->ARQOS(c0_ddr4_s_axi_arqos);
    mp_C0_DDR4_S_AXI_transactor->ARREADY(c0_ddr4_s_axi_arready);
    mp_C0_DDR4_S_AXI_transactor->ARSIZE(c0_ddr4_s_axi_arsize);
    mp_c0_ddr4_s_axi_aruser_converter = new xsc::common::scalar2vectorN_converter<1>("c0_ddr4_s_axi_aruser_converter");
    mp_c0_ddr4_s_axi_aruser_converter->scalar_in(c0_ddr4_s_axi_aruser);
    mp_c0_ddr4_s_axi_aruser_converter->vector_out(m_c0_ddr4_s_axi_aruser_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->ARUSER(m_c0_ddr4_s_axi_aruser_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->ARVALID(c0_ddr4_s_axi_arvalid);
    mp_C0_DDR4_S_AXI_transactor->AWADDR(c0_ddr4_s_axi_awaddr);
    mp_C0_DDR4_S_AXI_transactor->AWBURST(c0_ddr4_s_axi_awburst);
    mp_C0_DDR4_S_AXI_transactor->AWCACHE(c0_ddr4_s_axi_awcache);
    mp_C0_DDR4_S_AXI_transactor->AWID(c0_ddr4_s_axi_awid);
    mp_C0_DDR4_S_AXI_transactor->AWLEN(c0_ddr4_s_axi_awlen);
    mp_c0_ddr4_s_axi_awlock_converter = new xsc::common::vectorN2scalar_converter<1>("c0_ddr4_s_axi_awlock_converter");
    mp_c0_ddr4_s_axi_awlock_converter->vector_in(c0_ddr4_s_axi_awlock);
    mp_c0_ddr4_s_axi_awlock_converter->scalar_out(m_c0_ddr4_s_axi_awlock_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->AWLOCK(m_c0_ddr4_s_axi_awlock_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->AWPROT(c0_ddr4_s_axi_awprot);
    mp_C0_DDR4_S_AXI_transactor->AWQOS(c0_ddr4_s_axi_awqos);
    mp_C0_DDR4_S_AXI_transactor->AWREADY(c0_ddr4_s_axi_awready);
    mp_C0_DDR4_S_AXI_transactor->AWSIZE(c0_ddr4_s_axi_awsize);
    mp_c0_ddr4_s_axi_awuser_converter = new xsc::common::scalar2vectorN_converter<1>("c0_ddr4_s_axi_awuser_converter");
    mp_c0_ddr4_s_axi_awuser_converter->scalar_in(c0_ddr4_s_axi_awuser);
    mp_c0_ddr4_s_axi_awuser_converter->vector_out(m_c0_ddr4_s_axi_awuser_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->AWUSER(m_c0_ddr4_s_axi_awuser_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->AWVALID(c0_ddr4_s_axi_awvalid);
    mp_C0_DDR4_S_AXI_transactor->BID(c0_ddr4_s_axi_bid);
    mp_C0_DDR4_S_AXI_transactor->BREADY(c0_ddr4_s_axi_bready);
    mp_C0_DDR4_S_AXI_transactor->BRESP(c0_ddr4_s_axi_bresp);
    mp_C0_DDR4_S_AXI_transactor->BVALID(c0_ddr4_s_axi_bvalid);
    mp_C0_DDR4_S_AXI_transactor->RDATA(c0_ddr4_s_axi_rdata);
    mp_C0_DDR4_S_AXI_transactor->RID(c0_ddr4_s_axi_rid);
    mp_C0_DDR4_S_AXI_transactor->RLAST(c0_ddr4_s_axi_rlast);
    mp_C0_DDR4_S_AXI_transactor->RREADY(c0_ddr4_s_axi_rready);
    mp_C0_DDR4_S_AXI_transactor->RRESP(c0_ddr4_s_axi_rresp);
    mp_C0_DDR4_S_AXI_transactor->RVALID(c0_ddr4_s_axi_rvalid);
    mp_C0_DDR4_S_AXI_transactor->WDATA(c0_ddr4_s_axi_wdata);
    mp_C0_DDR4_S_AXI_transactor->WLAST(c0_ddr4_s_axi_wlast);
    mp_C0_DDR4_S_AXI_transactor->WREADY(c0_ddr4_s_axi_wready);
    mp_C0_DDR4_S_AXI_transactor->WSTRB(c0_ddr4_s_axi_wstrb);
    mp_C0_DDR4_S_AXI_transactor->WVALID(c0_ddr4_s_axi_wvalid);
    mp_C0_DDR4_S_AXI_transactor->CLK(c0_ddr4_ui_clk);
    mp_C0_DDR4_S_AXI_transactor->RST(c0_ddr4_aresetn);

    // C0_DDR4_S_AXI' transactor sockets

    mp_impl->C0_DDR_SAXI_rd_socket->bind(*(mp_C0_DDR4_S_AXI_transactor->rd_socket));
    mp_impl->C0_DDR_SAXI_wr_socket->bind(*(mp_C0_DDR4_S_AXI_transactor->wr_socket));
  }
  else
  {
  }

}

#endif // XM_SYSTEMC




#ifdef RIVIERA
cl_ddr4_32g_ap::cl_ddr4_32g_ap(const sc_core::sc_module_name& nm) : cl_ddr4_32g_ap_sc(nm), c0_init_calib_complete("c0_init_calib_complete"), dbg_clk("dbg_clk"), c0_sys_clk_p("c0_sys_clk_p"), c0_sys_clk_n("c0_sys_clk_n"), dbg_bus("dbg_bus"), c0_ddr4_adr("c0_ddr4_adr"), c0_ddr4_ba("c0_ddr4_ba"), c0_ddr4_cke("c0_ddr4_cke"), c0_ddr4_cs_n("c0_ddr4_cs_n"), c0_ddr4_dq("c0_ddr4_dq"), c0_ddr4_dqs_c("c0_ddr4_dqs_c"), c0_ddr4_dqs_t("c0_ddr4_dqs_t"), c0_ddr4_odt("c0_ddr4_odt"), c0_ddr4_parity("c0_ddr4_parity"), c0_ddr4_bg("c0_ddr4_bg"), c0_ddr4_reset_n("c0_ddr4_reset_n"), c0_ddr4_act_n("c0_ddr4_act_n"), c0_ddr4_ck_c("c0_ddr4_ck_c"), c0_ddr4_ck_t("c0_ddr4_ck_t"), c0_ddr4_ui_clk("c0_ddr4_ui_clk"), c0_ddr4_ui_clk_sync_rst("c0_ddr4_ui_clk_sync_rst"), c0_ddr4_app_sref_req("c0_ddr4_app_sref_req"), c0_ddr4_app_sref_ack("c0_ddr4_app_sref_ack"), c0_ddr4_app_restore_en("c0_ddr4_app_restore_en"), c0_ddr4_app_restore_complete("c0_ddr4_app_restore_complete"), c0_ddr4_app_mem_init_skip("c0_ddr4_app_mem_init_skip"), c0_ddr4_app_xsdb_select("c0_ddr4_app_xsdb_select"), c0_ddr4_app_xsdb_rd_en("c0_ddr4_app_xsdb_rd_en"), c0_ddr4_app_xsdb_wr_en("c0_ddr4_app_xsdb_wr_en"), c0_ddr4_app_xsdb_addr("c0_ddr4_app_xsdb_addr"), c0_ddr4_app_xsdb_wr_data("c0_ddr4_app_xsdb_wr_data"), c0_ddr4_app_xsdb_rd_data("c0_ddr4_app_xsdb_rd_data"), c0_ddr4_app_xsdb_rdy("c0_ddr4_app_xsdb_rdy"), c0_ddr4_app_dbg_out("c0_ddr4_app_dbg_out"), c0_ddr4_aresetn("c0_ddr4_aresetn"), c0_ddr4_s_axi_ctrl_awvalid("c0_ddr4_s_axi_ctrl_awvalid"), c0_ddr4_s_axi_ctrl_awready("c0_ddr4_s_axi_ctrl_awready"), c0_ddr4_s_axi_ctrl_awaddr("c0_ddr4_s_axi_ctrl_awaddr"), c0_ddr4_s_axi_ctrl_wvalid("c0_ddr4_s_axi_ctrl_wvalid"), c0_ddr4_s_axi_ctrl_wready("c0_ddr4_s_axi_ctrl_wready"), c0_ddr4_s_axi_ctrl_wdata("c0_ddr4_s_axi_ctrl_wdata"), c0_ddr4_s_axi_ctrl_bvalid("c0_ddr4_s_axi_ctrl_bvalid"), c0_ddr4_s_axi_ctrl_bready("c0_ddr4_s_axi_ctrl_bready"), c0_ddr4_s_axi_ctrl_bresp("c0_ddr4_s_axi_ctrl_bresp"), c0_ddr4_s_axi_ctrl_arvalid("c0_ddr4_s_axi_ctrl_arvalid"), c0_ddr4_s_axi_ctrl_arready("c0_ddr4_s_axi_ctrl_arready"), c0_ddr4_s_axi_ctrl_araddr("c0_ddr4_s_axi_ctrl_araddr"), c0_ddr4_s_axi_ctrl_rvalid("c0_ddr4_s_axi_ctrl_rvalid"), c0_ddr4_s_axi_ctrl_rready("c0_ddr4_s_axi_ctrl_rready"), c0_ddr4_s_axi_ctrl_rdata("c0_ddr4_s_axi_ctrl_rdata"), c0_ddr4_s_axi_ctrl_rresp("c0_ddr4_s_axi_ctrl_rresp"), c0_ddr4_interrupt("c0_ddr4_interrupt"), c0_ddr4_s_axi_awid("c0_ddr4_s_axi_awid"), c0_ddr4_s_axi_awaddr("c0_ddr4_s_axi_awaddr"), c0_ddr4_s_axi_awlen("c0_ddr4_s_axi_awlen"), c0_ddr4_s_axi_awsize("c0_ddr4_s_axi_awsize"), c0_ddr4_s_axi_awburst("c0_ddr4_s_axi_awburst"), c0_ddr4_s_axi_awlock("c0_ddr4_s_axi_awlock"), c0_ddr4_s_axi_awcache("c0_ddr4_s_axi_awcache"), c0_ddr4_s_axi_awprot("c0_ddr4_s_axi_awprot"), c0_ddr4_s_axi_awqos("c0_ddr4_s_axi_awqos"), c0_ddr4_s_axi_awvalid("c0_ddr4_s_axi_awvalid"), c0_ddr4_s_axi_awready("c0_ddr4_s_axi_awready"), c0_ddr4_s_axi_wdata("c0_ddr4_s_axi_wdata"), c0_ddr4_s_axi_wstrb("c0_ddr4_s_axi_wstrb"), c0_ddr4_s_axi_wlast("c0_ddr4_s_axi_wlast"), c0_ddr4_s_axi_wvalid("c0_ddr4_s_axi_wvalid"), c0_ddr4_s_axi_wready("c0_ddr4_s_axi_wready"), c0_ddr4_s_axi_bready("c0_ddr4_s_axi_bready"), c0_ddr4_s_axi_bid("c0_ddr4_s_axi_bid"), c0_ddr4_s_axi_bresp("c0_ddr4_s_axi_bresp"), c0_ddr4_s_axi_bvalid("c0_ddr4_s_axi_bvalid"), c0_ddr4_s_axi_arid("c0_ddr4_s_axi_arid"), c0_ddr4_s_axi_araddr("c0_ddr4_s_axi_araddr"), c0_ddr4_s_axi_arlen("c0_ddr4_s_axi_arlen"), c0_ddr4_s_axi_arsize("c0_ddr4_s_axi_arsize"), c0_ddr4_s_axi_arburst("c0_ddr4_s_axi_arburst"), c0_ddr4_s_axi_arlock("c0_ddr4_s_axi_arlock"), c0_ddr4_s_axi_arcache("c0_ddr4_s_axi_arcache"), c0_ddr4_s_axi_arprot("c0_ddr4_s_axi_arprot"), c0_ddr4_s_axi_arqos("c0_ddr4_s_axi_arqos"), c0_ddr4_s_axi_arvalid("c0_ddr4_s_axi_arvalid"), c0_ddr4_s_axi_arready("c0_ddr4_s_axi_arready"), c0_ddr4_s_axi_rready("c0_ddr4_s_axi_rready"), c0_ddr4_s_axi_rlast("c0_ddr4_s_axi_rlast"), c0_ddr4_s_axi_rvalid("c0_ddr4_s_axi_rvalid"), c0_ddr4_s_axi_rresp("c0_ddr4_s_axi_rresp"), c0_ddr4_s_axi_rid("c0_ddr4_s_axi_rid"), c0_ddr4_s_axi_rdata("c0_ddr4_s_axi_rdata"), c0_ddr4_s_axi_aruser("c0_ddr4_s_axi_aruser"), c0_ddr4_s_axi_awuser("c0_ddr4_s_axi_awuser"), sys_rst("sys_rst")
{

  // initialize pins
  mp_impl->c0_init_calib_complete(c0_init_calib_complete);
  mp_impl->dbg_clk(dbg_clk);
  mp_impl->c0_sys_clk_p(c0_sys_clk_p);
  mp_impl->c0_sys_clk_n(c0_sys_clk_n);
  mp_impl->dbg_bus(dbg_bus);
  mp_impl->c0_ddr4_adr(c0_ddr4_adr);
  mp_impl->c0_ddr4_ba(c0_ddr4_ba);
  mp_impl->c0_ddr4_cke(c0_ddr4_cke);
  mp_impl->c0_ddr4_cs_n(c0_ddr4_cs_n);
  mp_impl->c0_ddr4_dq(c0_ddr4_dq);
  mp_impl->c0_ddr4_dqs_c(c0_ddr4_dqs_c);
  mp_impl->c0_ddr4_dqs_t(c0_ddr4_dqs_t);
  mp_impl->c0_ddr4_odt(c0_ddr4_odt);
  mp_impl->c0_ddr4_parity(c0_ddr4_parity);
  mp_impl->c0_ddr4_bg(c0_ddr4_bg);
  mp_impl->c0_ddr4_reset_n(c0_ddr4_reset_n);
  mp_impl->c0_ddr4_act_n(c0_ddr4_act_n);
  mp_impl->c0_ddr4_ck_c(c0_ddr4_ck_c);
  mp_impl->c0_ddr4_ck_t(c0_ddr4_ck_t);
  mp_impl->c0_ddr4_ui_clk(c0_ddr4_ui_clk);
  mp_impl->c0_ddr4_ui_clk_sync_rst(c0_ddr4_ui_clk_sync_rst);
  mp_impl->c0_ddr4_app_sref_req(c0_ddr4_app_sref_req);
  mp_impl->c0_ddr4_app_sref_ack(c0_ddr4_app_sref_ack);
  mp_impl->c0_ddr4_app_restore_en(c0_ddr4_app_restore_en);
  mp_impl->c0_ddr4_app_restore_complete(c0_ddr4_app_restore_complete);
  mp_impl->c0_ddr4_app_mem_init_skip(c0_ddr4_app_mem_init_skip);
  mp_impl->c0_ddr4_app_xsdb_select(c0_ddr4_app_xsdb_select);
  mp_impl->c0_ddr4_app_xsdb_rd_en(c0_ddr4_app_xsdb_rd_en);
  mp_impl->c0_ddr4_app_xsdb_wr_en(c0_ddr4_app_xsdb_wr_en);
  mp_impl->c0_ddr4_app_xsdb_addr(c0_ddr4_app_xsdb_addr);
  mp_impl->c0_ddr4_app_xsdb_wr_data(c0_ddr4_app_xsdb_wr_data);
  mp_impl->c0_ddr4_app_xsdb_rd_data(c0_ddr4_app_xsdb_rd_data);
  mp_impl->c0_ddr4_app_xsdb_rdy(c0_ddr4_app_xsdb_rdy);
  mp_impl->c0_ddr4_app_dbg_out(c0_ddr4_app_dbg_out);
  mp_impl->c0_ddr4_aresetn(c0_ddr4_aresetn);
  mp_impl->c0_ddr4_interrupt(c0_ddr4_interrupt);
  mp_impl->sys_rst(sys_rst);

  // initialize transactors
  mp_C0_DDR4_S_AXI_CTRL_transactor = NULL;
  mp_C0_DDR4_S_AXI_transactor = NULL;
  mp_c0_ddr4_s_axi_arlock_converter = NULL;
  mp_c0_ddr4_s_axi_aruser_converter = NULL;
  mp_c0_ddr4_s_axi_awlock_converter = NULL;
  mp_c0_ddr4_s_axi_awuser_converter = NULL;

  // initialize socket stubs

}

void cl_ddr4_32g_ap::before_end_of_elaboration()
{
  // configure 'C0_DDR4_S_AXI_CTRL' transactor

  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_ddr4_32g_ap", "C0_DDR4_S_AXI_CTRL_TLM_MODE") != 1)
  {
    // Instantiate Socket Stubs

  // 'C0_DDR4_S_AXI_CTRL' transactor parameters
    xsc::common_cpp::properties C0_DDR4_S_AXI_CTRL_transactor_param_props;
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("DATA_WIDTH", "32");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("ID_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("ADDR_WIDTH", "32");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("WUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("RUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("BUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_BURST", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_LOCK", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_PROT", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_CACHE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_QOS", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_REGION", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_WSTRB", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_BRESP", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_RRESP", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_SIZE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_RESET", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addFloat("FREQ_HZ", "2.665e+08");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addFloat("PHASE", "0.0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_C0_DDR4_S_AXI_CTRL_transactor = new xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>("C0_DDR4_S_AXI_CTRL_transactor", C0_DDR4_S_AXI_CTRL_transactor_param_props);

    // C0_DDR4_S_AXI_CTRL' transactor ports

    mp_C0_DDR4_S_AXI_CTRL_transactor->ARADDR(c0_ddr4_s_axi_ctrl_araddr);
    mp_C0_DDR4_S_AXI_CTRL_transactor->ARREADY(c0_ddr4_s_axi_ctrl_arready);
    mp_C0_DDR4_S_AXI_CTRL_transactor->ARVALID(c0_ddr4_s_axi_ctrl_arvalid);
    mp_C0_DDR4_S_AXI_CTRL_transactor->AWADDR(c0_ddr4_s_axi_ctrl_awaddr);
    mp_C0_DDR4_S_AXI_CTRL_transactor->AWREADY(c0_ddr4_s_axi_ctrl_awready);
    mp_C0_DDR4_S_AXI_CTRL_transactor->AWVALID(c0_ddr4_s_axi_ctrl_awvalid);
    mp_C0_DDR4_S_AXI_CTRL_transactor->BREADY(c0_ddr4_s_axi_ctrl_bready);
    mp_C0_DDR4_S_AXI_CTRL_transactor->BRESP(c0_ddr4_s_axi_ctrl_bresp);
    mp_C0_DDR4_S_AXI_CTRL_transactor->BVALID(c0_ddr4_s_axi_ctrl_bvalid);
    mp_C0_DDR4_S_AXI_CTRL_transactor->RDATA(c0_ddr4_s_axi_ctrl_rdata);
    mp_C0_DDR4_S_AXI_CTRL_transactor->RREADY(c0_ddr4_s_axi_ctrl_rready);
    mp_C0_DDR4_S_AXI_CTRL_transactor->RRESP(c0_ddr4_s_axi_ctrl_rresp);
    mp_C0_DDR4_S_AXI_CTRL_transactor->RVALID(c0_ddr4_s_axi_ctrl_rvalid);
    mp_C0_DDR4_S_AXI_CTRL_transactor->WDATA(c0_ddr4_s_axi_ctrl_wdata);
    mp_C0_DDR4_S_AXI_CTRL_transactor->WREADY(c0_ddr4_s_axi_ctrl_wready);
    mp_C0_DDR4_S_AXI_CTRL_transactor->WVALID(c0_ddr4_s_axi_ctrl_wvalid);
    mp_C0_DDR4_S_AXI_CTRL_transactor->CLK(c0_ddr4_ui_clk);
    mp_C0_DDR4_S_AXI_CTRL_transactor->RST(c0_ddr4_aresetn);

    // C0_DDR4_S_AXI_CTRL' transactor sockets

    mp_impl->C0_DDR_SAXI_CTRL_rd_socket->bind(*(mp_C0_DDR4_S_AXI_CTRL_transactor->rd_socket));
    mp_impl->C0_DDR_SAXI_CTRL_wr_socket->bind(*(mp_C0_DDR4_S_AXI_CTRL_transactor->wr_socket));
  }
  else
  {
  }

  // configure 'C0_DDR4_S_AXI' transactor

  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_ddr4_32g_ap", "C0_DDR4_S_AXI_TLM_MODE") != 1)
  {
    // Instantiate Socket Stubs

  // 'C0_DDR4_S_AXI' transactor parameters
    xsc::common_cpp::properties C0_DDR4_S_AXI_transactor_param_props;
    C0_DDR4_S_AXI_transactor_param_props.addLong("DATA_WIDTH", "512");
    C0_DDR4_S_AXI_transactor_param_props.addLong("ID_WIDTH", "16");
    C0_DDR4_S_AXI_transactor_param_props.addLong("ADDR_WIDTH", "35");
    C0_DDR4_S_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_BURST", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_LOCK", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_CACHE", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_QOS", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "2");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "2");
    C0_DDR4_S_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "256");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_SIZE", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    C0_DDR4_S_AXI_transactor_param_props.addFloat("FREQ_HZ", "2.665e+08");
    C0_DDR4_S_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    C0_DDR4_S_AXI_transactor_param_props.addString("PROTOCOL", "AXI4");
    C0_DDR4_S_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    C0_DDR4_S_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_C0_DDR4_S_AXI_transactor = new xtlm::xaximm_pin2xtlm_t<512,35,16,1,1,1,1,1>("C0_DDR4_S_AXI_transactor", C0_DDR4_S_AXI_transactor_param_props);

    // C0_DDR4_S_AXI' transactor ports

    mp_C0_DDR4_S_AXI_transactor->ARADDR(c0_ddr4_s_axi_araddr);
    mp_C0_DDR4_S_AXI_transactor->ARBURST(c0_ddr4_s_axi_arburst);
    mp_C0_DDR4_S_AXI_transactor->ARCACHE(c0_ddr4_s_axi_arcache);
    mp_C0_DDR4_S_AXI_transactor->ARID(c0_ddr4_s_axi_arid);
    mp_C0_DDR4_S_AXI_transactor->ARLEN(c0_ddr4_s_axi_arlen);
    mp_c0_ddr4_s_axi_arlock_converter = new xsc::common::vectorN2scalar_converter<1>("c0_ddr4_s_axi_arlock_converter");
    mp_c0_ddr4_s_axi_arlock_converter->vector_in(c0_ddr4_s_axi_arlock);
    mp_c0_ddr4_s_axi_arlock_converter->scalar_out(m_c0_ddr4_s_axi_arlock_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->ARLOCK(m_c0_ddr4_s_axi_arlock_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->ARPROT(c0_ddr4_s_axi_arprot);
    mp_C0_DDR4_S_AXI_transactor->ARQOS(c0_ddr4_s_axi_arqos);
    mp_C0_DDR4_S_AXI_transactor->ARREADY(c0_ddr4_s_axi_arready);
    mp_C0_DDR4_S_AXI_transactor->ARSIZE(c0_ddr4_s_axi_arsize);
    mp_c0_ddr4_s_axi_aruser_converter = new xsc::common::scalar2vectorN_converter<1>("c0_ddr4_s_axi_aruser_converter");
    mp_c0_ddr4_s_axi_aruser_converter->scalar_in(c0_ddr4_s_axi_aruser);
    mp_c0_ddr4_s_axi_aruser_converter->vector_out(m_c0_ddr4_s_axi_aruser_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->ARUSER(m_c0_ddr4_s_axi_aruser_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->ARVALID(c0_ddr4_s_axi_arvalid);
    mp_C0_DDR4_S_AXI_transactor->AWADDR(c0_ddr4_s_axi_awaddr);
    mp_C0_DDR4_S_AXI_transactor->AWBURST(c0_ddr4_s_axi_awburst);
    mp_C0_DDR4_S_AXI_transactor->AWCACHE(c0_ddr4_s_axi_awcache);
    mp_C0_DDR4_S_AXI_transactor->AWID(c0_ddr4_s_axi_awid);
    mp_C0_DDR4_S_AXI_transactor->AWLEN(c0_ddr4_s_axi_awlen);
    mp_c0_ddr4_s_axi_awlock_converter = new xsc::common::vectorN2scalar_converter<1>("c0_ddr4_s_axi_awlock_converter");
    mp_c0_ddr4_s_axi_awlock_converter->vector_in(c0_ddr4_s_axi_awlock);
    mp_c0_ddr4_s_axi_awlock_converter->scalar_out(m_c0_ddr4_s_axi_awlock_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->AWLOCK(m_c0_ddr4_s_axi_awlock_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->AWPROT(c0_ddr4_s_axi_awprot);
    mp_C0_DDR4_S_AXI_transactor->AWQOS(c0_ddr4_s_axi_awqos);
    mp_C0_DDR4_S_AXI_transactor->AWREADY(c0_ddr4_s_axi_awready);
    mp_C0_DDR4_S_AXI_transactor->AWSIZE(c0_ddr4_s_axi_awsize);
    mp_c0_ddr4_s_axi_awuser_converter = new xsc::common::scalar2vectorN_converter<1>("c0_ddr4_s_axi_awuser_converter");
    mp_c0_ddr4_s_axi_awuser_converter->scalar_in(c0_ddr4_s_axi_awuser);
    mp_c0_ddr4_s_axi_awuser_converter->vector_out(m_c0_ddr4_s_axi_awuser_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->AWUSER(m_c0_ddr4_s_axi_awuser_converter_signal);
    mp_C0_DDR4_S_AXI_transactor->AWVALID(c0_ddr4_s_axi_awvalid);
    mp_C0_DDR4_S_AXI_transactor->BID(c0_ddr4_s_axi_bid);
    mp_C0_DDR4_S_AXI_transactor->BREADY(c0_ddr4_s_axi_bready);
    mp_C0_DDR4_S_AXI_transactor->BRESP(c0_ddr4_s_axi_bresp);
    mp_C0_DDR4_S_AXI_transactor->BVALID(c0_ddr4_s_axi_bvalid);
    mp_C0_DDR4_S_AXI_transactor->RDATA(c0_ddr4_s_axi_rdata);
    mp_C0_DDR4_S_AXI_transactor->RID(c0_ddr4_s_axi_rid);
    mp_C0_DDR4_S_AXI_transactor->RLAST(c0_ddr4_s_axi_rlast);
    mp_C0_DDR4_S_AXI_transactor->RREADY(c0_ddr4_s_axi_rready);
    mp_C0_DDR4_S_AXI_transactor->RRESP(c0_ddr4_s_axi_rresp);
    mp_C0_DDR4_S_AXI_transactor->RVALID(c0_ddr4_s_axi_rvalid);
    mp_C0_DDR4_S_AXI_transactor->WDATA(c0_ddr4_s_axi_wdata);
    mp_C0_DDR4_S_AXI_transactor->WLAST(c0_ddr4_s_axi_wlast);
    mp_C0_DDR4_S_AXI_transactor->WREADY(c0_ddr4_s_axi_wready);
    mp_C0_DDR4_S_AXI_transactor->WSTRB(c0_ddr4_s_axi_wstrb);
    mp_C0_DDR4_S_AXI_transactor->WVALID(c0_ddr4_s_axi_wvalid);
    mp_C0_DDR4_S_AXI_transactor->CLK(c0_ddr4_ui_clk);
    mp_C0_DDR4_S_AXI_transactor->RST(c0_ddr4_aresetn);

    // C0_DDR4_S_AXI' transactor sockets

    mp_impl->C0_DDR_SAXI_rd_socket->bind(*(mp_C0_DDR4_S_AXI_transactor->rd_socket));
    mp_impl->C0_DDR_SAXI_wr_socket->bind(*(mp_C0_DDR4_S_AXI_transactor->wr_socket));
  }
  else
  {
  }

}

#endif // RIVIERA




#ifdef VCSSYSTEMC
cl_ddr4_32g_ap::cl_ddr4_32g_ap(const sc_core::sc_module_name& nm) : cl_ddr4_32g_ap_sc(nm),  c0_init_calib_complete("c0_init_calib_complete"), dbg_clk("dbg_clk"), c0_sys_clk_p("c0_sys_clk_p"), c0_sys_clk_n("c0_sys_clk_n"), dbg_bus("dbg_bus"), c0_ddr4_adr("c0_ddr4_adr"), c0_ddr4_ba("c0_ddr4_ba"), c0_ddr4_cke("c0_ddr4_cke"), c0_ddr4_cs_n("c0_ddr4_cs_n"), c0_ddr4_dq("c0_ddr4_dq"), c0_ddr4_dqs_c("c0_ddr4_dqs_c"), c0_ddr4_dqs_t("c0_ddr4_dqs_t"), c0_ddr4_odt("c0_ddr4_odt"), c0_ddr4_parity("c0_ddr4_parity"), c0_ddr4_bg("c0_ddr4_bg"), c0_ddr4_reset_n("c0_ddr4_reset_n"), c0_ddr4_act_n("c0_ddr4_act_n"), c0_ddr4_ck_c("c0_ddr4_ck_c"), c0_ddr4_ck_t("c0_ddr4_ck_t"), c0_ddr4_ui_clk("c0_ddr4_ui_clk"), c0_ddr4_ui_clk_sync_rst("c0_ddr4_ui_clk_sync_rst"), c0_ddr4_app_sref_req("c0_ddr4_app_sref_req"), c0_ddr4_app_sref_ack("c0_ddr4_app_sref_ack"), c0_ddr4_app_restore_en("c0_ddr4_app_restore_en"), c0_ddr4_app_restore_complete("c0_ddr4_app_restore_complete"), c0_ddr4_app_mem_init_skip("c0_ddr4_app_mem_init_skip"), c0_ddr4_app_xsdb_select("c0_ddr4_app_xsdb_select"), c0_ddr4_app_xsdb_rd_en("c0_ddr4_app_xsdb_rd_en"), c0_ddr4_app_xsdb_wr_en("c0_ddr4_app_xsdb_wr_en"), c0_ddr4_app_xsdb_addr("c0_ddr4_app_xsdb_addr"), c0_ddr4_app_xsdb_wr_data("c0_ddr4_app_xsdb_wr_data"), c0_ddr4_app_xsdb_rd_data("c0_ddr4_app_xsdb_rd_data"), c0_ddr4_app_xsdb_rdy("c0_ddr4_app_xsdb_rdy"), c0_ddr4_app_dbg_out("c0_ddr4_app_dbg_out"), c0_ddr4_aresetn("c0_ddr4_aresetn"), c0_ddr4_s_axi_ctrl_awvalid("c0_ddr4_s_axi_ctrl_awvalid"), c0_ddr4_s_axi_ctrl_awready("c0_ddr4_s_axi_ctrl_awready"), c0_ddr4_s_axi_ctrl_awaddr("c0_ddr4_s_axi_ctrl_awaddr"), c0_ddr4_s_axi_ctrl_wvalid("c0_ddr4_s_axi_ctrl_wvalid"), c0_ddr4_s_axi_ctrl_wready("c0_ddr4_s_axi_ctrl_wready"), c0_ddr4_s_axi_ctrl_wdata("c0_ddr4_s_axi_ctrl_wdata"), c0_ddr4_s_axi_ctrl_bvalid("c0_ddr4_s_axi_ctrl_bvalid"), c0_ddr4_s_axi_ctrl_bready("c0_ddr4_s_axi_ctrl_bready"), c0_ddr4_s_axi_ctrl_bresp("c0_ddr4_s_axi_ctrl_bresp"), c0_ddr4_s_axi_ctrl_arvalid("c0_ddr4_s_axi_ctrl_arvalid"), c0_ddr4_s_axi_ctrl_arready("c0_ddr4_s_axi_ctrl_arready"), c0_ddr4_s_axi_ctrl_araddr("c0_ddr4_s_axi_ctrl_araddr"), c0_ddr4_s_axi_ctrl_rvalid("c0_ddr4_s_axi_ctrl_rvalid"), c0_ddr4_s_axi_ctrl_rready("c0_ddr4_s_axi_ctrl_rready"), c0_ddr4_s_axi_ctrl_rdata("c0_ddr4_s_axi_ctrl_rdata"), c0_ddr4_s_axi_ctrl_rresp("c0_ddr4_s_axi_ctrl_rresp"), c0_ddr4_interrupt("c0_ddr4_interrupt"), c0_ddr4_s_axi_awid("c0_ddr4_s_axi_awid"), c0_ddr4_s_axi_awaddr("c0_ddr4_s_axi_awaddr"), c0_ddr4_s_axi_awlen("c0_ddr4_s_axi_awlen"), c0_ddr4_s_axi_awsize("c0_ddr4_s_axi_awsize"), c0_ddr4_s_axi_awburst("c0_ddr4_s_axi_awburst"), c0_ddr4_s_axi_awlock("c0_ddr4_s_axi_awlock"), c0_ddr4_s_axi_awcache("c0_ddr4_s_axi_awcache"), c0_ddr4_s_axi_awprot("c0_ddr4_s_axi_awprot"), c0_ddr4_s_axi_awqos("c0_ddr4_s_axi_awqos"), c0_ddr4_s_axi_awvalid("c0_ddr4_s_axi_awvalid"), c0_ddr4_s_axi_awready("c0_ddr4_s_axi_awready"), c0_ddr4_s_axi_wdata("c0_ddr4_s_axi_wdata"), c0_ddr4_s_axi_wstrb("c0_ddr4_s_axi_wstrb"), c0_ddr4_s_axi_wlast("c0_ddr4_s_axi_wlast"), c0_ddr4_s_axi_wvalid("c0_ddr4_s_axi_wvalid"), c0_ddr4_s_axi_wready("c0_ddr4_s_axi_wready"), c0_ddr4_s_axi_bready("c0_ddr4_s_axi_bready"), c0_ddr4_s_axi_bid("c0_ddr4_s_axi_bid"), c0_ddr4_s_axi_bresp("c0_ddr4_s_axi_bresp"), c0_ddr4_s_axi_bvalid("c0_ddr4_s_axi_bvalid"), c0_ddr4_s_axi_arid("c0_ddr4_s_axi_arid"), c0_ddr4_s_axi_araddr("c0_ddr4_s_axi_araddr"), c0_ddr4_s_axi_arlen("c0_ddr4_s_axi_arlen"), c0_ddr4_s_axi_arsize("c0_ddr4_s_axi_arsize"), c0_ddr4_s_axi_arburst("c0_ddr4_s_axi_arburst"), c0_ddr4_s_axi_arlock("c0_ddr4_s_axi_arlock"), c0_ddr4_s_axi_arcache("c0_ddr4_s_axi_arcache"), c0_ddr4_s_axi_arprot("c0_ddr4_s_axi_arprot"), c0_ddr4_s_axi_arqos("c0_ddr4_s_axi_arqos"), c0_ddr4_s_axi_arvalid("c0_ddr4_s_axi_arvalid"), c0_ddr4_s_axi_arready("c0_ddr4_s_axi_arready"), c0_ddr4_s_axi_rready("c0_ddr4_s_axi_rready"), c0_ddr4_s_axi_rlast("c0_ddr4_s_axi_rlast"), c0_ddr4_s_axi_rvalid("c0_ddr4_s_axi_rvalid"), c0_ddr4_s_axi_rresp("c0_ddr4_s_axi_rresp"), c0_ddr4_s_axi_rid("c0_ddr4_s_axi_rid"), c0_ddr4_s_axi_rdata("c0_ddr4_s_axi_rdata"), c0_ddr4_s_axi_aruser("c0_ddr4_s_axi_aruser"), c0_ddr4_s_axi_awuser("c0_ddr4_s_axi_awuser"), sys_rst("sys_rst")
{
  // initialize pins
  mp_impl->c0_init_calib_complete(c0_init_calib_complete);
  mp_impl->dbg_clk(dbg_clk);
  mp_impl->c0_sys_clk_p(c0_sys_clk_p);
  mp_impl->c0_sys_clk_n(c0_sys_clk_n);
  mp_impl->dbg_bus(dbg_bus);
  mp_impl->c0_ddr4_adr(c0_ddr4_adr);
  mp_impl->c0_ddr4_ba(c0_ddr4_ba);
  mp_impl->c0_ddr4_cke(c0_ddr4_cke);
  mp_impl->c0_ddr4_cs_n(c0_ddr4_cs_n);
  mp_impl->c0_ddr4_dq(c0_ddr4_dq);
  mp_impl->c0_ddr4_dqs_c(c0_ddr4_dqs_c);
  mp_impl->c0_ddr4_dqs_t(c0_ddr4_dqs_t);
  mp_impl->c0_ddr4_odt(c0_ddr4_odt);
  mp_impl->c0_ddr4_parity(c0_ddr4_parity);
  mp_impl->c0_ddr4_bg(c0_ddr4_bg);
  mp_impl->c0_ddr4_reset_n(c0_ddr4_reset_n);
  mp_impl->c0_ddr4_act_n(c0_ddr4_act_n);
  mp_impl->c0_ddr4_ck_c(c0_ddr4_ck_c);
  mp_impl->c0_ddr4_ck_t(c0_ddr4_ck_t);
  mp_impl->c0_ddr4_ui_clk(c0_ddr4_ui_clk);
  mp_impl->c0_ddr4_ui_clk_sync_rst(c0_ddr4_ui_clk_sync_rst);
  mp_impl->c0_ddr4_app_sref_req(c0_ddr4_app_sref_req);
  mp_impl->c0_ddr4_app_sref_ack(c0_ddr4_app_sref_ack);
  mp_impl->c0_ddr4_app_restore_en(c0_ddr4_app_restore_en);
  mp_impl->c0_ddr4_app_restore_complete(c0_ddr4_app_restore_complete);
  mp_impl->c0_ddr4_app_mem_init_skip(c0_ddr4_app_mem_init_skip);
  mp_impl->c0_ddr4_app_xsdb_select(c0_ddr4_app_xsdb_select);
  mp_impl->c0_ddr4_app_xsdb_rd_en(c0_ddr4_app_xsdb_rd_en);
  mp_impl->c0_ddr4_app_xsdb_wr_en(c0_ddr4_app_xsdb_wr_en);
  mp_impl->c0_ddr4_app_xsdb_addr(c0_ddr4_app_xsdb_addr);
  mp_impl->c0_ddr4_app_xsdb_wr_data(c0_ddr4_app_xsdb_wr_data);
  mp_impl->c0_ddr4_app_xsdb_rd_data(c0_ddr4_app_xsdb_rd_data);
  mp_impl->c0_ddr4_app_xsdb_rdy(c0_ddr4_app_xsdb_rdy);
  mp_impl->c0_ddr4_app_dbg_out(c0_ddr4_app_dbg_out);
  mp_impl->c0_ddr4_aresetn(c0_ddr4_aresetn);
  mp_impl->c0_ddr4_interrupt(c0_ddr4_interrupt);
  mp_impl->sys_rst(sys_rst);

  // initialize transactors
  mp_C0_DDR4_S_AXI_CTRL_transactor = NULL;
  mp_C0_DDR4_S_AXI_transactor = NULL;
  mp_c0_ddr4_s_axi_arlock_converter = NULL;
  mp_c0_ddr4_s_axi_aruser_converter = NULL;
  mp_c0_ddr4_s_axi_awlock_converter = NULL;
  mp_c0_ddr4_s_axi_awuser_converter = NULL;

  // Instantiate Socket Stubs

  // configure C0_DDR4_S_AXI_CTRL_transactor
    xsc::common_cpp::properties C0_DDR4_S_AXI_CTRL_transactor_param_props;
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("DATA_WIDTH", "32");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("ID_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("ADDR_WIDTH", "32");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("WUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("RUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("BUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_BURST", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_LOCK", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_PROT", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_CACHE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_QOS", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_REGION", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_WSTRB", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_BRESP", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_RRESP", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_SIZE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_RESET", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addFloat("FREQ_HZ", "2.665e+08");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addFloat("PHASE", "0.0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_C0_DDR4_S_AXI_CTRL_transactor = new xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>("C0_DDR4_S_AXI_CTRL_transactor", C0_DDR4_S_AXI_CTRL_transactor_param_props);
  mp_C0_DDR4_S_AXI_CTRL_transactor->ARADDR(c0_ddr4_s_axi_ctrl_araddr);
  mp_C0_DDR4_S_AXI_CTRL_transactor->ARREADY(c0_ddr4_s_axi_ctrl_arready);
  mp_C0_DDR4_S_AXI_CTRL_transactor->ARVALID(c0_ddr4_s_axi_ctrl_arvalid);
  mp_C0_DDR4_S_AXI_CTRL_transactor->AWADDR(c0_ddr4_s_axi_ctrl_awaddr);
  mp_C0_DDR4_S_AXI_CTRL_transactor->AWREADY(c0_ddr4_s_axi_ctrl_awready);
  mp_C0_DDR4_S_AXI_CTRL_transactor->AWVALID(c0_ddr4_s_axi_ctrl_awvalid);
  mp_C0_DDR4_S_AXI_CTRL_transactor->BREADY(c0_ddr4_s_axi_ctrl_bready);
  mp_C0_DDR4_S_AXI_CTRL_transactor->BRESP(c0_ddr4_s_axi_ctrl_bresp);
  mp_C0_DDR4_S_AXI_CTRL_transactor->BVALID(c0_ddr4_s_axi_ctrl_bvalid);
  mp_C0_DDR4_S_AXI_CTRL_transactor->RDATA(c0_ddr4_s_axi_ctrl_rdata);
  mp_C0_DDR4_S_AXI_CTRL_transactor->RREADY(c0_ddr4_s_axi_ctrl_rready);
  mp_C0_DDR4_S_AXI_CTRL_transactor->RRESP(c0_ddr4_s_axi_ctrl_rresp);
  mp_C0_DDR4_S_AXI_CTRL_transactor->RVALID(c0_ddr4_s_axi_ctrl_rvalid);
  mp_C0_DDR4_S_AXI_CTRL_transactor->WDATA(c0_ddr4_s_axi_ctrl_wdata);
  mp_C0_DDR4_S_AXI_CTRL_transactor->WREADY(c0_ddr4_s_axi_ctrl_wready);
  mp_C0_DDR4_S_AXI_CTRL_transactor->WVALID(c0_ddr4_s_axi_ctrl_wvalid);
  mp_C0_DDR4_S_AXI_CTRL_transactor->CLK(c0_ddr4_ui_clk);
  mp_C0_DDR4_S_AXI_CTRL_transactor->RST(c0_ddr4_aresetn);
  // configure C0_DDR4_S_AXI_transactor
    xsc::common_cpp::properties C0_DDR4_S_AXI_transactor_param_props;
    C0_DDR4_S_AXI_transactor_param_props.addLong("DATA_WIDTH", "512");
    C0_DDR4_S_AXI_transactor_param_props.addLong("ID_WIDTH", "16");
    C0_DDR4_S_AXI_transactor_param_props.addLong("ADDR_WIDTH", "35");
    C0_DDR4_S_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_BURST", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_LOCK", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_CACHE", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_QOS", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "2");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "2");
    C0_DDR4_S_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "256");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_SIZE", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    C0_DDR4_S_AXI_transactor_param_props.addFloat("FREQ_HZ", "2.665e+08");
    C0_DDR4_S_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    C0_DDR4_S_AXI_transactor_param_props.addString("PROTOCOL", "AXI4");
    C0_DDR4_S_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    C0_DDR4_S_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_C0_DDR4_S_AXI_transactor = new xtlm::xaximm_pin2xtlm_t<512,35,16,1,1,1,1,1>("C0_DDR4_S_AXI_transactor", C0_DDR4_S_AXI_transactor_param_props);
  mp_C0_DDR4_S_AXI_transactor->ARADDR(c0_ddr4_s_axi_araddr);
  mp_C0_DDR4_S_AXI_transactor->ARBURST(c0_ddr4_s_axi_arburst);
  mp_C0_DDR4_S_AXI_transactor->ARCACHE(c0_ddr4_s_axi_arcache);
  mp_C0_DDR4_S_AXI_transactor->ARID(c0_ddr4_s_axi_arid);
  mp_C0_DDR4_S_AXI_transactor->ARLEN(c0_ddr4_s_axi_arlen);
  mp_c0_ddr4_s_axi_arlock_converter = new xsc::common::vectorN2scalar_converter<1>("c0_ddr4_s_axi_arlock_converter");
  mp_c0_ddr4_s_axi_arlock_converter->vector_in(c0_ddr4_s_axi_arlock);
  mp_c0_ddr4_s_axi_arlock_converter->scalar_out(m_c0_ddr4_s_axi_arlock_converter_signal);
  mp_C0_DDR4_S_AXI_transactor->ARLOCK(m_c0_ddr4_s_axi_arlock_converter_signal);
  mp_C0_DDR4_S_AXI_transactor->ARPROT(c0_ddr4_s_axi_arprot);
  mp_C0_DDR4_S_AXI_transactor->ARQOS(c0_ddr4_s_axi_arqos);
  mp_C0_DDR4_S_AXI_transactor->ARREADY(c0_ddr4_s_axi_arready);
  mp_C0_DDR4_S_AXI_transactor->ARSIZE(c0_ddr4_s_axi_arsize);
  mp_c0_ddr4_s_axi_aruser_converter = new xsc::common::scalar2vectorN_converter<1>("c0_ddr4_s_axi_aruser_converter");
  mp_c0_ddr4_s_axi_aruser_converter->scalar_in(c0_ddr4_s_axi_aruser);
  mp_c0_ddr4_s_axi_aruser_converter->vector_out(m_c0_ddr4_s_axi_aruser_converter_signal);
  mp_C0_DDR4_S_AXI_transactor->ARUSER(m_c0_ddr4_s_axi_aruser_converter_signal);
  mp_C0_DDR4_S_AXI_transactor->ARVALID(c0_ddr4_s_axi_arvalid);
  mp_C0_DDR4_S_AXI_transactor->AWADDR(c0_ddr4_s_axi_awaddr);
  mp_C0_DDR4_S_AXI_transactor->AWBURST(c0_ddr4_s_axi_awburst);
  mp_C0_DDR4_S_AXI_transactor->AWCACHE(c0_ddr4_s_axi_awcache);
  mp_C0_DDR4_S_AXI_transactor->AWID(c0_ddr4_s_axi_awid);
  mp_C0_DDR4_S_AXI_transactor->AWLEN(c0_ddr4_s_axi_awlen);
  mp_c0_ddr4_s_axi_awlock_converter = new xsc::common::vectorN2scalar_converter<1>("c0_ddr4_s_axi_awlock_converter");
  mp_c0_ddr4_s_axi_awlock_converter->vector_in(c0_ddr4_s_axi_awlock);
  mp_c0_ddr4_s_axi_awlock_converter->scalar_out(m_c0_ddr4_s_axi_awlock_converter_signal);
  mp_C0_DDR4_S_AXI_transactor->AWLOCK(m_c0_ddr4_s_axi_awlock_converter_signal);
  mp_C0_DDR4_S_AXI_transactor->AWPROT(c0_ddr4_s_axi_awprot);
  mp_C0_DDR4_S_AXI_transactor->AWQOS(c0_ddr4_s_axi_awqos);
  mp_C0_DDR4_S_AXI_transactor->AWREADY(c0_ddr4_s_axi_awready);
  mp_C0_DDR4_S_AXI_transactor->AWSIZE(c0_ddr4_s_axi_awsize);
  mp_c0_ddr4_s_axi_awuser_converter = new xsc::common::scalar2vectorN_converter<1>("c0_ddr4_s_axi_awuser_converter");
  mp_c0_ddr4_s_axi_awuser_converter->scalar_in(c0_ddr4_s_axi_awuser);
  mp_c0_ddr4_s_axi_awuser_converter->vector_out(m_c0_ddr4_s_axi_awuser_converter_signal);
  mp_C0_DDR4_S_AXI_transactor->AWUSER(m_c0_ddr4_s_axi_awuser_converter_signal);
  mp_C0_DDR4_S_AXI_transactor->AWVALID(c0_ddr4_s_axi_awvalid);
  mp_C0_DDR4_S_AXI_transactor->BID(c0_ddr4_s_axi_bid);
  mp_C0_DDR4_S_AXI_transactor->BREADY(c0_ddr4_s_axi_bready);
  mp_C0_DDR4_S_AXI_transactor->BRESP(c0_ddr4_s_axi_bresp);
  mp_C0_DDR4_S_AXI_transactor->BVALID(c0_ddr4_s_axi_bvalid);
  mp_C0_DDR4_S_AXI_transactor->RDATA(c0_ddr4_s_axi_rdata);
  mp_C0_DDR4_S_AXI_transactor->RID(c0_ddr4_s_axi_rid);
  mp_C0_DDR4_S_AXI_transactor->RLAST(c0_ddr4_s_axi_rlast);
  mp_C0_DDR4_S_AXI_transactor->RREADY(c0_ddr4_s_axi_rready);
  mp_C0_DDR4_S_AXI_transactor->RRESP(c0_ddr4_s_axi_rresp);
  mp_C0_DDR4_S_AXI_transactor->RVALID(c0_ddr4_s_axi_rvalid);
  mp_C0_DDR4_S_AXI_transactor->WDATA(c0_ddr4_s_axi_wdata);
  mp_C0_DDR4_S_AXI_transactor->WLAST(c0_ddr4_s_axi_wlast);
  mp_C0_DDR4_S_AXI_transactor->WREADY(c0_ddr4_s_axi_wready);
  mp_C0_DDR4_S_AXI_transactor->WSTRB(c0_ddr4_s_axi_wstrb);
  mp_C0_DDR4_S_AXI_transactor->WVALID(c0_ddr4_s_axi_wvalid);
  mp_C0_DDR4_S_AXI_transactor->CLK(c0_ddr4_ui_clk);
  mp_C0_DDR4_S_AXI_transactor->RST(c0_ddr4_aresetn);

  // initialize transactors stubs
  C0_DDR4_S_AXI_CTRL_transactor_target_wr_socket_stub = nullptr;
  C0_DDR4_S_AXI_CTRL_transactor_target_rd_socket_stub = nullptr;
  C0_DDR4_S_AXI_transactor_target_wr_socket_stub = nullptr;
  C0_DDR4_S_AXI_transactor_target_rd_socket_stub = nullptr;

}

void cl_ddr4_32g_ap::before_end_of_elaboration()
{
  // configure 'C0_DDR4_S_AXI_CTRL' transactor
  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_ddr4_32g_ap", "C0_DDR4_S_AXI_CTRL_TLM_MODE") != 1)
  {
    mp_impl->C0_DDR_SAXI_CTRL_rd_socket->bind(*(mp_C0_DDR4_S_AXI_CTRL_transactor->rd_socket));
    mp_impl->C0_DDR_SAXI_CTRL_wr_socket->bind(*(mp_C0_DDR4_S_AXI_CTRL_transactor->wr_socket));
  
  }
  else
  {
    C0_DDR4_S_AXI_CTRL_transactor_target_wr_socket_stub = new xtlm::xtlm_aximm_target_stub("wr_socket",0);
    C0_DDR4_S_AXI_CTRL_transactor_target_wr_socket_stub->bind(*(mp_C0_DDR4_S_AXI_CTRL_transactor->wr_socket));
    C0_DDR4_S_AXI_CTRL_transactor_target_rd_socket_stub = new xtlm::xtlm_aximm_target_stub("rd_socket",0);
    C0_DDR4_S_AXI_CTRL_transactor_target_rd_socket_stub->bind(*(mp_C0_DDR4_S_AXI_CTRL_transactor->rd_socket));
    mp_C0_DDR4_S_AXI_CTRL_transactor->disable_transactor();
  }

  // configure 'C0_DDR4_S_AXI' transactor
  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_ddr4_32g_ap", "C0_DDR4_S_AXI_TLM_MODE") != 1)
  {
    mp_impl->C0_DDR_SAXI_rd_socket->bind(*(mp_C0_DDR4_S_AXI_transactor->rd_socket));
    mp_impl->C0_DDR_SAXI_wr_socket->bind(*(mp_C0_DDR4_S_AXI_transactor->wr_socket));
  
  }
  else
  {
    C0_DDR4_S_AXI_transactor_target_wr_socket_stub = new xtlm::xtlm_aximm_target_stub("wr_socket",0);
    C0_DDR4_S_AXI_transactor_target_wr_socket_stub->bind(*(mp_C0_DDR4_S_AXI_transactor->wr_socket));
    C0_DDR4_S_AXI_transactor_target_rd_socket_stub = new xtlm::xtlm_aximm_target_stub("rd_socket",0);
    C0_DDR4_S_AXI_transactor_target_rd_socket_stub->bind(*(mp_C0_DDR4_S_AXI_transactor->rd_socket));
    mp_C0_DDR4_S_AXI_transactor->disable_transactor();
  }

}

#endif // VCSSYSTEMC




#ifdef MTI_SYSTEMC
cl_ddr4_32g_ap::cl_ddr4_32g_ap(const sc_core::sc_module_name& nm) : cl_ddr4_32g_ap_sc(nm),  c0_init_calib_complete("c0_init_calib_complete"), dbg_clk("dbg_clk"), c0_sys_clk_p("c0_sys_clk_p"), c0_sys_clk_n("c0_sys_clk_n"), dbg_bus("dbg_bus"), c0_ddr4_adr("c0_ddr4_adr"), c0_ddr4_ba("c0_ddr4_ba"), c0_ddr4_cke("c0_ddr4_cke"), c0_ddr4_cs_n("c0_ddr4_cs_n"), c0_ddr4_dq("c0_ddr4_dq"), c0_ddr4_dqs_c("c0_ddr4_dqs_c"), c0_ddr4_dqs_t("c0_ddr4_dqs_t"), c0_ddr4_odt("c0_ddr4_odt"), c0_ddr4_parity("c0_ddr4_parity"), c0_ddr4_bg("c0_ddr4_bg"), c0_ddr4_reset_n("c0_ddr4_reset_n"), c0_ddr4_act_n("c0_ddr4_act_n"), c0_ddr4_ck_c("c0_ddr4_ck_c"), c0_ddr4_ck_t("c0_ddr4_ck_t"), c0_ddr4_ui_clk("c0_ddr4_ui_clk"), c0_ddr4_ui_clk_sync_rst("c0_ddr4_ui_clk_sync_rst"), c0_ddr4_app_sref_req("c0_ddr4_app_sref_req"), c0_ddr4_app_sref_ack("c0_ddr4_app_sref_ack"), c0_ddr4_app_restore_en("c0_ddr4_app_restore_en"), c0_ddr4_app_restore_complete("c0_ddr4_app_restore_complete"), c0_ddr4_app_mem_init_skip("c0_ddr4_app_mem_init_skip"), c0_ddr4_app_xsdb_select("c0_ddr4_app_xsdb_select"), c0_ddr4_app_xsdb_rd_en("c0_ddr4_app_xsdb_rd_en"), c0_ddr4_app_xsdb_wr_en("c0_ddr4_app_xsdb_wr_en"), c0_ddr4_app_xsdb_addr("c0_ddr4_app_xsdb_addr"), c0_ddr4_app_xsdb_wr_data("c0_ddr4_app_xsdb_wr_data"), c0_ddr4_app_xsdb_rd_data("c0_ddr4_app_xsdb_rd_data"), c0_ddr4_app_xsdb_rdy("c0_ddr4_app_xsdb_rdy"), c0_ddr4_app_dbg_out("c0_ddr4_app_dbg_out"), c0_ddr4_aresetn("c0_ddr4_aresetn"), c0_ddr4_s_axi_ctrl_awvalid("c0_ddr4_s_axi_ctrl_awvalid"), c0_ddr4_s_axi_ctrl_awready("c0_ddr4_s_axi_ctrl_awready"), c0_ddr4_s_axi_ctrl_awaddr("c0_ddr4_s_axi_ctrl_awaddr"), c0_ddr4_s_axi_ctrl_wvalid("c0_ddr4_s_axi_ctrl_wvalid"), c0_ddr4_s_axi_ctrl_wready("c0_ddr4_s_axi_ctrl_wready"), c0_ddr4_s_axi_ctrl_wdata("c0_ddr4_s_axi_ctrl_wdata"), c0_ddr4_s_axi_ctrl_bvalid("c0_ddr4_s_axi_ctrl_bvalid"), c0_ddr4_s_axi_ctrl_bready("c0_ddr4_s_axi_ctrl_bready"), c0_ddr4_s_axi_ctrl_bresp("c0_ddr4_s_axi_ctrl_bresp"), c0_ddr4_s_axi_ctrl_arvalid("c0_ddr4_s_axi_ctrl_arvalid"), c0_ddr4_s_axi_ctrl_arready("c0_ddr4_s_axi_ctrl_arready"), c0_ddr4_s_axi_ctrl_araddr("c0_ddr4_s_axi_ctrl_araddr"), c0_ddr4_s_axi_ctrl_rvalid("c0_ddr4_s_axi_ctrl_rvalid"), c0_ddr4_s_axi_ctrl_rready("c0_ddr4_s_axi_ctrl_rready"), c0_ddr4_s_axi_ctrl_rdata("c0_ddr4_s_axi_ctrl_rdata"), c0_ddr4_s_axi_ctrl_rresp("c0_ddr4_s_axi_ctrl_rresp"), c0_ddr4_interrupt("c0_ddr4_interrupt"), c0_ddr4_s_axi_awid("c0_ddr4_s_axi_awid"), c0_ddr4_s_axi_awaddr("c0_ddr4_s_axi_awaddr"), c0_ddr4_s_axi_awlen("c0_ddr4_s_axi_awlen"), c0_ddr4_s_axi_awsize("c0_ddr4_s_axi_awsize"), c0_ddr4_s_axi_awburst("c0_ddr4_s_axi_awburst"), c0_ddr4_s_axi_awlock("c0_ddr4_s_axi_awlock"), c0_ddr4_s_axi_awcache("c0_ddr4_s_axi_awcache"), c0_ddr4_s_axi_awprot("c0_ddr4_s_axi_awprot"), c0_ddr4_s_axi_awqos("c0_ddr4_s_axi_awqos"), c0_ddr4_s_axi_awvalid("c0_ddr4_s_axi_awvalid"), c0_ddr4_s_axi_awready("c0_ddr4_s_axi_awready"), c0_ddr4_s_axi_wdata("c0_ddr4_s_axi_wdata"), c0_ddr4_s_axi_wstrb("c0_ddr4_s_axi_wstrb"), c0_ddr4_s_axi_wlast("c0_ddr4_s_axi_wlast"), c0_ddr4_s_axi_wvalid("c0_ddr4_s_axi_wvalid"), c0_ddr4_s_axi_wready("c0_ddr4_s_axi_wready"), c0_ddr4_s_axi_bready("c0_ddr4_s_axi_bready"), c0_ddr4_s_axi_bid("c0_ddr4_s_axi_bid"), c0_ddr4_s_axi_bresp("c0_ddr4_s_axi_bresp"), c0_ddr4_s_axi_bvalid("c0_ddr4_s_axi_bvalid"), c0_ddr4_s_axi_arid("c0_ddr4_s_axi_arid"), c0_ddr4_s_axi_araddr("c0_ddr4_s_axi_araddr"), c0_ddr4_s_axi_arlen("c0_ddr4_s_axi_arlen"), c0_ddr4_s_axi_arsize("c0_ddr4_s_axi_arsize"), c0_ddr4_s_axi_arburst("c0_ddr4_s_axi_arburst"), c0_ddr4_s_axi_arlock("c0_ddr4_s_axi_arlock"), c0_ddr4_s_axi_arcache("c0_ddr4_s_axi_arcache"), c0_ddr4_s_axi_arprot("c0_ddr4_s_axi_arprot"), c0_ddr4_s_axi_arqos("c0_ddr4_s_axi_arqos"), c0_ddr4_s_axi_arvalid("c0_ddr4_s_axi_arvalid"), c0_ddr4_s_axi_arready("c0_ddr4_s_axi_arready"), c0_ddr4_s_axi_rready("c0_ddr4_s_axi_rready"), c0_ddr4_s_axi_rlast("c0_ddr4_s_axi_rlast"), c0_ddr4_s_axi_rvalid("c0_ddr4_s_axi_rvalid"), c0_ddr4_s_axi_rresp("c0_ddr4_s_axi_rresp"), c0_ddr4_s_axi_rid("c0_ddr4_s_axi_rid"), c0_ddr4_s_axi_rdata("c0_ddr4_s_axi_rdata"), c0_ddr4_s_axi_aruser("c0_ddr4_s_axi_aruser"), c0_ddr4_s_axi_awuser("c0_ddr4_s_axi_awuser"), sys_rst("sys_rst")
{
  // initialize pins
  mp_impl->c0_init_calib_complete(c0_init_calib_complete);
  mp_impl->dbg_clk(dbg_clk);
  mp_impl->c0_sys_clk_p(c0_sys_clk_p);
  mp_impl->c0_sys_clk_n(c0_sys_clk_n);
  mp_impl->dbg_bus(dbg_bus);
  mp_impl->c0_ddr4_adr(c0_ddr4_adr);
  mp_impl->c0_ddr4_ba(c0_ddr4_ba);
  mp_impl->c0_ddr4_cke(c0_ddr4_cke);
  mp_impl->c0_ddr4_cs_n(c0_ddr4_cs_n);
  mp_impl->c0_ddr4_dq(c0_ddr4_dq);
  mp_impl->c0_ddr4_dqs_c(c0_ddr4_dqs_c);
  mp_impl->c0_ddr4_dqs_t(c0_ddr4_dqs_t);
  mp_impl->c0_ddr4_odt(c0_ddr4_odt);
  mp_impl->c0_ddr4_parity(c0_ddr4_parity);
  mp_impl->c0_ddr4_bg(c0_ddr4_bg);
  mp_impl->c0_ddr4_reset_n(c0_ddr4_reset_n);
  mp_impl->c0_ddr4_act_n(c0_ddr4_act_n);
  mp_impl->c0_ddr4_ck_c(c0_ddr4_ck_c);
  mp_impl->c0_ddr4_ck_t(c0_ddr4_ck_t);
  mp_impl->c0_ddr4_ui_clk(c0_ddr4_ui_clk);
  mp_impl->c0_ddr4_ui_clk_sync_rst(c0_ddr4_ui_clk_sync_rst);
  mp_impl->c0_ddr4_app_sref_req(c0_ddr4_app_sref_req);
  mp_impl->c0_ddr4_app_sref_ack(c0_ddr4_app_sref_ack);
  mp_impl->c0_ddr4_app_restore_en(c0_ddr4_app_restore_en);
  mp_impl->c0_ddr4_app_restore_complete(c0_ddr4_app_restore_complete);
  mp_impl->c0_ddr4_app_mem_init_skip(c0_ddr4_app_mem_init_skip);
  mp_impl->c0_ddr4_app_xsdb_select(c0_ddr4_app_xsdb_select);
  mp_impl->c0_ddr4_app_xsdb_rd_en(c0_ddr4_app_xsdb_rd_en);
  mp_impl->c0_ddr4_app_xsdb_wr_en(c0_ddr4_app_xsdb_wr_en);
  mp_impl->c0_ddr4_app_xsdb_addr(c0_ddr4_app_xsdb_addr);
  mp_impl->c0_ddr4_app_xsdb_wr_data(c0_ddr4_app_xsdb_wr_data);
  mp_impl->c0_ddr4_app_xsdb_rd_data(c0_ddr4_app_xsdb_rd_data);
  mp_impl->c0_ddr4_app_xsdb_rdy(c0_ddr4_app_xsdb_rdy);
  mp_impl->c0_ddr4_app_dbg_out(c0_ddr4_app_dbg_out);
  mp_impl->c0_ddr4_aresetn(c0_ddr4_aresetn);
  mp_impl->c0_ddr4_interrupt(c0_ddr4_interrupt);
  mp_impl->sys_rst(sys_rst);

  // initialize transactors
  mp_C0_DDR4_S_AXI_CTRL_transactor = NULL;
  mp_C0_DDR4_S_AXI_transactor = NULL;
  mp_c0_ddr4_s_axi_arlock_converter = NULL;
  mp_c0_ddr4_s_axi_aruser_converter = NULL;
  mp_c0_ddr4_s_axi_awlock_converter = NULL;
  mp_c0_ddr4_s_axi_awuser_converter = NULL;

  // Instantiate Socket Stubs

  // configure C0_DDR4_S_AXI_CTRL_transactor
    xsc::common_cpp::properties C0_DDR4_S_AXI_CTRL_transactor_param_props;
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("DATA_WIDTH", "32");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("ID_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("ADDR_WIDTH", "32");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("AWUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("ARUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("WUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("RUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("BUSER_WIDTH", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_BURST", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_LOCK", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_PROT", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_CACHE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_QOS", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_REGION", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_WSTRB", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_BRESP", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_RRESP", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("MAX_BURST_LENGTH", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_SIZE", "0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addLong("HAS_RESET", "1");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addFloat("FREQ_HZ", "2.665e+08");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addFloat("PHASE", "0.0");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addString("PROTOCOL", "AXI4LITE");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    C0_DDR4_S_AXI_CTRL_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_C0_DDR4_S_AXI_CTRL_transactor = new xtlm::xaximm_pin2xtlm_t<32,32,1,1,1,1,1,1>("C0_DDR4_S_AXI_CTRL_transactor", C0_DDR4_S_AXI_CTRL_transactor_param_props);
  mp_C0_DDR4_S_AXI_CTRL_transactor->ARADDR(c0_ddr4_s_axi_ctrl_araddr);
  mp_C0_DDR4_S_AXI_CTRL_transactor->ARREADY(c0_ddr4_s_axi_ctrl_arready);
  mp_C0_DDR4_S_AXI_CTRL_transactor->ARVALID(c0_ddr4_s_axi_ctrl_arvalid);
  mp_C0_DDR4_S_AXI_CTRL_transactor->AWADDR(c0_ddr4_s_axi_ctrl_awaddr);
  mp_C0_DDR4_S_AXI_CTRL_transactor->AWREADY(c0_ddr4_s_axi_ctrl_awready);
  mp_C0_DDR4_S_AXI_CTRL_transactor->AWVALID(c0_ddr4_s_axi_ctrl_awvalid);
  mp_C0_DDR4_S_AXI_CTRL_transactor->BREADY(c0_ddr4_s_axi_ctrl_bready);
  mp_C0_DDR4_S_AXI_CTRL_transactor->BRESP(c0_ddr4_s_axi_ctrl_bresp);
  mp_C0_DDR4_S_AXI_CTRL_transactor->BVALID(c0_ddr4_s_axi_ctrl_bvalid);
  mp_C0_DDR4_S_AXI_CTRL_transactor->RDATA(c0_ddr4_s_axi_ctrl_rdata);
  mp_C0_DDR4_S_AXI_CTRL_transactor->RREADY(c0_ddr4_s_axi_ctrl_rready);
  mp_C0_DDR4_S_AXI_CTRL_transactor->RRESP(c0_ddr4_s_axi_ctrl_rresp);
  mp_C0_DDR4_S_AXI_CTRL_transactor->RVALID(c0_ddr4_s_axi_ctrl_rvalid);
  mp_C0_DDR4_S_AXI_CTRL_transactor->WDATA(c0_ddr4_s_axi_ctrl_wdata);
  mp_C0_DDR4_S_AXI_CTRL_transactor->WREADY(c0_ddr4_s_axi_ctrl_wready);
  mp_C0_DDR4_S_AXI_CTRL_transactor->WVALID(c0_ddr4_s_axi_ctrl_wvalid);
  mp_C0_DDR4_S_AXI_CTRL_transactor->CLK(c0_ddr4_ui_clk);
  mp_C0_DDR4_S_AXI_CTRL_transactor->RST(c0_ddr4_aresetn);
  // configure C0_DDR4_S_AXI_transactor
    xsc::common_cpp::properties C0_DDR4_S_AXI_transactor_param_props;
    C0_DDR4_S_AXI_transactor_param_props.addLong("DATA_WIDTH", "512");
    C0_DDR4_S_AXI_transactor_param_props.addLong("ID_WIDTH", "16");
    C0_DDR4_S_AXI_transactor_param_props.addLong("ADDR_WIDTH", "35");
    C0_DDR4_S_AXI_transactor_param_props.addLong("AWUSER_WIDTH", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("ARUSER_WIDTH", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("WUSER_WIDTH", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("RUSER_WIDTH", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("BUSER_WIDTH", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_BURST", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_LOCK", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_PROT", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_CACHE", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_QOS", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_REGION", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_WSTRB", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_BRESP", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_RRESP", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("SUPPORTS_NARROW_BURST", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_READ_OUTSTANDING", "2");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_WRITE_OUTSTANDING", "2");
    C0_DDR4_S_AXI_transactor_param_props.addLong("MAX_BURST_LENGTH", "256");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_READ_THREADS", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("NUM_WRITE_THREADS", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("RUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("WUSER_BITS_PER_BYTE", "0");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_SIZE", "1");
    C0_DDR4_S_AXI_transactor_param_props.addLong("HAS_RESET", "1");
    C0_DDR4_S_AXI_transactor_param_props.addFloat("FREQ_HZ", "2.665e+08");
    C0_DDR4_S_AXI_transactor_param_props.addFloat("PHASE", "0.0");
    C0_DDR4_S_AXI_transactor_param_props.addString("PROTOCOL", "AXI4");
    C0_DDR4_S_AXI_transactor_param_props.addString("READ_WRITE_MODE", "READ_WRITE");
    C0_DDR4_S_AXI_transactor_param_props.addString("CLK_DOMAIN", "");

    mp_C0_DDR4_S_AXI_transactor = new xtlm::xaximm_pin2xtlm_t<512,35,16,1,1,1,1,1>("C0_DDR4_S_AXI_transactor", C0_DDR4_S_AXI_transactor_param_props);
  mp_C0_DDR4_S_AXI_transactor->ARADDR(c0_ddr4_s_axi_araddr);
  mp_C0_DDR4_S_AXI_transactor->ARBURST(c0_ddr4_s_axi_arburst);
  mp_C0_DDR4_S_AXI_transactor->ARCACHE(c0_ddr4_s_axi_arcache);
  mp_C0_DDR4_S_AXI_transactor->ARID(c0_ddr4_s_axi_arid);
  mp_C0_DDR4_S_AXI_transactor->ARLEN(c0_ddr4_s_axi_arlen);
  mp_c0_ddr4_s_axi_arlock_converter = new xsc::common::vectorN2scalar_converter<1>("c0_ddr4_s_axi_arlock_converter");
  mp_c0_ddr4_s_axi_arlock_converter->vector_in(c0_ddr4_s_axi_arlock);
  mp_c0_ddr4_s_axi_arlock_converter->scalar_out(m_c0_ddr4_s_axi_arlock_converter_signal);
  mp_C0_DDR4_S_AXI_transactor->ARLOCK(m_c0_ddr4_s_axi_arlock_converter_signal);
  mp_C0_DDR4_S_AXI_transactor->ARPROT(c0_ddr4_s_axi_arprot);
  mp_C0_DDR4_S_AXI_transactor->ARQOS(c0_ddr4_s_axi_arqos);
  mp_C0_DDR4_S_AXI_transactor->ARREADY(c0_ddr4_s_axi_arready);
  mp_C0_DDR4_S_AXI_transactor->ARSIZE(c0_ddr4_s_axi_arsize);
  mp_c0_ddr4_s_axi_aruser_converter = new xsc::common::scalar2vectorN_converter<1>("c0_ddr4_s_axi_aruser_converter");
  mp_c0_ddr4_s_axi_aruser_converter->scalar_in(c0_ddr4_s_axi_aruser);
  mp_c0_ddr4_s_axi_aruser_converter->vector_out(m_c0_ddr4_s_axi_aruser_converter_signal);
  mp_C0_DDR4_S_AXI_transactor->ARUSER(m_c0_ddr4_s_axi_aruser_converter_signal);
  mp_C0_DDR4_S_AXI_transactor->ARVALID(c0_ddr4_s_axi_arvalid);
  mp_C0_DDR4_S_AXI_transactor->AWADDR(c0_ddr4_s_axi_awaddr);
  mp_C0_DDR4_S_AXI_transactor->AWBURST(c0_ddr4_s_axi_awburst);
  mp_C0_DDR4_S_AXI_transactor->AWCACHE(c0_ddr4_s_axi_awcache);
  mp_C0_DDR4_S_AXI_transactor->AWID(c0_ddr4_s_axi_awid);
  mp_C0_DDR4_S_AXI_transactor->AWLEN(c0_ddr4_s_axi_awlen);
  mp_c0_ddr4_s_axi_awlock_converter = new xsc::common::vectorN2scalar_converter<1>("c0_ddr4_s_axi_awlock_converter");
  mp_c0_ddr4_s_axi_awlock_converter->vector_in(c0_ddr4_s_axi_awlock);
  mp_c0_ddr4_s_axi_awlock_converter->scalar_out(m_c0_ddr4_s_axi_awlock_converter_signal);
  mp_C0_DDR4_S_AXI_transactor->AWLOCK(m_c0_ddr4_s_axi_awlock_converter_signal);
  mp_C0_DDR4_S_AXI_transactor->AWPROT(c0_ddr4_s_axi_awprot);
  mp_C0_DDR4_S_AXI_transactor->AWQOS(c0_ddr4_s_axi_awqos);
  mp_C0_DDR4_S_AXI_transactor->AWREADY(c0_ddr4_s_axi_awready);
  mp_C0_DDR4_S_AXI_transactor->AWSIZE(c0_ddr4_s_axi_awsize);
  mp_c0_ddr4_s_axi_awuser_converter = new xsc::common::scalar2vectorN_converter<1>("c0_ddr4_s_axi_awuser_converter");
  mp_c0_ddr4_s_axi_awuser_converter->scalar_in(c0_ddr4_s_axi_awuser);
  mp_c0_ddr4_s_axi_awuser_converter->vector_out(m_c0_ddr4_s_axi_awuser_converter_signal);
  mp_C0_DDR4_S_AXI_transactor->AWUSER(m_c0_ddr4_s_axi_awuser_converter_signal);
  mp_C0_DDR4_S_AXI_transactor->AWVALID(c0_ddr4_s_axi_awvalid);
  mp_C0_DDR4_S_AXI_transactor->BID(c0_ddr4_s_axi_bid);
  mp_C0_DDR4_S_AXI_transactor->BREADY(c0_ddr4_s_axi_bready);
  mp_C0_DDR4_S_AXI_transactor->BRESP(c0_ddr4_s_axi_bresp);
  mp_C0_DDR4_S_AXI_transactor->BVALID(c0_ddr4_s_axi_bvalid);
  mp_C0_DDR4_S_AXI_transactor->RDATA(c0_ddr4_s_axi_rdata);
  mp_C0_DDR4_S_AXI_transactor->RID(c0_ddr4_s_axi_rid);
  mp_C0_DDR4_S_AXI_transactor->RLAST(c0_ddr4_s_axi_rlast);
  mp_C0_DDR4_S_AXI_transactor->RREADY(c0_ddr4_s_axi_rready);
  mp_C0_DDR4_S_AXI_transactor->RRESP(c0_ddr4_s_axi_rresp);
  mp_C0_DDR4_S_AXI_transactor->RVALID(c0_ddr4_s_axi_rvalid);
  mp_C0_DDR4_S_AXI_transactor->WDATA(c0_ddr4_s_axi_wdata);
  mp_C0_DDR4_S_AXI_transactor->WLAST(c0_ddr4_s_axi_wlast);
  mp_C0_DDR4_S_AXI_transactor->WREADY(c0_ddr4_s_axi_wready);
  mp_C0_DDR4_S_AXI_transactor->WSTRB(c0_ddr4_s_axi_wstrb);
  mp_C0_DDR4_S_AXI_transactor->WVALID(c0_ddr4_s_axi_wvalid);
  mp_C0_DDR4_S_AXI_transactor->CLK(c0_ddr4_ui_clk);
  mp_C0_DDR4_S_AXI_transactor->RST(c0_ddr4_aresetn);

  // initialize transactors stubs
  C0_DDR4_S_AXI_CTRL_transactor_target_wr_socket_stub = nullptr;
  C0_DDR4_S_AXI_CTRL_transactor_target_rd_socket_stub = nullptr;
  C0_DDR4_S_AXI_transactor_target_wr_socket_stub = nullptr;
  C0_DDR4_S_AXI_transactor_target_rd_socket_stub = nullptr;

}

void cl_ddr4_32g_ap::before_end_of_elaboration()
{
  // configure 'C0_DDR4_S_AXI_CTRL' transactor
  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_ddr4_32g_ap", "C0_DDR4_S_AXI_CTRL_TLM_MODE") != 1)
  {
    mp_impl->C0_DDR_SAXI_CTRL_rd_socket->bind(*(mp_C0_DDR4_S_AXI_CTRL_transactor->rd_socket));
    mp_impl->C0_DDR_SAXI_CTRL_wr_socket->bind(*(mp_C0_DDR4_S_AXI_CTRL_transactor->wr_socket));
  
  }
  else
  {
    C0_DDR4_S_AXI_CTRL_transactor_target_wr_socket_stub = new xtlm::xtlm_aximm_target_stub("wr_socket",0);
    C0_DDR4_S_AXI_CTRL_transactor_target_wr_socket_stub->bind(*(mp_C0_DDR4_S_AXI_CTRL_transactor->wr_socket));
    C0_DDR4_S_AXI_CTRL_transactor_target_rd_socket_stub = new xtlm::xtlm_aximm_target_stub("rd_socket",0);
    C0_DDR4_S_AXI_CTRL_transactor_target_rd_socket_stub->bind(*(mp_C0_DDR4_S_AXI_CTRL_transactor->rd_socket));
    mp_C0_DDR4_S_AXI_CTRL_transactor->disable_transactor();
  }

  // configure 'C0_DDR4_S_AXI' transactor
  if (xsc::utils::xsc_sim_manager::getInstanceParameterInt("cl_ddr4_32g_ap", "C0_DDR4_S_AXI_TLM_MODE") != 1)
  {
    mp_impl->C0_DDR_SAXI_rd_socket->bind(*(mp_C0_DDR4_S_AXI_transactor->rd_socket));
    mp_impl->C0_DDR_SAXI_wr_socket->bind(*(mp_C0_DDR4_S_AXI_transactor->wr_socket));
  
  }
  else
  {
    C0_DDR4_S_AXI_transactor_target_wr_socket_stub = new xtlm::xtlm_aximm_target_stub("wr_socket",0);
    C0_DDR4_S_AXI_transactor_target_wr_socket_stub->bind(*(mp_C0_DDR4_S_AXI_transactor->wr_socket));
    C0_DDR4_S_AXI_transactor_target_rd_socket_stub = new xtlm::xtlm_aximm_target_stub("rd_socket",0);
    C0_DDR4_S_AXI_transactor_target_rd_socket_stub->bind(*(mp_C0_DDR4_S_AXI_transactor->rd_socket));
    mp_C0_DDR4_S_AXI_transactor->disable_transactor();
  }

}

#endif // MTI_SYSTEMC




cl_ddr4_32g_ap::~cl_ddr4_32g_ap()
{
  delete mp_C0_DDR4_S_AXI_CTRL_transactor;

  delete mp_C0_DDR4_S_AXI_transactor;
  delete mp_c0_ddr4_s_axi_arlock_converter;
  delete mp_c0_ddr4_s_axi_aruser_converter;
  delete mp_c0_ddr4_s_axi_awlock_converter;
  delete mp_c0_ddr4_s_axi_awuser_converter;

}

#ifdef MTI_SYSTEMC
SC_MODULE_EXPORT(cl_ddr4_32g_ap);
#endif

#ifdef XM_SYSTEMC
XMSC_MODULE_EXPORT(cl_ddr4_32g_ap);
#endif

#ifdef RIVIERA
SC_MODULE_EXPORT(cl_ddr4_32g_ap);
SC_REGISTER_BV(512);
#endif

