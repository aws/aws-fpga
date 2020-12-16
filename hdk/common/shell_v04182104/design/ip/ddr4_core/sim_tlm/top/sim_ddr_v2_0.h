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
#include "utils/xtlm_cmnhdr.h"
#include "xtlm.h"
#include "report_handler.h"
#include <sstream>
#ifdef SDACCEL_WITH_DATA_CONVERTER 
#include "sdaccel_data_converter.h"
#endif
#include "sim_ddrx.h"
#ifdef TLM2_PROTOCOL_CHEKER
#include "tlm2_base_protocol_checker.h"
#endif
#ifndef sim_ddr_v2_0_H
#define sim_ddr_v2_0_H
#include "utils/xsc_stub_port.h"
#include <utils/xtlm_aximm_passthru_module.h>
class sim_ddr_v2_0 :public sc_module{
  public:
    explicit sim_ddr_v2_0(sc_core::sc_module_name name,
        xsc::common_cpp::properties model_param_props);
    ~sim_ddr_v2_0();

    xtlm::xtlm_aximm_target_socket* C0_DDR_SAXI_wr_socket;
    xtlm::xtlm_aximm_target_socket* C0_DDR_SAXI_rd_socket;
    xtlm::xtlm_aximm_target_socket* C0_DDR_SAXI_CTRL_wr_socket;
    xtlm::xtlm_aximm_target_socket* C0_DDR_SAXI_CTRL_rd_socket;
    
    xtlm::xtlm_aximm_target_rd_socket_util* rd_target_util;
    xtlm::xtlm_aximm_target_wr_socket_util* wr_target_util;
    SC_HAS_PROCESS(sim_ddr_v2_0);

#ifdef SDACCEL_WITH_DATA_CONVERTER
    sdaccel_data_converter* sdaccel_data_converter_model;
#endif

#ifdef TLM2_PROTOCOL_CHEKER        
    tlm2_base_protocol_checker* checker;
#endif
    sc_core::sc_out<bool> c0_ddr4_ui_clk;	
    sc_core::sc_in<bool> c0_ddr4_aresetn;
    sc_core::sc_in<bool> sys_rst;
    sc_core::sc_out< bool > c0_init_calib_complete;
    sc_core::sc_out< bool > dbg_clk;
    sc_core::sc_in< bool > c0_sys_clk_p;
    sc_core::sc_in< bool > c0_sys_clk_n;
    xsc::utils::xsc_stub_port dbg_bus;
    xsc::utils::xsc_stub_port c0_ddr4_adr;
    xsc::utils::xsc_stub_port c0_ddr4_ba;
    xsc::utils::xsc_stub_port c0_ddr4_cke;
    xsc::utils::xsc_stub_port c0_ddr4_cs_n;
    xsc::utils::xsc_stub_port c0_ddr4_dm_dbi_n;
    xsc::utils::xsc_stub_port c0_ddr4_dq;
    xsc::utils::xsc_stub_port c0_ddr4_dqs_c;
    xsc::utils::xsc_stub_port c0_ddr4_dqs_t;
    xsc::utils::xsc_stub_port c0_ddr4_odt;
    xsc::utils::xsc_stub_port c0_ddr4_bg;
    xsc::utils::xsc_stub_port c0_ddr4_parity;
    xsc::utils::xsc_stub_port c0_ddr4_reset_n;
    xsc::utils::xsc_stub_port c0_ddr4_act_n;
    xsc::utils::xsc_stub_port c0_ddr4_ck_c;
    xsc::utils::xsc_stub_port c0_ddr4_ck_t;
    xsc::utils::xsc_stub_port c0_ddr4_interrupt;
    xsc::utils::xsc_stub_port addn_ui_clkout1;
    xsc::utils::xsc_stub_port dbg_rd_data_cmp;
    xsc::utils::xsc_stub_port dbg_expected_data;
    xsc::utils::xsc_stub_port dbg_cal_seq;
    xsc::utils::xsc_stub_port dbg_cal_seq_cnt;
    xsc::utils::xsc_stub_port dbg_cal_seq_rd_cnt;
    xsc::utils::xsc_stub_port dbg_rd_valid;
    xsc::utils::xsc_stub_port dbg_cmp_byte;
    xsc::utils::xsc_stub_port dbg_rd_data;
    xsc::utils::xsc_stub_port dbg_cplx_config;
    xsc::utils::xsc_stub_port dbg_cplx_status;
    xsc::utils::xsc_stub_port dbg_io_address;
    xsc::utils::xsc_stub_port dbg_pllGate;
    xsc::utils::xsc_stub_port dbg_phy2clb_fixdly_rdy_low;
    xsc::utils::xsc_stub_port dbg_phy2clb_fixdly_rdy_upp;
    xsc::utils::xsc_stub_port dbg_phy2clb_phy_rdy_low;
    xsc::utils::xsc_stub_port dbg_phy2clb_phy_rdy_upp;
    xsc::utils::xsc_stub_port cal_r0_status;
    xsc::utils::xsc_stub_port cal_post_status;
    xsc::utils::xsc_stub_port c0_ddr4_mcs_lmb_ce;
    xsc::utils::xsc_stub_port c0_ddr4_mcs_lmb_ue;
    xsc::utils::xsc_stub_port c0_ddr4_app_sref_req;
    xsc::utils::xsc_stub_port c0_ddr4_app_sref_ack;
    xsc::utils::xsc_stub_port c0_ddr4_app_restore_en;
    xsc::utils::xsc_stub_port c0_ddr4_app_restore_complete;
    xsc::utils::xsc_stub_port c0_ddr4_app_mem_init_skip;
    xsc::utils::xsc_stub_port c0_ddr4_app_xsdb_select;
    xsc::utils::xsc_stub_port c0_ddr4_app_xsdb_rd_en;
    xsc::utils::xsc_stub_port c0_ddr4_app_xsdb_wr_en;
    xsc::utils::xsc_stub_port c0_ddr4_app_xsdb_addr;
    xsc::utils::xsc_stub_port c0_ddr4_app_xsdb_wr_data;
    xsc::utils::xsc_stub_port c0_ddr4_app_xsdb_rd_data;
    xsc::utils::xsc_stub_port c0_ddr4_app_xsdb_rdy;
    xsc::utils::xsc_stub_port c0_ddr4_app_dbg_out;
    xsc::utils::xsc_stub_port c0_ddr4_app_ref_req;
    xsc::utils::xsc_stub_port c0_ddr4_app_ref_ack;
    xsc::utils::xsc_stub_port c0_ddr4_app_zq_req;
    xsc::utils::xsc_stub_port c0_ddr4_app_zq_ack;
    xsc::utils::xsc_stub_port c0_ddr4_restore_crc_error;
    xsc::utils::xsc_stub_port c0_ddr4_app_addr;
    xsc::utils::xsc_stub_port c0_ddr4_app_cmd;
    xsc::utils::xsc_stub_port c0_ddr4_app_wdf_data;
    xsc::utils::xsc_stub_port c0_ddr4_app_wdf_mask;
    xsc::utils::xsc_stub_port c0_ddr4_app_rd_data;
    xsc::utils::xsc_stub_port c0_ddr4_app_en;
    xsc::utils::xsc_stub_port c0_ddr4_app_hi_pri;
    xsc::utils::xsc_stub_port c0_ddr4_app_wdf_end;
    xsc::utils::xsc_stub_port c0_ddr4_app_wdf_wren;
    xsc::utils::xsc_stub_port c0_ddr4_app_rd_data_end;
    xsc::utils::xsc_stub_port c0_ddr4_app_rd_data_valid;
    xsc::utils::xsc_stub_port c0_ddr4_app_rdy;
    xsc::utils::xsc_stub_port c0_ddr4_app_wdf_rdy;
    xsc::utils::xsc_stub_port rdDataEn;
    xsc::utils::xsc_stub_port rdDataEnd;
    xsc::utils::xsc_stub_port per_rd_done;
    xsc::utils::xsc_stub_port rmw_rd_done;
    xsc::utils::xsc_stub_port wrDataEn;
    xsc::utils::xsc_stub_port mc_ACT_n;
    xsc::utils::xsc_stub_port mcCasSlot;
    xsc::utils::xsc_stub_port mcCasSlot2;
    xsc::utils::xsc_stub_port mcRdCAS;
    xsc::utils::xsc_stub_port mcWrCAS;
    xsc::utils::xsc_stub_port winInjTxn;
    xsc::utils::xsc_stub_port winRmw;
    xsc::utils::xsc_stub_port gt_data_ready;
    xsc::utils::xsc_stub_port winRank;
    xsc::utils::xsc_stub_port tCWL;
    xsc::utils::xsc_stub_port wrData;
    xsc::utils::xsc_stub_port wrDataMask;
    xsc::utils::xsc_stub_port rdData;
    xsc::utils::xsc_stub_port mc_ADR;
    xsc::utils::xsc_stub_port mc_BA;
    xsc::utils::xsc_stub_port mc_CKE;
    xsc::utils::xsc_stub_port mc_CS_n;
    xsc::utils::xsc_stub_port mc_ODT;
    xsc::utils::xsc_stub_port dBufAdr;
    xsc::utils::xsc_stub_port rdDataAddr;
    xsc::utils::xsc_stub_port wrDataAddr;
    xsc::utils::xsc_stub_port winBuf;
    xsc::utils::xsc_stub_port ddr4_act_n;
    xsc::utils::xsc_stub_port ddr4_adr;
    xsc::utils::xsc_stub_port ddr4_ba;
    xsc::utils::xsc_stub_port ddr4_bg;
    xsc::utils::xsc_stub_port ddr4_par;
    xsc::utils::xsc_stub_port ddr4_cke;
    xsc::utils::xsc_stub_port ddr4_odt;
    xsc::utils::xsc_stub_port ddr4_cs_n;
    xsc::utils::xsc_stub_port ddr4_ck_t;
    xsc::utils::xsc_stub_port ddr4_ck_c;
    xsc::utils::xsc_stub_port ddr4_reset_n;
    xsc::utils::xsc_stub_port ddr4_dm_dbi_n;
    xsc::utils::xsc_stub_port ddr4_dq;
    xsc::utils::xsc_stub_port ddr4_dqs_c;
    xsc::utils::xsc_stub_port ddr4_dqs_t;
    xsc::utils::xsc_stub_port mc_BG;
    
    sc_core::sc_out< bool > c0_ddr4_ui_clk_sync_rst;
    sc_core::sc_in< bool > c0_sys_clk_i;
    sc_core::sc_signal<bool>out1;
    sc_core::sc_signal<bool>out2;
    xsc::common_cpp::report_handler* m_report_handler;
    std::stringstream m_ss;
    float clk;
    void generateReset();
  protected:

  private:
    xsc::sim_ddr_v1_0::sim_ddrx * ddrx_top_tlm_model;

    std::map<std::string, int> user_param_int;
    std::map<std::string, std::string> user_param_string;

};
#endif

