// (c) Copyright 1995-2021, 2023 Advanced Micro Devices, Inc. All rights reserved.
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
////////////////////////////////////////////////////////////

#ifndef _AXI_DWIDTH_CONVERTER_H_
#define _AXI_DWIDTH_CONVERTER_H_

#include "xtlm.h"
#include "report_handler.h"

class axi_dwidth_converter: public sc_core::sc_module {
public:
    SC_HAS_PROCESS(axi_dwidth_converter);
	xtlm::xtlm_aximm_target_socket* target_rd_socket;
	xtlm::xtlm_aximm_target_socket* target_wr_socket;
	xtlm::xtlm_aximm_initiator_socket* initiator_rd_socket;
	xtlm::xtlm_aximm_initiator_socket* initiator_wr_socket;
	sc_core::sc_in<bool> s_axi_aclk;
	sc_core::sc_in<bool> s_axi_aresetn;
  sc_core::sc_in<bool> m_axi_aclk;
	sc_core::sc_in<bool> m_axi_aresetn;
  sc_core::sc_signal<bool> clk;
	sc_core::sc_signal<bool> resetn;
	axi_dwidth_converter(sc_core::sc_module_name p_name,
				xsc::common_cpp::properties& m_properties);
	xtlm::xtlm_aximm_target_rd_socket_util* rd_target_util;
    xtlm::xtlm_aximm_target_wr_socket_util* wr_target_util;
    xtlm::xtlm_aximm_initiator_rd_socket_util* rd_initiator_util;
    xtlm::xtlm_aximm_initiator_wr_socket_util* wr_initiator_util;
    xtlm::xtlm_aximm_mem_manager* mem_manager;
    ~axi_dwidth_converter();
    unsigned int SI_DATA_WIDTH;
    unsigned int MI_DATA_WIDTH;
    unsigned int FIFO_MODE;
    unsigned int ratio;

    void wr_handler();
    void rd_handler();
    void wr_upsizing();
    void wr_downsizing();
    void rd_upsizing();
    void rd_downsizing();

    /**
     * @brief Method to send transaction on master interface
     */
    void m_downsize_interface_txn_sender();
    void m_upsize_interface_txn_sender();

    void m_downsize_interface_response_sender();
    void m_upsize_interface_response_sender();

private:
    xtlm::aximm_payload* m_rd_trans;
    xtlm::aximm_payload* m_wr_trans;
    std::queue<xtlm::aximm_payload*> m_upsize_rd_payld_queue;
    std::queue<xtlm::aximm_payload*> m_upsize_wr_payld_queue;
    std::queue<xtlm::aximm_payload*> m_interface_wr_payload_queue;
    std::queue<xtlm::aximm_payload*> m_interface_rd_payload_queue;
    sc_core::sc_event event_downsize_trig_txn_sender;	//!< Event to trigger Txn Sender Method
    sc_core::sc_event event_upsize_trig_txn_sender; //!< Event to trigger Txn Sender Method
    sc_core::sc_event event_trig_rd_handler;
    sc_core::sc_event event_trig_wr_handler;
    std::list<xtlm::aximm_payload* > *m_response_list;
    std::map<xtlm::aximm_payload*,std::list<xtlm::aximm_payload*>*> m_response_mapper_downsize;
    std::map<xtlm::aximm_payload*,xtlm::aximm_payload*> m_response_mapper_upsize;
    xsc::common_cpp::report_handler m_logger;
    std::string m_log_msg;
};

#endif /* _AXI_DWIDTH_CONVERTER_H_ */



