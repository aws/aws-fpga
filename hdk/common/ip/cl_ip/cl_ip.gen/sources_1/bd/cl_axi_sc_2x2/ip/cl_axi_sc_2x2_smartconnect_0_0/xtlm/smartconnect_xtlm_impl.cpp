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

#include "smartconnect_xtlm_impl.h"
#include "smartconnect_xtlm.h"

namespace smartconnect_xtlm_impl {
	target_rd_util::target_rd_util(sc_core::sc_module_name p_name,
			xtlm::aximm::granularity g_hint, int width_p,int si_number_,smartconnect_xtlm *_sxtlm_ptr) :si_number(si_number_),
			xtlm::xtlm_aximm_target_rd_socket_util(p_name, g_hint, width_p),sxtlm_ptr(_sxtlm_ptr) {
	}
	unsigned int target_rd_util::transport_dbg_cb(xtlm::aximm_payload& trans) {
		return sxtlm_ptr->transport_dbg_cb(trans,si_number);
	}
	void target_rd_util::b_transport(xtlm::aximm_payload & trans, sc_core::sc_time & t) {
        sxtlm_ptr->b_transport_cb(trans,t,si_number);
        /*
		std::stringstream ss;
		std::string payloadDes;
		trans.get_log(payloadDes, 1);
		if (parent->m_report_handler->get_verbosity_level()
				== xsc::common_cpp::DEBUG) {
			ss.str("");
			ss << parent->m_module_name << ": "
					<< "Received blocking READ  call b_transport IN sock_id "
					<< m_index << std::endl << payloadDes;
			parent->m_report_handler->report("1", ss.str().c_str(),
					xsc::common_cpp::INFO, xsc::common_cpp::DEBUG);
		}
		int master_itf_id = parent->addressDecoder(trans,
				parent->sockIdtoItfId(m_index));
		if (master_itf_id < 0) {
			trans.set_response_status(xtlm::XTLM_ADDRESS_ERROR_RESPONSE);
		} else if (trans.get_command() == xtlm::XTLM_IGNORE_COMMAND) {
			trans.set_response_status(xtlm::XTLM_COMMAND_ERROR_RESPONSE);
		} else {
			parent->m_b_trans_master_req[master_itf_id].push(&trans);
			while (parent->m_master_btr_busy[master_itf_id]
					|| parent->m_b_trans_master_req[master_itf_id].front() != &trans) {
				wait(parent->m_btr_done_event[master_itf_id]);
			}
			parent->m_master_btr_busy[master_itf_id] = true;
			if (parent->m_report_handler->get_verbosity_level()
					== xsc::common_cpp::DEBUG) {
				ss.str("");
				ss << parent->m_module_name << ": "
						<< "Forwarding blocking READ call b_transport IN to slave "
						<< master_itf_id << std::endl << payloadDes;
				parent->m_report_handler->report("1", ss.str().c_str(),
						xsc::common_cpp::INFO, xsc::common_cpp::DEBUG);
			}

			parent->initiator_rd_sockets_util[master_itf_id]->b_transport(trans,
					t);

			parent->m_b_trans_master_req[master_itf_id].pop();
			parent->m_master_btr_busy[master_itf_id] = false;
			notify(parent->m_btr_done_event[master_itf_id]);
			if (parent->m_report_handler->get_verbosity_level()
					== xsc::common_cpp::DEBUG) {
				ss.str("");
				ss << parent->m_module_name << ": "
						<< "Forwarding done READ call b_transport IN to slave "
						<< master_itf_id << std::endl << payloadDes;
				parent->m_report_handler->report("1", ss.str().c_str(),
						xsc::common_cpp::INFO, xsc::common_cpp::DEBUG);
			}
		}
        */
    }
  /*
    void target_rd_util::register_b_transport(void (*smartconnect_xtlm::b_transport_handler_)(xtlm::aximm_payload& trans, sc_core::sc_time& t,int si_num)) {
        b_transport_handler = b_transport_handler_;
    }
    void target_rd_util::register_transport_dbg(unsigned int (*smartconnect_xtlm::transport_dbg_handler_)(xtlm::aximm_payload& trans,int si_num)) {
        transport_dbg_handler = transport_dbg_handler_;
    }
    */
	target_wr_util::target_wr_util(sc_core::sc_module_name p_name,
			xtlm::aximm::granularity g_hint, int width_p,int si_number_,smartconnect_xtlm *_sxtlm_ptr) :si_number(si_number_),
			xtlm::xtlm_aximm_target_wr_socket_util(p_name, g_hint, width_p),sxtlm_ptr(_sxtlm_ptr) {
	}
	unsigned int target_wr_util::transport_dbg_cb(xtlm::aximm_payload& trans) {
		return sxtlm_ptr->transport_dbg_cb(trans,si_number);
	}
	void target_wr_util::b_transport(xtlm::aximm_payload & trans, sc_core::sc_time & t) {
        sxtlm_ptr->b_transport_cb(trans,t,si_number);
        /*
		//Should wait till the parent is free to make transport call
		std::stringstream ss;
		std::string payloadDes;
		trans.get_log(payloadDes, 1);
		if (parent->m_report_handler->get_verbosity_level()
				== xsc::common_cpp::DEBUG) {
			ss.str("");
			ss << parent->m_module_name << ": "
					<< "Received blocking WRITE call b_transport IN sock_id "
					<< m_index << std::endl << payloadDes;
			parent->m_report_handler->report("1", ss.str().c_str(),
					xsc::common_cpp::INFO, xsc::common_cpp::DEBUG);
		}
		int master_itf_id = parent->addressDecoder(trans,
				parent->sockIdtoItfId(m_index));
		if (master_itf_id < 0) {
			trans.set_response_status(xtlm::XTLM_ADDRESS_ERROR_RESPONSE);
		} else if (trans.get_command() == xtlm::XTLM_IGNORE_COMMAND) {
			trans.set_response_status(xtlm::XTLM_COMMAND_ERROR_RESPONSE);
		} else {
			parent->m_b_trans_master_req[master_itf_id].push(&trans);
			while (parent->m_master_btr_busy[master_itf_id]
					|| parent->m_b_trans_master_req[master_itf_id].front() != &trans) {
				wait(parent->m_btr_done_event[master_itf_id]);
			}
			parent->m_master_btr_busy[master_itf_id] = true;
			if (parent->m_report_handler->get_verbosity_level()
					== xsc::common_cpp::DEBUG) {
				ss.str("");
				ss << parent->m_module_name << ": "
						<< "Forwarding blocking WRITE call b_transport IN to slave "
						<< master_itf_id << std::endl << payloadDes;
				parent->m_report_handler->report("1", ss.str().c_str(),
						xsc::common_cpp::INFO, xsc::common_cpp::DEBUG);
			}
			parent->initiator_wr_sockets_util[master_itf_id]->b_transport(trans,
					t);

			parent->m_b_trans_master_req[master_itf_id].pop();
			parent->m_master_btr_busy[master_itf_id] = false;
			notify(parent->m_btr_done_event[master_itf_id]);
			if (parent->m_report_handler->get_verbosity_level()
					== xsc::common_cpp::DEBUG) {
				ss.str("");
				ss << parent->m_module_name << ": "
						<< "Forwarding done WRITE call b_transport IN to slave "
						<< master_itf_id << std::endl << payloadDes;
				parent->m_report_handler->report("1", ss.str().c_str(),
						xsc::common_cpp::INFO, xsc::common_cpp::DEBUG);
			}
		}
        */
	}
  /*
    void target_wr_util::register_b_transport(void (smartconnect_xtlm::*b_transport_handler_)(xtlm::aximm_payload& trans, sc_core::sc_time& t, int si_num)) {
        b_transport_handler = b_transport_handler_;
    }
    void target_wr_util::register_transport_dbg(unsigned int (smartconnect_xtlm::*transport_dbg_handler_)(xtlm::aximm_payload& trans,int si_num)) {
        transport_dbg_handler = transport_dbg_handler_;
    }
    */
}
