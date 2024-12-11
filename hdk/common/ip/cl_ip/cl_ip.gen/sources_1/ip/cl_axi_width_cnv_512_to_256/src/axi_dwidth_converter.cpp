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

#include "axi_dwidth_converter.h"
#define PAYLOAD_LOG_LEVEL 3

axi_dwidth_converter::axi_dwidth_converter(sc_core::sc_module_name p_name,
		xsc::common_cpp::properties& m_properties) :
		sc_core::sc_module(p_name), m_wr_trans(nullptr), m_rd_trans(nullptr), m_response_list(
				nullptr),m_logger((std::string) (p_name)) {

	initiator_rd_socket = new xtlm::xtlm_aximm_initiator_socket(
			"rd_trace_socket", 32);
	initiator_wr_socket = new xtlm::xtlm_aximm_initiator_socket(
			"wr_trace_socket", 32);
	target_rd_socket = new xtlm::xtlm_aximm_target_socket("rd_trace_socket",
			32);
	target_wr_socket = new xtlm::xtlm_aximm_target_socket("wr_trace_socket",
			32);
	rd_target_util = new xtlm::xtlm_aximm_target_rd_socket_util("rd_tar_util",
			xtlm::aximm::TRANSACTION, 32);
	wr_target_util = new xtlm::xtlm_aximm_target_wr_socket_util("wr_tar_util",
			xtlm::aximm::TRANSACTION, 32);
	rd_initiator_util = new xtlm::xtlm_aximm_initiator_rd_socket_util(
			"rd_ini_util", xtlm::aximm::TRANSACTION, 32);
	wr_initiator_util = new xtlm::xtlm_aximm_initiator_wr_socket_util(
			"wr_ini_util", xtlm::aximm::TRANSACTION, 32);
	target_rd_socket->bind(rd_target_util->rd_socket);
	target_wr_socket->bind(wr_target_util->wr_socket);
	rd_initiator_util->rd_socket.bind(*initiator_rd_socket);
	wr_initiator_util->wr_socket.bind(*initiator_wr_socket);

	mem_manager = new xtlm::xtlm_aximm_mem_manager();
	SI_DATA_WIDTH = m_properties.getLongLong("C_S_AXI_DATA_WIDTH")/8;
	MI_DATA_WIDTH = m_properties.getLongLong("C_M_AXI_DATA_WIDTH")/8;
  FIFO_MODE = m_properties.getLongLong("C_FIFO_MODE");


	ratio = 0; //SI_DATA_WIDTH/MI_DATA_WIDTH;
    if(FIFO_MODE!=2)
  {
    	m_axi_aclk(clk);
			m_axi_aresetn(resetn);
  }

	SC_METHOD(wr_handler);
	dont_initialize();
	sensitive << wr_target_util->transaction_available;
    sensitive << event_trig_wr_handler;

	SC_METHOD(rd_handler);
	dont_initialize();
	sensitive << rd_target_util->addr_available;
    sensitive << event_trig_rd_handler;

	SC_METHOD(m_downsize_interface_txn_sender);
	sensitive << event_downsize_trig_txn_sender;
    sensitive << wr_initiator_util->transaction_sampled;
    sensitive << rd_initiator_util->transaction_sampled;
	dont_initialize();

	SC_METHOD(m_upsize_interface_txn_sender);
	sensitive << event_upsize_trig_txn_sender;
	dont_initialize();

	SC_METHOD(m_downsize_interface_response_sender);
	dont_initialize();
	sensitive << wr_initiator_util->resp_available;
	sensitive << rd_initiator_util->data_available;
  sensitive << rd_target_util->data_sampled;
  sensitive << wr_target_util->resp_sampled;

	SC_METHOD(m_upsize_interface_response_sender);
	dont_initialize();
	sensitive << wr_initiator_util->resp_available;
	sensitive << rd_initiator_util->data_available;
  sensitive << rd_target_util->data_sampled;
  sensitive << wr_target_util->resp_sampled;

}

void axi_dwidth_converter::wr_handler() {
    if(wr_initiator_util->is_slave_ready() && 
            wr_target_util->is_trans_available() )
    {
        m_wr_trans = wr_target_util->get_transaction();
        m_log_msg = "Sampled Write transaction on slave interface : " + std::to_string(m_wr_trans->get_address());
        XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::001",m_log_msg.c_str(), DEBUG); 
        ratio = m_wr_trans->get_burst_size() / MI_DATA_WIDTH;
        if (ratio <= 1)
            wr_upsizing();
        else
            wr_downsizing();
    }
}

void axi_dwidth_converter::rd_handler() {
    if(rd_initiator_util->is_slave_ready() &&
            rd_target_util->is_trans_available() )
    {
	    m_rd_trans = rd_target_util->get_transaction();
        
        m_log_msg = "Sampled Read transaction on slave interface : " + std::to_string( m_rd_trans->get_address());
        XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::001",m_log_msg.c_str(), DEBUG); 
	    
        ratio = m_rd_trans->get_burst_size()  / MI_DATA_WIDTH;
	    if (ratio <= 1)
	    	rd_upsizing();
	    else
	    	rd_downsizing();
    }
}

void axi_dwidth_converter::rd_downsizing() {
	//auto beat_l = m_rd_trans->get_burst_length();
	auto data = m_rd_trans->get_data_ptr();
	//auto new_beat_l = beat_l * (ratio);
	auto strb = m_rd_trans->get_byte_enable_ptr();
	auto s_addr = m_rd_trans->get_address();
  unsigned int length = m_rd_trans->get_data_length();
  auto size = m_rd_trans->get_burst_size();
  auto beat_l = length/size;
  auto new_beat_l = beat_l * (ratio);
	auto num_byte_counter = 0;
	auto total_num_bytes = beat_l * m_rd_trans->get_burst_size();
	auto cur_beat_l = 0;
	auto t_total_txns = 0;

    std::string payload_log; 
    m_rd_trans->get_log(payload_log, PAYLOAD_LOG_LEVEL);
    m_log_msg = "Down Sizing input transaction : " + payload_log;
    XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::002",m_log_msg.c_str(), DEBUG); 
	
    m_response_list = new std::list<xtlm::aximm_payload*>;
	do {
		if (new_beat_l > 256)
			cur_beat_l = 256;
		else
			cur_beat_l = new_beat_l;

		xtlm::aximm_payload* t_trans = mem_manager->get_payload();
		t_trans->acquire();
		t_trans->deep_copy_from(*m_rd_trans);
		t_trans->set_address(s_addr + num_byte_counter);
		t_trans->set_data_ptr(data + num_byte_counter,
				cur_beat_l * MI_DATA_WIDTH);
		t_trans->set_burst_size(MI_DATA_WIDTH);
		if (strb != nullptr)
			t_trans->set_byte_enable_ptr(strb + num_byte_counter,
					cur_beat_l * MI_DATA_WIDTH);
		t_trans->set_burst_length(cur_beat_l);
		num_byte_counter += cur_beat_l * MI_DATA_WIDTH ;
		m_interface_rd_payload_queue.push(t_trans);
		m_response_list->push_back(t_trans);
		t_total_txns++;
        
        std::string payload_log; 
        t_trans->get_log(payload_log, PAYLOAD_LOG_LEVEL);
        m_log_msg = "Down sized output transaction  : " + payload_log;
        XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::002",m_log_msg.c_str(), DEBUG); 

	} while (num_byte_counter < total_num_bytes);
	m_response_mapper_downsize[m_rd_trans] = m_response_list;
	event_downsize_trig_txn_sender.notify();
}

void axi_dwidth_converter::wr_downsizing() {
	//auto beat_l = m_wr_trans->get_burst_length();
	auto data = m_wr_trans->get_data_ptr();
	auto strb = m_wr_trans->get_byte_enable_ptr();
	//auto new_beat_l = beat_l * (ratio);
   unsigned int length = m_wr_trans->get_data_length();
  auto size = m_wr_trans->get_burst_size();
  auto beat_l = length/size;
  auto new_beat_l = beat_l * (ratio);
	auto s_addr = m_wr_trans->get_address();
	auto num_byte_counter = 0;
	auto total_num_bytes = beat_l * m_wr_trans->get_burst_size();
	auto cur_beat_l = 0;
	auto t_total_txns = 0;
	m_response_list = new std::list<xtlm::aximm_payload*>;
    
    std::string payload_log; 
    m_wr_trans->get_log(payload_log, PAYLOAD_LOG_LEVEL);
    m_log_msg = "Down Sizing input transaction : " + payload_log;
    XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::002",m_log_msg.c_str(), DEBUG); 
	
    do {
		if (new_beat_l > 256)
			cur_beat_l = 256;
		else
			cur_beat_l = new_beat_l;

		xtlm::aximm_payload* t_trans = mem_manager->get_payload();
		t_trans->acquire();
		t_trans->deep_copy_from(*m_wr_trans);
		t_trans->set_address(s_addr + num_byte_counter);
		t_trans->set_data_ptr(data + num_byte_counter,
				cur_beat_l * MI_DATA_WIDTH);
		if (strb != nullptr)
			t_trans->set_byte_enable_ptr(strb + num_byte_counter,
					cur_beat_l * MI_DATA_WIDTH );
		t_trans->set_burst_size(MI_DATA_WIDTH );
		t_trans->set_burst_length(cur_beat_l);
		num_byte_counter += cur_beat_l * MI_DATA_WIDTH;
		m_interface_wr_payload_queue.push(t_trans);
		m_response_list->push_back(t_trans);
		t_total_txns++;

        std::string payload_log; 
        t_trans->get_log(payload_log, PAYLOAD_LOG_LEVEL);
        m_log_msg = "Down sized output transaction  : " + payload_log;
        XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::002",m_log_msg.c_str(), DEBUG); 

	} while (num_byte_counter < total_num_bytes);

	m_response_mapper_downsize[m_wr_trans] = m_response_list;
	event_downsize_trig_txn_sender.notify();
}

void axi_dwidth_converter::m_downsize_interface_txn_sender() {
	sc_core::sc_time zero_delay = SC_ZERO_TIME;
	if (wr_initiator_util->is_slave_ready()
			&& (m_interface_wr_payload_queue.size() != 0)) {
        m_log_msg = "Sending Write transaction " + 
            std::to_string(m_interface_wr_payload_queue.front()->get_address());
        XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::003",m_log_msg.c_str(), DEBUG); 
		
        wr_initiator_util->send_transaction(
				*m_interface_wr_payload_queue.front(), zero_delay);
		m_interface_wr_payload_queue.pop();
	}

	//For Read transaction
	zero_delay = SC_ZERO_TIME;
	if (rd_initiator_util->is_slave_ready()
			&& (m_interface_rd_payload_queue.size() != 0)) {
        m_log_msg = "Sending Read transaction " + 
            std::to_string(m_interface_rd_payload_queue.front()->get_address());
        XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::003",m_log_msg.c_str(), DEBUG); 
		
        rd_initiator_util->send_transaction(
				*m_interface_rd_payload_queue.front(), zero_delay);
		m_interface_rd_payload_queue.pop();
	}

}
void axi_dwidth_converter::m_downsize_interface_response_sender() {
	if (ratio <= 1)
		return;
	if (wr_initiator_util->is_resp_available()
			&& (m_response_mapper_downsize.size() != 0)
			&& (wr_target_util->is_master_ready())) {
		xtlm::aximm_payload* response_payld = wr_initiator_util->get_resp();
				response_payld->acquire();
        m_log_msg = "Sampled Response for Write : " + std::to_string(response_payld->get_address());
        XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::003",m_log_msg.c_str(), DEBUG); 

		std::list<xtlm::aximm_payload*>::iterator itrlist;
		std::map<xtlm::aximm_payload*, std::list<xtlm::aximm_payload*>*>::iterator itr;
		for (itr = m_response_mapper_downsize.begin();
				itr != m_response_mapper_downsize.end(); itr++) {
			itrlist = (std::find(itr->second->begin(), itr->second->end(),
					response_payld));
			if (itrlist != itr->second->end()) {
				itr->second->remove(response_payld);
				if (itr->second->size() == 0) {
					sc_core::sc_time zero_delay = SC_ZERO_TIME;
                    itr->first->set_axi_response_status(
                            response_payld->get_axi_response_status());
                    m_log_msg = "Sending Response for Write : " + 
                        std::to_string(itr->first->get_address());
                    XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::003",m_log_msg.c_str(), DEBUG); 
					
                    wr_target_util->send_resp(*(itr->first), zero_delay);
					delete (itr->second);
					m_response_mapper_downsize.erase(itr);
                    event_trig_wr_handler.notify(sc_core::SC_ZERO_TIME);
					break;
				}
				response_payld->release();
			}
		}
	}

	if (rd_initiator_util->is_data_available()
			&& (m_response_mapper_downsize.size() != 0)
			&& (rd_target_util->is_master_ready())) {
		xtlm::aximm_payload* response_payld = rd_initiator_util->get_data();
				response_payld->acquire();
        m_log_msg = "Sampled Response for Read : " + std::to_string(response_payld->get_address());
        XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::003",m_log_msg.c_str(), DEBUG); 

		std::list<xtlm::aximm_payload*>::iterator itrlist;
		std::map<xtlm::aximm_payload*, std::list<xtlm::aximm_payload*>*>::iterator itr;
		for (itr = m_response_mapper_downsize.begin();
				itr != m_response_mapper_downsize.end(); itr++) {
			itrlist = (std::find(itr->second->begin(), itr->second->end(),
					response_payld));
			if (itrlist != itr->second->end()) {
				itr->second->remove(response_payld);
				if (itr->second->size() == 0) {
					sc_core::sc_time zero_delay = SC_ZERO_TIME;
                    itr->first->set_axi_response_status(
                            response_payld->get_axi_response_status());
                    m_log_msg = "Sending Response for Read : " + 
                        std::to_string(itr->first->get_address());
                    XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::003",m_log_msg.c_str(), DEBUG); 
					
                    rd_target_util->send_data(*(itr->first), zero_delay);
					delete (itr->second);
                    event_trig_rd_handler.notify(sc_core::SC_ZERO_TIME);
					m_response_mapper_downsize.erase(itr);
					break;
				}
				//Release the transaction to memory manager
				response_payld->release();
			}
		}
	}
}
void axi_dwidth_converter::wr_upsizing() {
	auto si_addr = m_wr_trans->get_address();
	auto si_burst_len = m_wr_trans->get_burst_length();
	auto si_burst_size = m_wr_trans->get_burst_size();
	auto strb = m_wr_trans->get_byte_enable_ptr();
	auto data = m_wr_trans->get_data_ptr();
	auto aligned_start = (si_addr / MI_DATA_WIDTH) * MI_DATA_WIDTH;
	auto aligned_end = ((((si_addr / SI_DATA_WIDTH) * SI_DATA_WIDTH)
			+ (si_burst_len - 1) * si_burst_size) / MI_DATA_WIDTH)
			* MI_DATA_WIDTH;
	auto mi_len = (aligned_end - aligned_start) / MI_DATA_WIDTH + 1;

	xtlm::aximm_payload* t_trans = mem_manager->get_payload();
	t_trans->acquire();
	t_trans->deep_copy_from(*m_wr_trans);
	t_trans->set_address(si_addr);
    auto data_new = t_trans->create_and_get_data_ptr(mi_len * MI_DATA_WIDTH);
    memcpy(data_new,data,m_wr_trans->get_data_length());
    memset(data_new+m_wr_trans->get_data_length(),0,((mi_len * MI_DATA_WIDTH)-m_wr_trans->get_data_length()));
    auto str_new = t_trans->create_and_get_byte_enable_ptr(mi_len * MI_DATA_WIDTH);
    if(strb ) 
    {
        memcpy(str_new,strb, m_wr_trans->get_byte_enable_length());
        memset(str_new+m_wr_trans->get_byte_enable_length(),0,((mi_len * MI_DATA_WIDTH)-m_wr_trans->get_byte_enable_length()));
    }
    else 
    {
           memset(str_new, 0xFF, m_wr_trans->get_data_length());
           memset(str_new, 0x00, mi_len * MI_DATA_WIDTH - m_wr_trans->get_data_length());
    }
	t_trans->set_burst_size(MI_DATA_WIDTH );
	t_trans->set_burst_length(mi_len);
	m_upsize_wr_payld_queue.push(t_trans);
	m_response_mapper_upsize[t_trans] = m_wr_trans;
    
    m_log_msg = "Upsizing input Txn ";
    std::string payload_log; 
    m_wr_trans->get_log(payload_log, PAYLOAD_LOG_LEVEL);
    m_log_msg += payload_log;                
    XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::004",m_log_msg.c_str(), DEBUG); 

    m_log_msg = "Upsized output Txn ";
    t_trans->get_log(payload_log, PAYLOAD_LOG_LEVEL);
    m_log_msg += payload_log;                
    XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::004",m_log_msg.c_str(), DEBUG); 
	
    event_upsize_trig_txn_sender.notify();

}
void axi_dwidth_converter::rd_upsizing() {
	auto si_addr = m_rd_trans->get_address();
	auto si_burst_len = m_rd_trans->get_burst_length();
	auto si_burst_size = m_rd_trans->get_burst_size();
	auto strb = m_rd_trans->get_byte_enable_ptr();
	auto data = m_rd_trans->get_data_ptr();
	auto aligned_start = (si_addr / MI_DATA_WIDTH) * MI_DATA_WIDTH;
	auto aligned_end = ((((si_addr / SI_DATA_WIDTH) * SI_DATA_WIDTH)
			+ (si_burst_len - 1) * si_burst_size) / MI_DATA_WIDTH)
			* MI_DATA_WIDTH;
	auto mi_len = (aligned_end - aligned_start) / MI_DATA_WIDTH + 1;

	xtlm::aximm_payload* t_trans = mem_manager->get_payload();
	t_trans->acquire();
	t_trans->deep_copy_from(*m_rd_trans);
	t_trans->set_address(si_addr);
  auto data_new = t_trans->create_and_get_data_ptr(mi_len * MI_DATA_WIDTH);
  memcpy(data_new,data,m_rd_trans->get_data_length());
  memset(data_new+m_rd_trans->get_data_length(),0,((mi_len * MI_DATA_WIDTH)-m_rd_trans->get_data_length()));
  if (strb != nullptr) {
  auto str_new = t_trans->create_and_get_byte_enable_ptr(mi_len * MI_DATA_WIDTH);
  if(strb) 
  {
      memcpy(str_new,strb, m_rd_trans->get_byte_enable_length());
      memset(str_new+m_rd_trans->get_byte_enable_length(),0,((mi_len * MI_DATA_WIDTH)-m_rd_trans->get_byte_enable_length()));
  }
  else 
  {
         memset(str_new, 0xFF, m_rd_trans->get_data_length());
         memset(str_new, 0x00, mi_len * MI_DATA_WIDTH - m_rd_trans->get_data_length());
  }
  }
	t_trans->set_burst_size(MI_DATA_WIDTH);
	t_trans->set_burst_length(mi_len);
	m_upsize_rd_payld_queue.push(t_trans);
	m_response_mapper_upsize[t_trans] = m_rd_trans;
    
    m_log_msg = "Upsizing input Txn ";
    std::string payload_log; 
    m_rd_trans->get_log(payload_log, PAYLOAD_LOG_LEVEL);
    m_log_msg += payload_log;                
    XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::004",m_log_msg.c_str(), DEBUG); 

    m_log_msg = "Upsized output Txn ";
    t_trans->get_log(payload_log, PAYLOAD_LOG_LEVEL);
    m_log_msg += payload_log;                
    XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::004",m_log_msg.c_str(), DEBUG); 
	
    event_upsize_trig_txn_sender.notify();
}

void axi_dwidth_converter::m_upsize_interface_txn_sender() {
	sc_core::sc_time zero_delay = SC_ZERO_TIME;
	if (wr_initiator_util->is_slave_ready()
			&& (m_upsize_wr_payld_queue.size() != 0)) {
        
        m_log_msg = "Sending Write transaction " + 
            std::to_string(m_upsize_wr_payld_queue.front()->get_address());
        XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::005",m_log_msg.c_str(), DEBUG); 
		
        wr_initiator_util->send_transaction(*m_upsize_wr_payld_queue.front(),
				zero_delay);
		m_upsize_wr_payld_queue.pop();
	}

	//For Read transaction
	zero_delay = SC_ZERO_TIME;
	if (rd_initiator_util->is_slave_ready()
			&& (m_upsize_rd_payld_queue.size() != 0)) {

        m_log_msg = "Sending Read transaction " + 
            std::to_string(m_upsize_rd_payld_queue.front()->get_address());
        XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::005",m_log_msg.c_str(), DEBUG); 
		
        rd_initiator_util->send_transaction(*m_upsize_rd_payld_queue.front(),
				zero_delay);
		m_upsize_rd_payld_queue.pop();
	}

}
void axi_dwidth_converter::m_upsize_interface_response_sender() {
	if (ratio > 1)
		return;
	if (wr_initiator_util->is_resp_available()
			&& (m_response_mapper_upsize.size() != 0)
			&& (wr_target_util->is_master_ready())) {
		xtlm::aximm_payload* response_payld = wr_initiator_util->get_resp();
				response_payld->acquire();
        m_log_msg = "Sampled Response for Write : " + std::to_string(response_payld->get_address());
        XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::006",m_log_msg.c_str(), DEBUG); 

		std::map<xtlm::aximm_payload*, xtlm::aximm_payload*>::iterator itr;
		itr = (m_response_mapper_upsize.find(response_payld));
		if (itr != m_response_mapper_upsize.end()) {
			sc_core::sc_time zero_delay = SC_ZERO_TIME;
            m_response_mapper_upsize[response_payld]->set_axi_response_status(
                    response_payld->get_axi_response_status());
            m_log_msg = "Sending Response for Write : " + 
                std::to_string(m_response_mapper_upsize[response_payld]->get_address());
            XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::006",m_log_msg.c_str(), DEBUG);

			wr_target_util->send_resp(*m_response_mapper_upsize[response_payld],
					zero_delay);
			response_payld->release();
			m_response_mapper_upsize.erase(response_payld);
            event_trig_wr_handler.notify(sc_core::SC_ZERO_TIME);
		}
	}

	if (rd_initiator_util->is_data_available()
			&& (m_response_mapper_upsize.size() != 0)
			&& (rd_target_util->is_master_ready())) {
		xtlm::aximm_payload* response_payld = rd_initiator_util->get_data();
				response_payld->acquire();
        m_log_msg = "Sampled Response for Read : " + std::to_string(response_payld->get_address());
        XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::006",m_log_msg.c_str(), DEBUG); 

		std::map<xtlm::aximm_payload*, xtlm::aximm_payload*>::iterator itr;
		itr = m_response_mapper_upsize.find(response_payld);
		if (itr != m_response_mapper_upsize.end()) {
			sc_core::sc_time zero_delay = SC_ZERO_TIME;
            m_response_mapper_upsize[response_payld]->set_axi_response_status(
                    response_payld->get_axi_response_status());
            m_log_msg = "Sending Response for Read : " + 
                std::to_string(m_response_mapper_upsize[response_payld]->get_address());
            XSC_REPORT_INFO_VERB(m_logger, "DWIDTH::006",m_log_msg.c_str(), DEBUG);
        
            xtlm::aximm_payload *org_payload = m_response_mapper_upsize[response_payld];
            memcpy(org_payload->get_data_ptr(),response_payld->get_data_ptr(),org_payload->get_data_length());

			rd_target_util->send_data(*org_payload,
					zero_delay);
            
			response_payld->release();
			m_response_mapper_upsize.erase(response_payld);
            event_trig_rd_handler.notify(sc_core::SC_ZERO_TIME);
		}
	}
}

axi_dwidth_converter::~axi_dwidth_converter() {
	delete mem_manager;
	delete target_rd_socket;
	delete target_wr_socket;
	delete initiator_rd_socket;
	delete initiator_wr_socket;
	delete rd_target_util;
	delete wr_target_util;
	delete wr_initiator_util;
	delete rd_initiator_util;
}

