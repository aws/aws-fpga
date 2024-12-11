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

#include "smartconnect_xtlm.h"
#define s00_axi_WR_SLV_SKT_ID 0
#define s00_axi_RD_SLV_SKT_ID 1
//#define VERBOSE

smartconnect_xtlm::smartconnect_xtlm(sc_core::sc_module_name name,
    xsc::common_cpp::properties& _properties, map<string, string> _smc_properties,xsc::common_cpp::report_handler* report_handler) :
    sc_module(name), m_properties(_properties), smc_properties(_smc_properties) {

    m_report_handler = report_handler;

    smc_num_si = stoi(smc_properties["NUM_SI"]);
    smc_num_mi = stoi(smc_properties["NUM_MI"]);


        //Fill in m_properties
        for (int i = 0; i < smc_num_si; i++) {

         saxi_rd_req_vec.push_back  ( list<xtlm::aximm_payload*> ( 0));
         saxi_rd_resp_vec.push_back ( list<xtlm::aximm_payload*> ( 0));
         saxi_wr_req_vec.push_back  ( list<xtlm::aximm_payload*> ( 0));
         saxi_wr_resp_vec.push_back ( list<xtlm::aximm_payload*> ( 0));
         SI_m_properties.push_back  ( m_properties);

         std::string si_index;
         if (i < 10) {
            si_index = "S0" + std::to_string(i) + "_AXI.";
         } else {
            si_index = "S" + std::to_string(i) + "_AXI.";
         }

         SI_m_properties[i].addLong   ( "DATA_WIDTH"            , smc_properties[si_index + "CONFIG.DATA_WIDTH"]);
         SI_m_properties[i].addString ( "PROTOCOL"              , smc_properties[si_index + "CONFIG.PROTOCOL"]);
         SI_m_properties[i].addLong   ( "FREQ_HZ"               , smc_properties[si_index + "CONFIG.FREQ_HZ"]);
         SI_m_properties[i].addLong   ( "ID_WIDTH"              , smc_properties[si_index + "CONFIG.ID_WIDTH"]);
         SI_m_properties[i].addLong   ( "ADDR_WIDTH"            , smc_properties[si_index + "CONFIG.ADDR_WIDTH"]);
         SI_m_properties[i].addLong   ( "AWUSER_WIDTH"          , smc_properties[si_index + "CONFIG.AWUSER_WIDTH"]);
         SI_m_properties[i].addLong   ( "ARUSER_WIDTH"          , smc_properties[si_index + "CONFIG.ARUSER_WIDTH"]);
         SI_m_properties[i].addLong   ( "WUSER_WIDTH"           , smc_properties[si_index + "CONFIG.WUSER_WIDTH"]);
         SI_m_properties[i].addLong   ( "RUSER_WIDTH"           , smc_properties[si_index + "CONFIG.RUSER_WIDTH"]);
         SI_m_properties[i].addLong   ( "BUSER_WIDTH"           , smc_properties[si_index + "CONFIG.BUSER_WIDTH"]);
         SI_m_properties[i].addString ( "READ_WRITE_MODE"       , smc_properties[si_index + "CONFIG.READ_WRITE_MODE"]);
         SI_m_properties[i].addLong   ( "HAS_BURST"             , smc_properties[si_index + "CONFIG.HAS_BURST"]);
         SI_m_properties[i].addLong   ( "HAS_LOCK"              , smc_properties[si_index + "CONFIG.HAS_LOCK"]);
         SI_m_properties[i].addLong   ( "HAS_PROT"              , smc_properties[si_index + "CONFIG.HAS_PROT"]);
         SI_m_properties[i].addLong   ( "HAS_CACHE"             , smc_properties[si_index + "CONFIG.HAS_CACHE"]);
         SI_m_properties[i].addLong   ( "HAS_QOS"               , smc_properties[si_index + "CONFIG.HAS_QOS"]);
         SI_m_properties[i].addLong   ( "HAS_REGION"            , smc_properties[si_index + "CONFIG.HAS_REGION"]);
         SI_m_properties[i].addLong   ( "HAS_WSTRB"             , smc_properties[si_index + "CONFIG.HAS_WSTRB"]);
         SI_m_properties[i].addLong   ( "HAS_BRESP"             , smc_properties[si_index + "CONFIG.HAS_BRESP"]);
         SI_m_properties[i].addLong   ( "HAS_RRESP"             , smc_properties[si_index + "CONFIG.HAS_RRESP"]);
         SI_m_properties[i].addLong   ( "SUPPORTS_NARROW_BURST" , smc_properties[si_index + "CONFIG.SUPPORTS_NARROW_BURST"]);
         SI_m_properties[i].addLong   ( "NUM_READ_OUTSTANDING"  , smc_properties[si_index + "CONFIG.NUM_READ_OUTSTANDING"]);
         SI_m_properties[i].addLong   ( "NUM_WRITE_OUTSTANDING" , smc_properties[si_index + "CONFIG.NUM_WRITE_OUTSTANDING"]);
         SI_m_properties[i].addLong   ( "MAX_BURST_LENGTH"      , smc_properties[si_index + "CONFIG.MAX_BURST_LENGTH"]);
         SI_m_properties[i].addFloat  ( "PHASE"                 , smc_properties[si_index + "CONFIG.PHASE"]);
         SI_m_properties[i].addString ( "CLK_DOMAIN"            , smc_properties[si_index + "CONFIG.CLK_DOMAIN"]);
         SI_m_properties[i].addLong   ( "NUM_READ_THREADS"      , smc_properties[si_index + "CONFIG.NUM_READ_THREADS"]);
         SI_m_properties[i].addLong   ( "NUM_WRITE_THREADS"     , smc_properties[si_index + "CONFIG.NUM_WRITE_THREADS"]);
         SI_m_properties[i].addLong   ( "RUSER_BITS_PER_BYTE"   , smc_properties[si_index + "CONFIG.RUSER_BITS_PER_BYTE"]);
         SI_m_properties[i].addLong   ( "WUSER_BITS_PER_BYTE"   , smc_properties[si_index + "CONFIG.WUSER_BITS_PER_BYTE"]);
         SI_m_properties[i].addLong   ( "INSERT_VIP"            , smc_properties[si_index + "CONFIG.INSERT_VIP"]);
         SI_m_properties[i].addLong   ( "NUM_SEG"               , smc_properties[si_index + "NUM_SEG"]);
         SI_m_properties[i].addLong   ( "IS_CASCADED"           , smc_properties[si_index + "IS_CASCADED"]);

         int SI_num_seg = SI_m_properties[i].getInt("NUM_SEG");

         for (int j = 0; j < SI_num_seg; j++) {
            std::string seg_index;
            int num_mi;
            if (j < 10) {
               seg_index = "SEG00" + std::to_string(j) + ".";
            } else if (j >= 10 && j < 100 ) {
               seg_index = "SEG0" + std::to_string(j) + ".";
            } else {
               seg_index = "SEG" + std::to_string(j) + ".";
            }

            SI_m_properties[i].addString ( seg_index + "BASE_ADDR"      , smc_properties[si_index + seg_index + "BASE_ADDR"]);
            SI_m_properties[i].addLong   ( seg_index + "SIZE"           , smc_properties[si_index + seg_index + "SIZE"]);
            SI_m_properties[i].addLong   ( seg_index + "SUPPORTS_READ"  , smc_properties[si_index + seg_index + "SUPPORTS_READ"]);
            SI_m_properties[i].addLong   ( seg_index + "SUPPORTS_WRITE" , smc_properties[si_index + seg_index + "SUPPORTS_WRITE"]);
            SI_m_properties[i].addLong   ( seg_index + "SECURE_READ"    , smc_properties[si_index + seg_index + "SECURE_READ"]);
            SI_m_properties[i].addLong   ( seg_index + "SECURE_WRITE"   , smc_properties[si_index + seg_index + "SECURE_WRITE"]);
            SI_m_properties[i].addBitString ( seg_index + "SEP_ROUTE"   , smc_properties[si_index + seg_index + "SEP_ROUTE"].substr(2), 64);
            SI_m_properties[i].addString ( seg_index + "PROTOCOL"       , smc_properties[si_index + seg_index + "PROTOCOL"]);
            SI_m_properties[i].addLong   ( seg_index + "DATA_WIDTH"     , smc_properties[si_index + seg_index + "DATA_WIDTH"]);
         }
        }


        //Fill in m_properties
        for (int i = 0; i < smc_num_mi; i++) {

         maxi_wr_req_vec.push_back       ( list<xtlm::aximm_payload*> ( 0));
         maxi_wr_resp_vec.push_back      ( list<xtlm::aximm_payload*> ( 0));
         maxi_rd_req_vec.push_back       ( list<xtlm::aximm_payload*> ( 0));
         maxi_rd_resp_vec.push_back      ( list<xtlm::aximm_payload*> ( 0));
         maxi_wr_req_numsi_vec.push_back ( list<unsigned int>         ( 0));
         maxi_rd_req_numsi_vec.push_back ( list<unsigned int>         ( 0));
         maxi_rd_req_vec_itr.push_back   ( list<xtlm::aximm_payload*>::iterator (0));
         MI_m_properties.push_back       (m_properties);

         maxi_wr_req_cnt.push_back(0); 
         maxi_rd_req_cnt.push_back(0);

         std::string mi_index;
         if (i < 10) {
            mi_index = "M0" + std::to_string(i) + "_AXI.";
         } else {
            mi_index = "M" + std::to_string(i) + "_AXI.";
         }

         MI_m_properties[i].addLong   ( "DATA_WIDTH"            , smc_properties[mi_index + "CONFIG.DATA_WIDTH"]);
         MI_m_properties[i].addString ( "PROTOCOL"              , smc_properties[mi_index + "CONFIG.PROTOCOL"]);
         MI_m_properties[i].addLong   ( "FREQ_HZ"               , smc_properties[mi_index + "CONFIG.FREQ_HZ"]);
         MI_m_properties[i].addLong   ( "ID_WIDTH"              , smc_properties[mi_index + "CONFIG.ID_WIDTH"]);
         MI_m_properties[i].addLong   ( "ADDR_WIDTH"            , smc_properties[mi_index + "CONFIG.ADDR_WIDTH"]);
         MI_m_properties[i].addLong   ( "AWUSER_WIDTH"          , smc_properties[mi_index + "CONFIG.AWUSER_WIDTH"]);
         MI_m_properties[i].addLong   ( "ARUSER_WIDTH"          , smc_properties[mi_index + "CONFIG.ARUSER_WIDTH"]);
         MI_m_properties[i].addLong   ( "WUSER_WIDTH"           , smc_properties[mi_index + "CONFIG.WUSER_WIDTH"]);
         MI_m_properties[i].addLong   ( "RUSER_WIDTH"           , smc_properties[mi_index + "CONFIG.RUSER_WIDTH"]);
         MI_m_properties[i].addLong   ( "BUSER_WIDTH"           , smc_properties[mi_index + "CONFIG.BUSER_WIDTH"]);
         MI_m_properties[i].addString ( "READ_WRITE_MODE"       , smc_properties[mi_index + "CONFIG.READ_WRITE_MODE"]);
         MI_m_properties[i].addLong   ( "HAS_BURST"             , smc_properties[mi_index + "CONFIG.HAS_BURST"]);
         MI_m_properties[i].addLong   ( "HAS_LOCK"              , smc_properties[mi_index + "CONFIG.HAS_LOCK"]);
         MI_m_properties[i].addLong   ( "HAS_PROT"              , smc_properties[mi_index + "CONFIG.HAS_PROT"]);
         MI_m_properties[i].addLong   ( "HAS_CACHE"             , smc_properties[mi_index + "CONFIG.HAS_CACHE"]);
         MI_m_properties[i].addLong   ( "HAS_QOS"               , smc_properties[mi_index + "CONFIG.HAS_QOS"]);
         MI_m_properties[i].addLong   ( "HAS_REGION"            , smc_properties[mi_index + "CONFIG.HAS_REGION"]);
         MI_m_properties[i].addLong   ( "HAS_WSTRB"             , smc_properties[mi_index + "CONFIG.HAS_WSTRB"]);
         MI_m_properties[i].addLong   ( "HAS_BRESP"             , smc_properties[mi_index + "CONFIG.HAS_BRESP"]);
         MI_m_properties[i].addLong   ( "HAS_RRESP"             , smc_properties[mi_index + "CONFIG.HAS_RRESP"]);
         MI_m_properties[i].addLong   ( "SUPPORTS_NARROW_BURST" , smc_properties[mi_index + "CONFIG.SUPPORTS_NARROW_BURST"]);
         MI_m_properties[i].addLong   ( "NUM_READ_OUTSTANDING"  , smc_properties[mi_index + "CONFIG.NUM_READ_OUTSTANDING"]);
         MI_m_properties[i].addLong   ( "NUM_WRITE_OUTSTANDING" , smc_properties[mi_index + "CONFIG.NUM_WRITE_OUTSTANDING"]);
         MI_m_properties[i].addLong   ( "MAX_BURST_LENGTH"      , smc_properties[mi_index + "CONFIG.MAX_BURST_LENGTH"]);
         MI_m_properties[i].addFloat  ( "PHASE"                 , smc_properties[mi_index + "CONFIG.PHASE"]);
         MI_m_properties[i].addString ( "CLK_DOMAIN"            , smc_properties[mi_index + "CONFIG.CLK_DOMAIN"]);
         MI_m_properties[i].addLong   ( "NUM_READ_THREADS"      , smc_properties[mi_index + "CONFIG.NUM_READ_THREADS"]);
         MI_m_properties[i].addLong   ( "NUM_WRITE_THREADS"     , smc_properties[mi_index + "CONFIG.NUM_WRITE_THREADS"]);
         MI_m_properties[i].addLong   ( "RUSER_BITS_PER_BYTE"   , smc_properties[mi_index + "CONFIG.RUSER_BITS_PER_BYTE"]);
         MI_m_properties[i].addLong   ( "WUSER_BITS_PER_BYTE"   , smc_properties[mi_index + "CONFIG.WUSER_BITS_PER_BYTE"]);
         MI_m_properties[i].addLong   ( "INSERT_VIP"            , smc_properties[mi_index + "CONFIG.INSERT_VIP"]);
         MI_m_properties[i].addLong   ( "IS_CASCADED"           , smc_properties[mi_index + "IS_CASCADED"]);

         MI_burst_length.push_back(stoi(smc_properties[mi_index + "CONFIG.MAX_BURST_LENGTH"]));
         
         uint64_t burst_size = MI_m_properties[i].getLongLong("DATA_WIDTH")/8;
	    if (m_report_handler->get_verbosity_level()
	    		== xsc::common_cpp::VERBOSITY::DEBUG) {
	    	m_ss.str("");
	    	m_ss << this->name() << "Pushing MI_burst_size: " << burst_size << std::endl;
	    	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	    			DEBUG);
	    }
         
         MI_burst_size.push_back(burst_size);

        }


    trans_done = false;
    create_wr_resp = false;
    s_trans = NULL;
    m_trans = NULL;

    //Default burst_length and burst_size
    m_rd_burst_length = 1;
    m_wr_burst_length = 1;
    m_rd_burst_size = 4;
    m_wr_burst_size = 4;

    slave_wr_req = -1;
    slave_rd_req = -1;

    bad_saxi_wr_trans = -1;
    bad_saxi_rd_trans = -1;


    payload_msg = "";
    
    //Memory Manager for payloads
    mem_manager = new xtlm::xtlm_aximm_mem_manager();

    for (int i = 0; i < smc_num_si; i++) {

         //Instantiate utils and sockets
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "Initializing sockets and utils SXI: " << std::dec << i << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
		saxi_rd_util.push_back(
				new smartconnect_xtlm_impl::target_rd_util(
						std::string("saxi_rd_util_" + std::to_string(i)).c_str(),
						xtlm::aximm::TRANSACTION, 32, i, this));
		saxi_wr_util.push_back(
				new smartconnect_xtlm_impl::target_wr_util(
						std::string("saxi_wr_util_" + std::to_string(i)).c_str(),
						xtlm::aximm::TRANSACTION, 32, i, this));

		//Sockets Initialization
		saxi_wr_socket.push_back(
				new xtlm::xtlm_aximm_target_socket(
						std::string("saxi_rd_socket_" + std::to_string(i)).c_str(),
						32));
		saxi_rd_socket.push_back(
				new xtlm::xtlm_aximm_target_socket(
						std::string("saxi_wr_socket_" + std::to_string(i)).c_str(),
						32));

	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "Binding sockets and utils SXI: " << std::dec << i << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
        (*saxi_wr_socket[i])(saxi_wr_util[i]->wr_socket);
        (*saxi_rd_socket[i])(saxi_rd_util[i]->rd_socket);
    }

        
    // TODO: change iterator name
    for (int num_mi = 0; num_mi < smc_num_mi; num_mi++) {
	    if (m_report_handler->get_verbosity_level()
	    		== xsc::common_cpp::VERBOSITY::DEBUG) {
	    	m_ss.str("");
	    	m_ss << this->name() << "Initializing sockets and utils MXI: " << std::dec << num_mi << std::endl;
	    	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	    			DEBUG);
	    }
		maxi_rd_util.push_back(
				new xtlm::xtlm_aximm_initiator_rd_socket_util(
						std::string("maxi_rd_util_" + std::to_string(num_mi)).c_str(),
						xtlm::aximm::TRANSACTION, 32));
		maxi_wr_util.push_back(
				new xtlm::xtlm_aximm_initiator_wr_socket_util(
						std::string("maxi_wr_util_" + std::to_string(num_mi)).c_str(),
						xtlm::aximm::TRANSACTION, 32));

		maxi_rd_socket.push_back(
				new xtlm::xtlm_aximm_initiator_socket(
						std::string("maxi_rd_socket_" + std::to_string(num_mi)).c_str(),
						32));
		maxi_wr_socket.push_back(
				new xtlm::xtlm_aximm_initiator_socket(
						std::string("maxi_wr_socket_" + std::to_string(num_mi)).c_str(),
						32));

	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "Binding sockets and utils MXI: " << std::dec << num_mi << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
        maxi_rd_util[num_mi]->rd_socket.bind(*maxi_rd_socket[num_mi]);
        maxi_wr_util[num_mi]->wr_socket.bind(*maxi_wr_socket[num_mi]);

    }


    //Create methods sensitive to events
	if (m_report_handler->get_verbosity_level()
			== xsc::common_cpp::VERBOSITY::DEBUG) {
		m_ss.str("");
		m_ss << this->name() << "Initializing SC_METHODS"  << std::endl;
		XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
				DEBUG);
	}
    SC_METHOD(process_saxi_wr_req);
    sensitive << check_saxi_wr_req;
    for (int num_si = 0; num_si < smc_num_si; num_si++) {
        sensitive << saxi_wr_util[num_si]->transaction_available;
    }
    dont_initialize();

    SC_METHOD(process_maxi_wr_req);
    sensitive << initiate_maxi_wr_req;
    for (int num_mi = 0; num_mi < smc_num_mi; num_mi++) {
        sensitive << maxi_wr_util[num_mi]->transaction_sampled;
    }
    dont_initialize();

    SC_METHOD(process_maxi_wr_resp);
    for (int num_mi = 0; num_mi < smc_num_mi; num_mi++) {
        sensitive << maxi_wr_util[num_mi]->resp_available;
    }
    dont_initialize();

    SC_METHOD(process_saxi_wr_resp);
    sensitive << send_wr_resp;
    dont_initialize();

    SC_METHOD(process_saxi_rd_req);
    sensitive << check_saxi_rd_req;
    for (int num_si = 0; num_si < smc_num_si; num_si++) {
        sensitive << saxi_rd_util[num_si]->transaction_available;
    }
    dont_initialize();

    SC_METHOD(process_maxi_rd_req);
    sensitive << initiate_maxi_rd_req;
    for (int num_mi = 0; num_mi < smc_num_mi; num_mi++) {
        sensitive << maxi_rd_util[num_mi]->transaction_sampled;
    }
    dont_initialize();

    SC_METHOD(process_maxi_rd_resp);
    for (int num_mi = 0; num_mi < smc_num_mi; num_mi++) {
        sensitive << maxi_rd_util[num_mi]->data_available;
    }
    dont_initialize();

    SC_METHOD(process_saxi_rd_resp);
    sensitive << send_saxi_rd_resp;
    dont_initialize();
	if (m_report_handler->get_verbosity_level()
			== xsc::common_cpp::VERBOSITY::DEBUG) {
		m_ss.str("");
		m_ss << this->name() << "DONE Initializing SC_METHODS" << std::endl;
		XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
				DEBUG);
	}
}

smartconnect_xtlm::~smartconnect_xtlm() {
    // TODO; revise to vector iteration.
   // for (int num_si = 0; num_si < smc_num_si; num_si++) {
   //    delete saxi_wr_socket[num_si];
   //    delete saxi_rd_socket[num_si];
   // }
   // for (int num_mi = 0; num_mi < smc_num_mi; num_mi++) {
   //    delete maxi_wr_socket[num_mi];
   //    delete maxi_rd_socket[num_mi];
   // }
   delete m_report_handler;
}

void smartconnect_xtlm::print_header(std::string str) {
   std::string s = "BEGIN " + std::string(this->name()) + " " + str;

   if (s.length() <= 56) {
      int num_space = (56 - s.length())/2;
      for (int i = 0; i < num_space; i++) {
         s = " " + s;
      }
   }

	if (m_report_handler->get_verbosity_level()
			== xsc::common_cpp::VERBOSITY::DEBUG) {
		m_ss.str("");
		m_ss << this->name() << "\n**********************************************************\n"
          << s << "\n"
          << "**********************************************************\n\n"
          << std::endl;
		XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
				DEBUG);
	}
}

void smartconnect_xtlm::print_footer(std::string str) {
   std::string s = "END " + std::string(this->name()) + " " + str;

   if (s.length() <= 56) {
      int num_space = (56 - s.length())/2;
      for (int i = 0; i < num_space; i++) {
         s = " " + s;
      }
   }

	if (m_report_handler->get_verbosity_level()
			== xsc::common_cpp::VERBOSITY::DEBUG) {
		m_ss.str("");
		m_ss << this->name() << "\n**********************************************************\n"
       << s << "\n"
       << "**********************************************************\n\n" << std::endl;
		XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
				DEBUG);
	}
}

void smartconnect_xtlm::print_log(std::string port, int port_id, std::string rw, std::string action, xtlm::aximm_payload* &trans_ptr) {
	if (m_report_handler->get_verbosity_level()
			== xsc::common_cpp::VERBOSITY::DEBUG) {
	  	m_ss.str("");
	  	m_ss << this->name() << std::setw(35) << std::left << std::string(this->name()) << ":"
         << std::setw(5) << std::left << port << std::setw(5) << std::left << std::dec << port_id
         << std::setw(8) << std::left << rw
         << std::setw(25) << std::left << action
         << std::setw(8) << std::left << "TRANS:" << std::setw(10) << std::left << trans_ptr
         << "\n";
	  	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	  			DEBUG);
	}
}
int smartconnect_xtlm::is_address_hit_lite(xtlm::aximm_payload* trans_ptr, int num_si) {
   unsigned long long addr = trans_ptr->get_address();
   xtlm::xtlm_command command = trans_ptr->get_command();
   int slave;
   int si_sep_route;
   unsigned long long sep_route;
   bool si_cascaded = (SI_m_properties[num_si].getInt("IS_CASCADED") == 1);
   int SI_num_seg = SI_m_properties[num_si].getInt("NUM_SEG");

	if (m_report_handler->get_verbosity_level()
			== xsc::common_cpp::VERBOSITY::DEBUG) {
		m_ss.str("");
		m_ss << this->name() << "is_address_hit: SI_num_seg: " << std::dec << SI_num_seg << std::endl;
		XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
				DEBUG);
	}

   for (int i = 0; i < SI_num_seg; i++) {
      std::string seg_index;
      if (i < 10) {
         seg_index = "SEG00" + std::to_string(i) + ".";
      } else if (i >= 10 && i < 100 ) {
         seg_index = "SEG0" + std::to_string(i) + ".";
      } else {
         seg_index = "SEG" + std::to_string(i) + ".";
      }


      int size                     = SI_m_properties[num_si].getInt( seg_index + "SIZE");
      unsigned long long baseaddr  = stoll(SI_m_properties[num_si].getString( seg_index + "BASE_ADDR"), nullptr, 16);
      unsigned long long high_addr = baseaddr + (unsigned long long) exp2(size);
      int num_mi_log2              = ceil(log2(smc_num_mi));


      if (si_cascaded) {
         smartconnect_extension* exten = trans_ptr->get_extension<smartconnect_extension>();
         sep_route                     = exten->get_sep_route();
//         sep_route                     = 0;
         slave                         = ((1 << num_mi_log2) - 1) & sep_route;
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() <<  "is_address_hit(): SI " << num_si << " IS CASCADED: sep_route: " << std::hex << sep_route << "\n"
            << "is_address_hit(): SI " << num_si << " IS CASCADED: exten is: " << exten << "\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
      } else {
         sep_route = SI_m_properties[num_si].getLongLong( seg_index + "SEP_ROUTE");
         slave     = ((1 << num_mi_log2) - 1) & sep_route;
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "is_address_hit(): SI " << num_si << " NOT CASCADED: sep_route: 0x" << std::hex << sep_route << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
      }

	  if (m_report_handler->get_verbosity_level()
	  		== xsc::common_cpp::VERBOSITY::DEBUG) {
	  	m_ss.str("");
	  	m_ss << this->name() << std::hex << "Address " << baseaddr << " : " << high_addr << std::endl;
	  	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	  			DEBUG);
	  }

      if ( (baseaddr <= addr && addr < high_addr) || si_cascaded ) {

         if (command == xtlm::xtlm_command::XTLM_READ_COMMAND) {
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "SMARTCONNECT_XTLM: is_address_hit(): Address hit slave_rd_req: " << slave_rd_req << "\n"
            << "                   Base address: " << std::hex << baseaddr << "\n"
            << "                   High address: " << std::hex << high_addr - 1 << "\n"
            << "                   Slave       : " << slave << "\n"
            << "                   MI_burst_length[" << i << "]: " << MI_burst_length[slave] << "\n"
            << "                   MI_burst_size[" << i << "]: " << MI_burst_size[slave] << "\n\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
         } else if (command == xtlm::xtlm_command::XTLM_WRITE_COMMAND) {
	        if (m_report_handler->get_verbosity_level()
	        		== xsc::common_cpp::VERBOSITY::DEBUG) {
	        	m_ss.str("");
	        	m_ss << this->name() << "SMARTCONNECT_XTLM: is_address_hit(): Address hit slave_wr_req: " << slave_wr_req << "\n"
               << "                   Base address: " << std::hex << baseaddr << "\n"
               << "                   High address: " << std::hex << high_addr - 1 << "\n"
               << "                   Slave       : " << slave << "\n"
               << "                   MI_burst_length[" << i << "]: " << MI_burst_length[slave] << "\n"
               << "                   MI_burst_size[" << i << "]: " << MI_burst_size[slave] << "\n\n";
	        	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	        			DEBUG);
	        }
         }

         //create extension payload if MI is cascaded
         
         if (MI_m_properties[slave].getInt("IS_CASCADED") == 1) {
            si_sep_route = (sep_route >> num_mi_log2);
            smartconnect_extension* exten =nullptr;
            trans_ptr->get_extension(exten);
            if (exten!=nullptr) {
              exten->set_sep_route(si_sep_route);
            } else {
              exten = new smartconnect_extension();
              exten->set_sep_route(si_sep_route);
              trans_ptr->set_auto_extension(exten);
            }
	        if (m_report_handler->get_verbosity_level()
	        		== xsc::common_cpp::VERBOSITY::DEBUG) {
	        	m_ss.str("");
	        	m_ss << this->name() << "is_address_hit(): MI " << slave << " IS CASCADED: sep_route is: " << std::bitset<64>(sep_route) << "\n"
               << "is_address_hit(): MI " << slave << " IS CASCADED: setting si_sep_route: " << std::bitset<64>(si_sep_route) << "\n\n";
	        	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	        			DEBUG);
	        }
         }

         return slave;
      }
   }
   return -1;
}

bool smartconnect_xtlm::is_address_hit(xtlm::aximm_payload* &trans_ptr, int num_si, unsigned long long &si_sep_route, int &m_burst_length, unsigned int &m_burst_size) {
   unsigned long long addr = trans_ptr->get_address();
   xtlm::xtlm_command command = trans_ptr->get_command();
   int slave;
   unsigned long long sep_route;
   bool si_cascaded = (SI_m_properties[num_si].getInt("IS_CASCADED") == 1);
   int SI_num_seg = SI_m_properties[num_si].getInt("NUM_SEG");

	if (m_report_handler->get_verbosity_level()
			== xsc::common_cpp::VERBOSITY::DEBUG) {
		m_ss.str("");
		m_ss << this->name() << "is_address_hit: SI_num_seg: " << std::dec << SI_num_seg << std::endl;
		XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
				DEBUG);
	}

   for (int i = 0; i < SI_num_seg; i++) {
      std::string seg_index;
      if (i < 10) {
         seg_index = "SEG00" + std::to_string(i) + ".";
      } else if (i >= 10 && i < 100 ) {
         seg_index = "SEG0" + std::to_string(i) + ".";
      } else {
         seg_index = "SEG" + std::to_string(i) + ".";
      }

//      int      size      = stoi(smc_properties[si_index + seg_index + "SIZE"]);
//      uint64_t baseaddr  = stoll(smc_properties[si_index + seg_index + "BASE_ADDR"], nullptr, 16);
//      uint64_t high_addr = baseaddr + (int) (std::pow(2, size));
//      int      slave     = stoi(smc_properties[si_index + seg_index + "SEP_ROUTE"].substr(2), nullptr, 2);

      int size                     = SI_m_properties[num_si].getInt( seg_index + "SIZE");
      unsigned long long baseaddr  = stoll(SI_m_properties[num_si].getString( seg_index + "BASE_ADDR"), nullptr, 16);
      unsigned long long high_addr = baseaddr + (unsigned long long) exp2(size);
      int num_mi_log2              = ceil(log2(smc_num_mi));

      if (si_cascaded) {
         smartconnect_extension* exten = trans_ptr->get_extension<smartconnect_extension>();
         sep_route                     = exten->get_sep_route();
//         sep_route                     = 0;
         slave                         = ((1 << num_mi_log2) - 1) & sep_route;
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "is_address_hit(): SI " << num_si << " IS CASCADED: sep_route: " << std::hex << sep_route << "\n"
            << "is_address_hit(): SI " << num_si << " IS CASCADED: exten is: " << exten << "\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
      } else {
         sep_route = SI_m_properties[num_si].getLongLong( seg_index + "SEP_ROUTE");
         slave     = ((1 << num_mi_log2) - 1) & sep_route;
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "is_address_hit(): SI " << num_si << " NOT CASCADED: sep_route: 0x" << std::hex << sep_route << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
      }

	  if (m_report_handler->get_verbosity_level()
	  		== xsc::common_cpp::VERBOSITY::DEBUG) {
	  	m_ss.str("");
	  	m_ss << this->name() << std::hex << "Address " << baseaddr << " : " << high_addr << std::endl;
	  	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	  			DEBUG);
	  }

      if ( (baseaddr <= addr && addr < high_addr) || si_cascaded ) {

         m_burst_length = get_max_burst_length(SI_m_properties[num_si].getString( seg_index + "PROTOCOL"));
         m_burst_size = SI_m_properties[num_si].getInt( seg_index + "DATA_WIDTH") / 8; 

         if (command == xtlm::xtlm_command::XTLM_READ_COMMAND) {
            slave_rd_req = slave;
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "SMARTCONNECT_XTLM: is_address_hit(): Address hit slave_rd_req: " << slave_rd_req << "\n"
            << "                   Base address: " << std::hex << baseaddr << "\n"
            << "                   High address: " << std::hex << high_addr - 1 << "\n"
            << "                   Slave       : " << slave << "\n"
            << "                   MI_burst_length[" << i << "]: " << MI_burst_length[slave] << "\n"
            << "                   MI_burst_size[" << i << "]: " << MI_burst_size[slave] << "\n\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
         } else if (command == xtlm::xtlm_command::XTLM_WRITE_COMMAND) {
            slave_wr_req = slave;
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "SMARTCONNECT_XTLM: is_address_hit(): Address hit slave_wr_req: " << slave_wr_req << "\n"
            << "                   Base address: " << std::hex << baseaddr << "\n"
            << "                   High address: " << std::hex << high_addr - 1 << "\n"
            << "                   Slave       : " << slave << "\n"
            << "                   MI_burst_length[" << i << "]: " << MI_burst_length[slave] << "\n"
            << "                   MI_burst_size[" << i << "]: " << MI_burst_size[slave] << "\n\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
         }

         //create extension payload if MI is cascaded
         if (MI_m_properties[slave].getInt("IS_CASCADED") == 1) {
            si_sep_route = (sep_route >> num_mi_log2);
	        if (m_report_handler->get_verbosity_level()
	        		== xsc::common_cpp::VERBOSITY::DEBUG) {
	        	m_ss.str("");
	        	m_ss << this->name() << "is_address_hit(): MI " << slave << " IS CASCADED: sep_route is: " << std::bitset<64>(sep_route) << "\n"
                << "is_address_hit(): MI " << slave << " IS CASCADED: setting si_sep_route: " << std::bitset<64>(si_sep_route) << "\n";
	        	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	        			DEBUG);
	        }
         }

         return true;
      }
   }
   return false;
}

int smartconnect_xtlm::get_max_burst_length(std::string protocol) {

   if (protocol == "AXI4") {
      return 256;
   } else if (protocol == "AXI3") {
      return 16;
   } else {
      return 1;
   }
}

int smartconnect_xtlm::decode_burst_size(unsigned int burst_size) {
   switch (burst_size) {
      case 0:
         return 1;
      case 1:
         return 2;
      case 2:
         return 4;
      case 3:
         return 8;
      case 4:
         return 16;
      case 5:
         return 32;
      case 6:
         return 64;
      case 7:
         return 128;
   }

   return 1;
}

int smartconnect_xtlm::encode_burst_size(int num_burst) {
   if (num_burst == 1) { return 0; }
   else if (num_burst == 2) { return 1; }
   else if (num_burst >  2 && num_burst <= 4)   { return 2; }
   else if (num_burst >  4 && num_burst <= 8)   { return 3; }
   else if (num_burst >  8 && num_burst <= 16)  { return 4; }
   else if (num_burst > 16 && num_burst <= 32)  { return 5; }
   else if (num_burst > 32 && num_burst <= 64)  { return 6; }
   else if (num_burst > 64 && num_burst <= 128) { return 7; }
   else { return 0; }
}

smartconnect_xtlm::transaction_status smartconnect_xtlm::get_transaction_status(xtlm::aximm_payload* &trans_ptr, int num_si, 
                                          unsigned long long &si_sep_route, int &m_burst_length, unsigned int &m_burst_size) {

   if (trans_ptr->get_burst_type() == XAXI_BURST_FIXED || (SI_m_properties[num_si].getInt("HAS_BURST") == 0 && trans_ptr->get_burst_type() == XAXI_BURST_WRAP)) {
      trans_ptr->set_response_status(xtlm::XTLM_BURST_ERROR_RESPONSE);
      return TRANSACTION_BURST_ERROR;
   }

   if (!is_address_hit(trans_ptr, num_si, si_sep_route, m_burst_length, m_burst_size)) {
      trans_ptr->set_response_status(xtlm::XTLM_ADDRESS_ERROR_RESPONSE);
      return TRANSACTION_ADDRESS_ERROR;
   }

   return TRANSACTION_OK;
}

xtlm::aximm_payload* smartconnect_xtlm::get_dummy_transaction(xtlm::xtlm_command cmd) {

   xtlm::aximm_payload* trans_ptr = mem_manager->get_payload();
   trans_ptr->set_command(cmd);
   trans_ptr->set_axi_id(static_cast<unsigned int>(0));
   trans_ptr->set_burst_type(XAXI_BURST_INCR); //XAXI_BURST_INCR
   trans_ptr->set_burst_length(1);
   trans_ptr->set_burst_size(3);

   return trans_ptr;
}

void smartconnect_xtlm::create_burst_transaction(std::list<xtlm::aximm_payload*> &saxi_vec, std::list<xtlm::aximm_payload*> &maxi_vec, 
                                       std::list<unsigned int> &numsi_vec, int m_burst_length, unsigned int m_burst_size, int &req_cnt, unsigned int numsi,
                                       unsigned int nummi, unsigned long long si_sep_route) {

   print_header("create_burst_transaction()");

   xtlm::aximm_payload* trans_ptr = saxi_vec.back();
   unsigned int s_axi_id = trans_ptr->get_axi_id();
   int s_burst_length = trans_ptr->get_burst_length();
   int s_burst_cnt = s_burst_length;
   int s_burst_size = trans_ptr->get_burst_size();
   int s_num_burst = s_burst_size;
   int s_data_size = trans_ptr->get_data_length();
   //This is absolute s_data_size buffer
   int s_data_size_abs = trans_ptr->get_data_length();
   unsigned char* s_data_ptr = trans_ptr->get_data_ptr();
   unsigned char* s_data_en_ptr = trans_ptr->get_byte_enable_ptr();
   int s_data_ptr_indx = 0;
   int s_data_ptr_indx_high = s_data_size_abs - 1;

	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "BEGIN Incoming Paylod information" << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	    	trans_ptr->get_log(payload_msg, 3);
	     	m_ss.str("");
	     	m_ss << this->name() << payload_msg << std::endl;
            m_ss << "END Incoming Payload information\n\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     	payload_msg = "";
	     }

//   int m_num_burst = decode_burst_size(m_burst_size);
   int m_burst_cnt = m_burst_length;
   int m_num_burst = m_burst_size;
   int m_data_size = m_burst_cnt * m_num_burst;
   bool mi_cascaded = (MI_m_properties[nummi].getInt("IS_CASCADED") == 1);

   unsigned long long address = trans_ptr->get_address();

   if(m_burst_size > s_burst_size) {
      int si_size = encode_burst_size(s_burst_size);
      int mi_size = encode_burst_size(m_burst_size);
      int valid_byte = address & ((int) (std::pow(2, mi_size)) - 1);
      int mask = 0xFFFFFFFF << si_size;
      //Modify s_data_size buffer since the address on MI is unaligned
      s_data_size += (valid_byte & mask);
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << std::dec << "s_data_size buffer modified to:" << s_data_size << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
   }

   //Total new MI transactions generate
   int num_mi_transaction = 1;
   if (s_data_size > m_data_size) {
      num_mi_transaction = ( s_data_size % m_data_size ) ? (s_data_size / m_data_size) + 1 : 
                                                           (s_data_size / m_data_size);
   }

   if(!mi_cascaded) {
      if (trans_ptr->get_command() == xtlm::XTLM_WRITE_COMMAND) {
         map_wr_si_to_nummi[trans_ptr] = num_mi_transaction;   //Maps number of mi_trans generated for given si_trans
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "Filled: map_wr_si_to_nummi[" << trans_ptr << "]: " << map_wr_si_to_nummi[trans_ptr] << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
         map_wr_si_to_numsi[trans_ptr] = numsi;                //Maps si_trans to corresponding SI port
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "Filled: map_wr_si_to_numsi[" << trans_ptr << "]: " << map_wr_si_to_numsi[trans_ptr] << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
      } else if (trans_ptr->get_command() == xtlm::XTLM_READ_COMMAND) {
         map_rd_si_to_nummi[trans_ptr] = num_mi_transaction;   //Maps number of mi_trans generated for given si_trans
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "Filled: map_rd_si_to_nummi[" << trans_ptr << "]: " << map_rd_si_to_nummi[trans_ptr] << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
         map_rd_si_to_numsi[trans_ptr] = numsi;                //Maps si_trans to corresponding SI port
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "Filled: map_rd_si_to_numsi[" << trans_ptr << "]: " << map_rd_si_to_numsi[trans_ptr] << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
      }
   }

   for (int num_trans = 0; num_trans < num_mi_transaction; num_trans++) {
      m_trans = mem_manager->get_payload();
      m_trans->acquire();
      m_trans->set_command(trans_ptr->get_command());
      m_trans->set_axi_id(static_cast<unsigned int>(0));
      m_trans->set_burst_type(trans_ptr->get_burst_type());
      numsi_vec.push_back(numsi);

      int burst_cnt = 1;
      int num_burst = 1;
      int fill_null_bytes = 0;

	  if (m_report_handler->get_verbosity_level()
	  		== xsc::common_cpp::VERBOSITY::DEBUG) {
	  	m_ss.str("");
	  	m_ss << this->name() << "Round: " << num_trans << "\n"
        << std::dec << "s_data_size: " << s_data_size << "\n"
        << std::dec << "m_data_size: " << m_data_size << "\n"
        << std::dec << "m_num_burst: " << m_num_burst << "\n";
	  	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	  			DEBUG);
	  }

      if (s_data_size >= m_data_size) {
         burst_cnt = m_burst_cnt;
         num_burst = m_num_burst;
      } else if (s_data_size >= m_num_burst) {
         burst_cnt = (s_data_size % m_num_burst) ? (s_data_size/m_num_burst) + 1 : (s_data_size/m_num_burst);
         num_burst = m_num_burst;
         fill_null_bytes = (m_num_burst*burst_cnt) - s_data_size;
      } else {
         burst_cnt = 1;
         num_burst = m_num_burst;
         fill_null_bytes = m_num_burst - s_data_size;
      }

	  if (m_report_handler->get_verbosity_level()
	  		== xsc::common_cpp::VERBOSITY::DEBUG) {
	  	m_ss.str("");
	  	m_ss << this->name() << std::dec << "burst_cnt: " << burst_cnt << "\n"
        << std::dec << "num_burst: " << num_burst << "\n"
        << std::dec << "fill_null_bytes: " << fill_null_bytes << "\n";
	  	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	  			DEBUG);
	  }
      
      m_trans->set_burst_size(m_num_burst);
      m_trans->set_burst_length(burst_cnt);

      unsigned int data_size = num_burst * burst_cnt; 

      m_trans->set_address(address);
      address = address + data_size;
      m_trans->create_and_get_data_ptr(data_size);
      if(trans_ptr->get_byte_enable_ptr() == nullptr){
        m_trans->set_byte_enable_ptr(nullptr, 0);
      }else{
        m_trans->create_and_get_byte_enable_ptr(data_size);
      }

      unsigned char* data_ptr = m_trans->get_data_ptr();

      //Fill in data when it is xtlm::XTLM_WRITE_COMMAND
      if (trans_ptr->get_command() == xtlm::XTLM_WRITE_COMMAND) {
         unsigned char* data_en_ptr = m_trans->get_byte_enable_ptr();

         for (int i = 0; i < burst_cnt; i++) {
            for (int j = 0; j < num_burst; j++) {
               if (s_data_size_abs > 0) {
                  data_ptr[i * num_burst + j]    = s_data_ptr[s_data_ptr_indx + (i * num_burst) + j];
                  data_en_ptr[i * num_burst + j] = s_data_en_ptr[s_data_ptr_indx + (i * num_burst) + j];
	            if (m_report_handler->get_verbosity_level()
	            		== xsc::common_cpp::VERBOSITY::DEBUG) {
	            	m_ss.str("");
	            	m_ss << this->name() << "Wrote data_ptr[" << i * num_burst + j << "] = s_data_ptr[" << s_data_ptr_indx + (i * num_burst) + j << "] : " << std::hex << static_cast<int>(s_data_ptr[s_data_ptr_indx + (i * num_burst) + j]) << std::endl;
	            	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	            			DEBUG);
	            }
               } else {
                  data_ptr[i * num_burst + j]    = 0x0;
                  data_en_ptr[i * num_burst + j] = 0x0;
	                if (m_report_handler->get_verbosity_level()
	                		== xsc::common_cpp::VERBOSITY::DEBUG) {
	                	m_ss.str("");
	                	m_ss << this->name() << "Wrote data_ptr[" << i * num_burst + j << "] = 0x0\n" << std::endl;
	                	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	                			DEBUG);
	                }
               }
               s_data_size_abs--;
               s_data_size--;
            }
         }

         if (fill_null_bytes) {
            //fill null bytes
         }

         s_data_ptr_indx += data_size;
      } else {
         s_data_size = s_data_size - (burst_cnt * num_burst);
      }

	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "BEGIN Outgoing " << num_trans << " Paylod information" << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
	  if (m_report_handler->get_verbosity_level()
	  		== xsc::common_cpp::VERBOSITY::DEBUG) {
		m_trans->get_log(payload_msg, 3);
	  	m_ss.str("");
	  	m_ss << this->name() << payload_msg  << std::endl;
         m_ss << "END Outgoing " << num_trans << " Payload information\n";
	  	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	  			DEBUG);
	  	payload_msg = "";
	  }

      if (!mi_cascaded) {
         if (trans_ptr->get_command() == xtlm::XTLM_WRITE_COMMAND) {
            map_wr_mi_to_si[m_trans] = trans_ptr;                             //Map si_trans corresponding to each mi_trans
	        if (m_report_handler->get_verbosity_level()
	        		== xsc::common_cpp::VERBOSITY::DEBUG) {
	        	m_ss.str("");
	        	m_ss << this->name() << "Filled: map_wr_mi_to_si[" << m_trans << "]: " << map_wr_mi_to_si[m_trans] << std::endl;
	        	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	        			DEBUG);
	        }
            mmap_wr_si_to_mi.insert(std::make_pair(trans_ptr, m_trans));      //Maps si_trans to each generated mi_trans 
	        if (m_report_handler->get_verbosity_level()
	        		== xsc::common_cpp::VERBOSITY::DEBUG) {
	        	m_ss.str("");
	        	m_ss << this->name() << "Filled: mmap_wr_si_to_mi[" << trans_ptr << "]: " << m_trans << std::endl;
	        	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	        			DEBUG);
	        }
         } else if (trans_ptr->get_command() == xtlm::XTLM_READ_COMMAND) {
            map_rd_mi_to_si[m_trans] = trans_ptr;                             //Map si_trans corresponding to each mi_trans
	        if (m_report_handler->get_verbosity_level()
	        		== xsc::common_cpp::VERBOSITY::DEBUG) {
	        	m_ss.str("");
	        	m_ss << this->name() << "Filled: map_rd_mi_to_si[" << m_trans << "]: " << map_rd_mi_to_si[m_trans] << std::endl;
	        	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	        			DEBUG);
	        }
            mmap_rd_si_to_mi.insert(std::make_pair(trans_ptr, m_trans));      //Maps si_trans to each generated mi_trans
	        if (m_report_handler->get_verbosity_level()
	        		== xsc::common_cpp::VERBOSITY::DEBUG) {
	        	m_ss.str("");
	        	m_ss << this->name() << "Filled: mmap_rd_si_to_mi[" << trans_ptr << "]: " << m_trans << std::endl;
	        	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	        			DEBUG);
	        }
         }
      }

      maxi_vec.push_back(m_trans);
      req_cnt++;

   }
                     
   m_trans = NULL;

   print_footer("create_burst_transaction()");

}

void smartconnect_xtlm::process_saxi_wr_req() {

   print_header("process_saxi_wr_req()");
   
   for (int num_si = 0; num_si < smc_num_si; num_si++) {
      saxi_wr_util[num_si]->enable_logs(0);
   }

   for (int num_mi = 0; num_mi < smc_num_mi; num_mi++) {
      maxi_wr_util[num_mi]->enable_logs(0);
   }

   //Check each SI for new transaction, and enqueue if:
   //1. wr req vec is empty and:
   // 1.a. Either wr resp vec is empty or wr resp vec != empty and new trans axiid == current trans axiid
   for (int num_si = 0; num_si < smc_num_si; num_si++) {

	  if (m_report_handler->get_verbosity_level()
	  		== xsc::common_cpp::VERBOSITY::DEBUG) {
	  	m_ss.str("");
	  	m_ss << this->name() << "Checking for saxi_wr_util[" << num_si << "]->is_trans_available(): " <<  saxi_wr_util[num_si]->is_trans_available()
             << " and saxi_wr_req_vec[" << num_si << "].empty(): " << saxi_wr_req_vec[num_si].empty() << "\n";
	  	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	  			DEBUG);
	  }

      if (saxi_wr_util[num_si]->is_trans_available() && saxi_wr_req_vec[num_si].empty()) {

         xtlm::aximm_payload* in_trans_ptr = saxi_wr_util[num_si]->peek_transaction();
         unsigned int in_axi_id = in_trans_ptr->get_axi_id();

	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "Checking for saxi_wr_resp_vec[" << num_si << "].empty(): " << saxi_wr_resp_vec[num_si].empty() << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }

         //if (saxi_wr_resp_vec[num_si].empty() || (in_axi_id == saxi_wr_resp_vec[num_si].front()->get_axi_id()) ) {
         if (saxi_wr_resp_vec[num_si].empty()) {
            saxi_wr_req_vec[num_si].push_back(in_trans_ptr);
         }
      }
   }

   //Check each SI transaction queue and send them to MI or generate appropriate response
   for (int num_si = 0; num_si < smc_num_si; num_si++) {
      if (!saxi_wr_req_vec[num_si].empty() && (slave_wr_req < 0) ) {

         xtlm::aximm_payload* trans_ptr = saxi_wr_util[num_si]->get_transaction();
//         trans_ptr->acquire();
         saxi_wr_resp_vec[num_si].push_back(trans_ptr);
         saxi_wr_req_vec[num_si].pop_front();

         print_log("SI", num_si, "WRITE", "Transaction received", trans_ptr);

	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "saxi_wr_resp_vec[" << num_si << "] size: " << saxi_wr_resp_vec[num_si].size() << "\n"
            << "BEGIN Incoming Write Paylod information on num_si " << num_si << "\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	    	trans_ptr->get_log(payload_msg, 3);
	     	m_ss.str("");
	     	m_ss << this->name() << payload_msg << std::endl;
            m_ss << "END Incoming Write Payload information on num_si " << num_si<< "\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     	payload_msg = "";
	     }

         unsigned long long si_sep_route;

         if (get_transaction_status(trans_ptr, num_si, si_sep_route, m_wr_burst_length, m_wr_burst_size) == smartconnect_xtlm::TRANSACTION_OK) {

            bool si_cascaded = (SI_m_properties[num_si].getInt("IS_CASCADED") == 1);
            bool mi_cascaded = (MI_m_properties[slave_wr_req].getInt("IS_CASCADED") == 1);

            if (si_cascaded) {
               if (mi_cascaded) {
                  //xtlm::aximm_payload* dummy_trans = get_dummy_transaction(trans_ptr->get_command());
                  smartconnect_extension* exten = trans_ptr->get_extension<smartconnect_extension>();
                  exten->set_sep_route(si_sep_route);
                  //dummy_trans->set_auto_extension(exten);

                  maxi_wr_req_vec[slave_wr_req].push_back(trans_ptr);

                  map_wr_si_to_nummi[trans_ptr] = 1;                                //Maps number of mi_trans generated for given si_trans
                  map_wr_si_to_numsi[trans_ptr] = num_si;                            //Maps si_trans to corresponding SI port
                  mmap_wr_si_to_mi.insert(std::make_pair(trans_ptr, trans_ptr));  //Maps si_trans to each generated mi_trans
                  map_wr_mi_to_si[trans_ptr] = trans_ptr;                         //Map si_trans corresponding to each mi_trans

               } else {
                  //Extract MI trans from extension and send to MI
                  smartconnect_extension* exten = trans_ptr->get_extension<smartconnect_extension>();
                  map_wr_si_to_nummi[trans_ptr] = 0;
                  map_wr_si_to_numsi[trans_ptr] = num_si;

                  for ( auto mi_trans_vec_itr = (exten->get_mi_trans_vec()).begin(); mi_trans_vec_itr != (exten->get_mi_trans_vec()).end(); mi_trans_vec_itr++ ) {
                     xtlm::aximm_payload* m_trans = *mi_trans_vec_itr; 
                     mmap_wr_si_to_mi.insert(std::make_pair(trans_ptr, m_trans));
                     map_wr_mi_to_si[m_trans] = trans_ptr;
                     map_wr_si_to_nummi[trans_ptr]++;
                     maxi_wr_req_vec[slave_wr_req].push_back(m_trans);
                  }

               }
            } else { //SI not cascaded
               if (mi_cascaded) {
                  
                  xtlm::aximm_payload* dummy_trans = get_dummy_transaction(trans_ptr->get_command());
                  dummy_trans->acquire();
                  smartconnect_extension* exten = new smartconnect_extension();
                  exten->set_sep_route(si_sep_route);
                  dummy_trans->set_auto_extension(exten);

                  maxi_wr_req_vec[slave_wr_req].push_back(dummy_trans);

                  map_wr_si_to_nummi[trans_ptr] = 1;                                //Maps number of mi_trans generated for given si_trans
                  map_wr_si_to_numsi[trans_ptr] = num_si;                            //Maps si_trans to corresponding SI port
                  mmap_wr_si_to_mi.insert(std::make_pair(trans_ptr, dummy_trans));  //Maps si_trans to each generated mi_trans
                  map_wr_mi_to_si[dummy_trans] = trans_ptr;                         //Map si_trans corresponding to each mi_trans

                  //Create end-point slave transactions
                  create_burst_transaction(saxi_wr_resp_vec[num_si], (exten->get_mi_trans_vec()), maxi_wr_req_numsi_vec[slave_wr_req], m_wr_burst_length, 
                                    m_wr_burst_size, maxi_wr_req_cnt[slave_wr_req], num_si, slave_wr_req, si_sep_route );

               } else {
                  create_burst_transaction(saxi_wr_resp_vec[num_si], maxi_wr_req_vec[slave_wr_req], maxi_wr_req_numsi_vec[slave_wr_req], m_wr_burst_length, 
                                    m_wr_burst_size, maxi_wr_req_cnt[slave_wr_req], num_si, slave_wr_req, si_sep_route );

               }
            }

            initiate_maxi_wr_req.notify(sc_core::SC_ZERO_TIME);

         } else {
            sc_time delay = SC_ZERO_TIME;
            print_log("SI", num_si, "WRITE", "Err Response sent", trans_ptr);
            saxi_wr_util[num_si]->send_resp(*trans_ptr, delay);
            saxi_wr_resp_vec[num_si].pop_back();
         }

      } else if (slave_wr_req >= 0) {
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "\nNUM SI: " << num_si << " on hold because NUM MI: " << slave_wr_req << " is busy \n\n" << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
         //next_trigger(maxi_wr_util[slave_wr_req]->transaction_sampled);
      }
   }

   print_footer("process_saxi_wr_req()");

}

void smartconnect_xtlm::process_maxi_wr_req() {

   print_header("process_maxi_wr_req()");

   if (slave_wr_req >= 0) {
      if (maxi_wr_util[slave_wr_req]->is_slave_ready() && !maxi_wr_req_vec[slave_wr_req].empty()) {
         xtlm::aximm_payload* trans_ptr = maxi_wr_req_vec[slave_wr_req].front();
         sc_time delay = SC_ZERO_TIME;
         maxi_wr_util[slave_wr_req]->send_transaction(*trans_ptr, delay);

         print_log("MI", slave_wr_req, "WRITE", "Transaction sent", trans_ptr);

	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "BEGIN Sent out Write Paylod information from num_mi " << slave_wr_req << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	    	 trans_ptr->get_log(payload_msg, 3);
	     	m_ss.str("");
	     	m_ss << this->name() << payload_msg << std::endl;
            m_ss << "END Sent out Write Payload information from num_mi " << slave_wr_req << "\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     	payload_msg = "";
	     }

         maxi_wr_req_vec[slave_wr_req].pop_front();
         if (maxi_wr_req_vec[slave_wr_req].empty()) {
            slave_wr_req = -1;
         }
      } else {
         if (maxi_wr_req_vec[slave_wr_req].empty()) {
	        if (m_report_handler->get_verbosity_level()
	        		== xsc::common_cpp::VERBOSITY::DEBUG) {
	        	m_ss.str("");
	        	m_ss << this->name() << "process_maxi_wr_req: maxi_wr_req_vec[" << slave_wr_req << "].empty()-> empty!!!\n" << std::endl;
	        	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	        			DEBUG);
	        }
         } else {
	        if (m_report_handler->get_verbosity_level()
	        		== xsc::common_cpp::VERBOSITY::DEBUG) {
	        	m_ss.str("");
	        	m_ss << this->name() << "process_maxi_wr_req: maxi_wr_util[" << slave_wr_req << "]->is_slave_ready()-> not ready!!!\n" << std::endl;
	        	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	        			DEBUG);
	        }
         }
      }
   } else {
	  if (m_report_handler->get_verbosity_level()
	  		== xsc::common_cpp::VERBOSITY::DEBUG) {
	  	m_ss.str("");
	  	m_ss << this->name() << "slave_wr_req is: " << slave_wr_req << std::endl;
	  	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	  			DEBUG);
	  }
      //Always check for any pending saxi wr request after processing all maxi transactions
      check_saxi_wr_req.notify(sc_core::SC_ZERO_TIME);
   }

   print_footer("process_maxi_wr_req()");

}

void smartconnect_xtlm::process_maxi_wr_resp() {

   print_header("process_maxi_wr_resp()");

   for (int num_mi = 0; num_mi < smc_num_mi; num_mi++) {
      if (maxi_wr_util[num_mi]->is_resp_available()) {
         xtlm::aximm_payload* mi_trans = maxi_wr_util[num_mi]->get_resp();
         xtlm::aximm_payload* si_trans = map_wr_mi_to_si[mi_trans];

	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "Accessed: in process_maxi_wr_resp() si_trans: " << si_trans << "for mi_trans: " << mi_trans <<std::endl;
            m_ss << "Accessed: in process_maxi_wr_resp() map_wr_si_to_nummi[" << si_trans << "] before: " << map_wr_si_to_nummi[si_trans] << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }

//         maxi_wr_resp_vec[num_mi].push_back(mi_trans);

         print_log("MI", num_mi, "WRITE", "Response received", mi_trans);

         //New code to notify based on map
         map_wr_si_to_nummi[si_trans]--;
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "Accessed: in process_maxi_wr_resp() map_wr_si_to_nummi[" << si_trans << "] after: " << map_wr_si_to_nummi[si_trans] << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
         if (map_wr_si_to_nummi[si_trans] == 0) {
            slave_wr_resp.push_back(si_trans);
            slave_wr_resp_nummi.push_back(num_mi);
	        if (m_report_handler->get_verbosity_level()
	        		== xsc::common_cpp::VERBOSITY::DEBUG) {
	        	m_ss.str("");
	        	m_ss << this->name() << "Accessed: in process_maxi_wr_resp() notifying send_wr_resp with si_trans: " << slave_wr_resp.back() << std::endl;
	        	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	        			DEBUG);
	        }
            send_wr_resp.notify(sc_core::SC_ZERO_TIME);
         }
      }
   }

   print_footer("process_maxi_wr_resp()");

}

void smartconnect_xtlm::process_saxi_wr_resp() {

   print_header("process_saxi_wr_resp()");

//   unsigned int num_si = maxi_wr_req_numsi_vec[slave_wr_resp].front();
//   xtlm::aximm_payload* trans_ptr = saxi_wr_resp_vec[num_si].front();

   while(!slave_wr_resp.empty()) {
   
      xtlm::aximm_payload* trans_ptr = slave_wr_resp.front();
      unsigned int num_si = map_wr_si_to_numsi[trans_ptr];
   
      unsigned int num_mi = slave_wr_resp_nummi.front();
   
      bool si_cascaded = (SI_m_properties[num_si].getInt("IS_CASCADED") == 1);
      bool mi_cascaded = (MI_m_properties[num_mi].getInt("IS_CASCADED") == 1);
      
	  if (m_report_handler->get_verbosity_level()
	  		== xsc::common_cpp::VERBOSITY::DEBUG) {
	  	m_ss.str("");
	  	m_ss << this->name() << "saxi_wr_resp_vec[" << num_si << "] size: " << saxi_wr_resp_vec[num_si].size() << "\n"
         << "Processing process_saxi_wr_resp on num_si: " << num_si << "\n"
         << "BEGIN Response information\n";
	  	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	  			DEBUG);
	  }
	  if (m_report_handler->get_verbosity_level()
	  		== xsc::common_cpp::VERBOSITY::DEBUG) {
		trans_ptr->get_log(payload_msg, 3);
	  	m_ss.str("");
	  	m_ss << this->name() << payload_msg << std::endl;
         m_ss << "RESPONSE: " << trans_ptr->get_response_string() << "\n"
          << "END Response information\n\n";
	  	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	  			DEBUG);
	  	payload_msg = "";
	  }
   
      if (saxi_wr_util[num_si]->is_master_ready() == false) {
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "Processing process_saxi_wr_resp on num_si: " << num_si << " master not ready\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
         next_trigger(saxi_wr_util[num_si]->resp_sampled);
         return;
      }

      slave_wr_resp.pop_front();
      slave_wr_resp_nummi.pop_front();
   
      saxi_wr_resp_vec[num_si].pop_front();
      
      trans_ptr->set_response_status(xtlm::XTLM_OK_RESPONSE);
      mmap_wr_si_to_mi_itr = mmap_wr_si_to_mi.find(trans_ptr);
   
      xtlm::aximm_payload* m_trans_ptr = NULL;
   
      while (mmap_wr_si_to_mi_itr != mmap_wr_si_to_mi.end() ) {
         m_trans_ptr = mmap_wr_si_to_mi_itr->second;
   
         if (!si_cascaded && m_trans_ptr->is_response_error()) {
            trans_ptr->set_response_status(m_trans_ptr->get_response_status());
         }
   
         if (mi_cascaded && !si_cascaded) {
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "Accessing extension of " << m_trans_ptr << " \n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
            smartconnect_extension* exten = m_trans_ptr->get_extension<smartconnect_extension>();
            xtlm::aximm_payload* mi_trans_ptr = NULL;
            if (exten != 0) {
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "Extension exists!!\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
            } else {
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() <<"Extension does not exists!!\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
            }
            while ( !((exten->get_mi_trans_vec()).empty()) ) {
               mi_trans_ptr = (exten->get_mi_trans_vec()).front();
	            if (m_report_handler->get_verbosity_level()
	            		== xsc::common_cpp::VERBOSITY::DEBUG) {
	            	m_ss.str("");
	            	m_ss << this->name() << "Accessed:" << mi_trans_ptr << "\n";
	            	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	            			DEBUG);
	            }
               (exten->get_mi_trans_vec()).pop_front();
               if (mi_trans_ptr->is_response_error()) {
                  trans_ptr->set_response_status(mi_trans_ptr->get_response_status());
               }
               mi_trans_ptr->release();
            }
   
         }
   
         if (!si_cascaded) {
            m_trans_ptr->release();
         }
   
         mmap_wr_si_to_mi.erase(mmap_wr_si_to_mi_itr);
         map_wr_mi_to_si.erase(m_trans_ptr);
         mmap_wr_si_to_mi_itr = mmap_wr_si_to_mi.find(trans_ptr);
      }
   
      if (trans_ptr->get_response_status() == NULL) {
         trans_ptr->set_response_status(xtlm::XTLM_GENERIC_ERROR_RESPONSE);
      }
   
      sc_time delay = SC_ZERO_TIME;
   
      if (trans_ptr != NULL) {
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "BEGIN sending Write Response information on num_si " << num_si << "\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	    	trans_ptr->get_log(payload_msg, 3);
	     	m_ss.str("");
	     	m_ss << this->name() << payload_msg << std::endl;
            m_ss << "RESPONSE: " << trans_ptr->get_response_string() << "\n"
            << "END sending Write Response information on num_si " << num_si << "\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     	payload_msg = "";
	     }
   
         print_log("SI", num_si, "WRITE", "Response sent", trans_ptr);
   
         saxi_wr_util[num_si]->send_resp(*trans_ptr, delay);
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "INFO: " << std::string(this->name()) << ": process_saxi_wr_resp(): SAXI WR RESP sent \n\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
         map_wr_si_to_nummi.erase(trans_ptr);
         map_wr_si_to_numsi.erase(trans_ptr);
   //      trans_ptr->release();
         create_wr_resp = false;
         bad_saxi_wr_trans = -1;
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "INFO: " << std::string(this->name()) << ": process_saxi_wr_resp(): SAXI WR RESP released and sent \n\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
      }

   } //end of while loop

   //Check for pending incoming wr transaction
   check_saxi_wr_req.notify(sc_core::SC_ZERO_TIME);

   print_footer("process_saxi_wr_resp()");

}

void smartconnect_xtlm::process_saxi_rd_req() {

   print_header("process_saxi_rd_req()");

   for (int num_si = 0; num_si < smc_num_si; num_si++) {
      saxi_rd_util[num_si]->enable_logs(0);
   }

   for (int num_mi = 0; num_mi < smc_num_mi; num_mi++) {
      maxi_rd_util[num_mi]->enable_logs(0);
   }

   //Check each SI for new transaction, and enqueue if:
   //1. rd req vec is empty and:
   // 1.a. Either rd resp vec is empty or if rd resp vec != empty and new trans axiid == current trans axiid
   for (int num_si = 0; num_si < smc_num_si; num_si++) {

	  if (m_report_handler->get_verbosity_level()
	  		== xsc::common_cpp::VERBOSITY::DEBUG) {
	  	m_ss.str("");
	  	m_ss << this->name() << "Checking for saxi_rd_util[" << num_si << "]->is_trans_available(): " <<  saxi_rd_util[num_si]->is_trans_available()
             << " and saxi_rd_req_vec[" << num_si << "].empty(): " << saxi_rd_req_vec[num_si].empty() << "\n";
	  	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	  			DEBUG);
	  }

      if (saxi_rd_util[num_si]->is_trans_available() && saxi_rd_req_vec[num_si].empty()) {

         xtlm::aximm_payload* in_trans_ptr = saxi_rd_util[num_si]->peek_transaction();
         unsigned int in_axi_id = in_trans_ptr->get_axi_id();

	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "Checking for saxi_rd_resp_vec[" << num_si << "].empty(): " << saxi_rd_resp_vec[num_si].empty() << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }

         //if (saxi_rd_resp_vec[num_si].empty() || (in_axi_id == saxi_rd_resp_vec[num_si].front()->get_axi_id()) ) {
         if (saxi_rd_resp_vec[num_si].empty()) {
            saxi_rd_req_vec[num_si].push_back(in_trans_ptr);
         }
      }
   }

   //Check each SI transaction queue and send them to MI or generate appropriate response
   for (int num_si = 0; num_si < smc_num_si; num_si++) {
      if (!saxi_rd_req_vec[num_si].empty() && (slave_rd_req < 0) ) {         

         xtlm::aximm_payload* trans_ptr = saxi_rd_util[num_si]->get_transaction();
//         trans_ptr->acquire();
         saxi_rd_resp_vec[num_si].push_back(trans_ptr);
         saxi_rd_req_vec[num_si].pop_front();

	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "saxi_rd_resp_vec[" << num_si << "] size: " << saxi_rd_resp_vec[num_si].size() << "\n"
            << "BEGIN Incoming Read Paylod information on num_si " << num_si << "\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }

         print_log("SI", num_si, "READ", "Transaction received", trans_ptr);

	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	    	trans_ptr->get_log(payload_msg, 3);
	     	m_ss.str("");
	     	m_ss << this->name() << payload_msg  << std::endl;
            m_ss << "END Incoming Read Payload information on num_si " << num_si << "\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     	payload_msg = "";
	     }

         unsigned long long si_sep_route;

         if (get_transaction_status(trans_ptr, num_si, si_sep_route, m_rd_burst_length, m_rd_burst_size) == smartconnect_xtlm::TRANSACTION_OK) {

            bool si_cascaded = (SI_m_properties[num_si].getInt("IS_CASCADED") == 1);
            bool mi_cascaded = (MI_m_properties[slave_rd_req].getInt("IS_CASCADED") == 1);

            if (si_cascaded) {
               if (mi_cascaded) {
                  //xtlm::aximm_payload* dummy_trans = get_dummy_transaction(trans_ptr->get_command());
                  smartconnect_extension* exten = trans_ptr->get_extension<smartconnect_extension>();
                  exten->set_sep_route(si_sep_route);
                  //dummy_trans->set_auto_extension(exten);

                  maxi_rd_req_vec[slave_rd_req].push_back(trans_ptr);

                  map_rd_si_to_nummi[trans_ptr] = 1;                                //Maps number of mi_trans generated for given si_trans
                  map_rd_si_to_numsi[trans_ptr] = num_si;                            //Maps si_trans to corresponding SI port
                  mmap_rd_si_to_mi.insert(std::make_pair(trans_ptr, trans_ptr));  //Maps si_trans to each generated mi_trans
                  map_rd_mi_to_si[trans_ptr] = trans_ptr;                         //Map si_trans corresponding to each mi_trans

               } else {
                  //Extract MI trans from extension and send to MI
                  smartconnect_extension* exten = trans_ptr->get_extension<smartconnect_extension>();
                  map_rd_si_to_nummi[trans_ptr] = 0;
                  map_rd_si_to_numsi[trans_ptr] = num_si;

                  for ( auto mi_trans_vec_itr = (exten->get_mi_trans_vec()).begin(); mi_trans_vec_itr != (exten->get_mi_trans_vec()).end(); mi_trans_vec_itr++ ) {
                     xtlm::aximm_payload* m_trans = *mi_trans_vec_itr; 
                     mmap_rd_si_to_mi.insert(std::make_pair(trans_ptr, m_trans));
                     map_rd_mi_to_si[m_trans] = trans_ptr;
                     map_rd_si_to_nummi[trans_ptr]++;
                     maxi_rd_req_vec[slave_rd_req].push_back(m_trans);
                  }

               }
            } else { //SI not cascaded
               if (mi_cascaded) {
                  
                  xtlm::aximm_payload* dummy_trans = get_dummy_transaction(trans_ptr->get_command());
                  dummy_trans->acquire();
                  smartconnect_extension* exten = new smartconnect_extension();
                  exten->set_sep_route(si_sep_route);
                  dummy_trans->set_auto_extension(exten);

                  maxi_rd_req_vec[slave_rd_req].push_back(dummy_trans);

                  map_rd_si_to_nummi[trans_ptr] = 1;                                //Maps number of mi_trans generated for given si_trans
                  map_rd_si_to_numsi[trans_ptr] = num_si;                            //Maps si_trans to corresponding SI port
                  mmap_rd_si_to_mi.insert(std::make_pair(trans_ptr, dummy_trans));  //Maps si_trans to each generated mi_trans
                  map_rd_mi_to_si[dummy_trans] = trans_ptr;                         //Map si_trans corresponding to each mi_trans

                  //Create end-point slave transactions
                  create_burst_transaction(saxi_rd_resp_vec[num_si], (exten->get_mi_trans_vec()), maxi_rd_req_numsi_vec[slave_rd_req], m_rd_burst_length, 
                                    m_rd_burst_size, maxi_rd_req_cnt[slave_rd_req], num_si, slave_rd_req, si_sep_route );

               } else {
                  create_burst_transaction(saxi_rd_resp_vec[num_si], maxi_rd_req_vec[slave_rd_req], maxi_rd_req_numsi_vec[slave_rd_req], m_rd_burst_length, 
                                    m_rd_burst_size, maxi_rd_req_cnt[slave_rd_req], num_si, slave_rd_req, si_sep_route );

               }
            }

            initiate_maxi_rd_req.notify(sc_core::SC_ZERO_TIME);

         } else {
            sc_time delay = SC_ZERO_TIME;
            print_log("SI", num_si, "READ", "Err Response sent", trans_ptr);
            saxi_rd_util[num_si]->send_data(*trans_ptr, delay);
            saxi_rd_resp_vec[num_si].pop_back();
         }
      } else if (slave_rd_req >= 0) {
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "\nNUM SI: " << num_si << " on hold because NUM MI: " << slave_rd_req << " is busy \n" << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
         //next_trigger(maxi_rd_util[slave_rd_req]->transaction_sampled);
      }
   }

  print_footer("process_saxi_rd_req()");

}

void smartconnect_xtlm::process_maxi_rd_req() {

   print_header("process_maxi_rd_req()");

   if (slave_rd_req >= 0) {
      if (maxi_rd_util[slave_rd_req]->is_slave_ready() && !maxi_rd_req_vec[slave_rd_req].empty() ) {
         xtlm::aximm_payload* trans_ptr = maxi_rd_req_vec[slave_rd_req].front();

	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "BEGIN process_maxi_rd_req() sending READ payload\n" << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	    	trans_ptr->get_log(payload_msg, 3);
	     	m_ss.str("");
	     	m_ss << this->name() << payload_msg << std::endl;
            m_ss << "END process_maxi_rd_req() sending READ payload\n\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     	payload_msg = "";
	     }

         print_log("MI", slave_rd_req, "READ", "Transaction sent", trans_ptr);

         sc_time delay = SC_ZERO_TIME;
         maxi_rd_util[slave_rd_req]->send_transaction(*trans_ptr, delay);
         maxi_rd_req_vec[slave_rd_req].pop_front();
         if (maxi_rd_req_vec[slave_rd_req].empty()) {
            slave_rd_req = -1;
         }
      } else {
         if (!maxi_rd_util[slave_rd_req]->is_slave_ready()) {
	        if (m_report_handler->get_verbosity_level()
	        		== xsc::common_cpp::VERBOSITY::DEBUG) {
	        	m_ss.str("");
	        	m_ss << this->name() << "process_maxi_rd_req: maxi_rd_util[" << slave_rd_req 
                << "]->is_slave_ready()-> not ready!!!\n" << std::endl;
	        	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	        			DEBUG);
	        }
         } else {
	        if (m_report_handler->get_verbosity_level()
	        		== xsc::common_cpp::VERBOSITY::DEBUG) {
	        	m_ss.str("");
	        	m_ss << this->name() << "process_maxi_rd_req: maxi_rd_req_vec[" << slave_rd_req 
                << "] reached maxi_rd_req_vec[" << slave_rd_req << "].end()\n" << std::endl;
	        	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	        			DEBUG);
	        }
         }
      }
   } else {
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "slave_rd_req is: " << slave_rd_req << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
      check_saxi_rd_req.notify(sc_core::SC_ZERO_TIME);
   }

   print_footer("process_maxi_rd_req()");

}

void smartconnect_xtlm::process_maxi_rd_resp() {

   print_header("process_maxi_rd_resp()");

   for (int num_mi = 0; num_mi < smc_num_mi; num_mi++) {
      if (maxi_rd_util[num_mi]->is_data_available()) {
         xtlm::aximm_payload* mi_trans = maxi_rd_util[num_mi]->get_data();
         xtlm::aximm_payload* si_trans = map_rd_mi_to_si[mi_trans];

         print_log("MI", num_mi, "READ", "Response received", mi_trans);

	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "BEGIN Regslice receiving READ information\n" << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	    	mi_trans->get_log(payload_msg, 3);
	     	m_ss.str("");
	     	m_ss << this->name() << payload_msg << std::endl;
            m_ss << "END Regslice receiving READ information\n\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     	payload_msg = "";
	     }

         //New code to notify based on map
         map_rd_si_to_nummi[si_trans]--;
         if (map_rd_si_to_nummi[si_trans] == 0) {
            slave_rd_resp.push_back(si_trans);
            slave_rd_resp_nummi.push_back(num_mi);
            send_saxi_rd_resp.notify(sc_core::SC_ZERO_TIME);
         }
      }
   }
   
   print_footer("process_maxi_rd_resp()");
}

void smartconnect_xtlm::process_saxi_rd_resp() {

   print_header("process_saxi_rd_resp()");

   while (!slave_rd_resp.empty()) {

      xtlm::aximm_payload* m_req_trans_ptr = NULL;
      xtlm::aximm_payload* m_resp_trans_ptr = NULL;
   
      xtlm::aximm_payload* trans_ptr = slave_rd_resp.front();
      unsigned int num_si = map_rd_si_to_numsi[trans_ptr];
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "num_si is: " << num_si << std::endl;
            m_ss << "SI trans is is: " << trans_ptr<< "\n\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
   
      unsigned int num_mi = slave_rd_resp_nummi.front();
   
      bool si_cascaded = (SI_m_properties[num_si].getInt("IS_CASCADED") == 1);
      bool mi_cascaded = (MI_m_properties[num_mi].getInt("IS_CASCADED") == 1);
   
      trans_ptr->set_response_status(xtlm::XTLM_OK_RESPONSE);
   
	  if (m_report_handler->get_verbosity_level()
	  		== xsc::common_cpp::VERBOSITY::DEBUG) {
	  	m_ss.str("");
	  	m_ss << this->name() << "saxi_rd_resp_vec[" << num_si << "] size: " << saxi_rd_resp_vec[num_si].size() << "\n"
        << "Processing process_saxi_rd_resp on num_si: " << num_si << "\n"
        << "BEGIN Response information\n";
	  	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	  			DEBUG);
	  }
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	    	trans_ptr->get_log(payload_msg, 3);
	     	m_ss.str("");
	     	m_ss << this->name() << payload_msg << std::endl;
            m_ss << "RESPONSE: " << trans_ptr->get_response_string()
            << "END Response information\n\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     	payload_msg = "";
	     }
      
      if (saxi_rd_util[num_si]->is_master_ready() == false) {
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "Processing process_saxi_rd_resp on num_si: " << num_si << " master not ready\n" << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
         next_trigger(saxi_rd_util[num_si]->data_sampled);
         return;
      }

      slave_rd_resp.pop_front();
      slave_rd_resp_nummi.pop_front();
   
      saxi_rd_resp_vec[num_si].pop_front();
   
      if (si_cascaded) { //If SI is cascaded, clear the pointers and send response to upstream
         mmap_rd_si_to_mi_itr = mmap_rd_si_to_mi.find(trans_ptr);
   
         while (mmap_rd_si_to_mi_itr != mmap_rd_si_to_mi.end()) {
            m_req_trans_ptr = mmap_rd_si_to_mi_itr->second;
            mmap_rd_si_to_mi.erase(mmap_rd_si_to_mi_itr);
            map_rd_mi_to_si.erase(m_req_trans_ptr);
            mmap_rd_si_to_mi_itr = mmap_rd_si_to_mi.find(trans_ptr);
            m_req_trans_ptr = NULL;
         }
      } else { //Else, extract read data from response
   
         int s_burst_length = trans_ptr->get_burst_length();
         int s_burst_size = trans_ptr->get_burst_size();
      
         int s_burst_cnt = trans_ptr->get_burst_length();
         int s_num_burst = s_burst_size;
      //   int s_data_size = s_burst_cnt * s_num_burst;
         int s_data_size = trans_ptr->get_data_length();
         uint64_t s_addr = trans_ptr->get_address();
         unsigned char* s_data_ptr = trans_ptr->get_data_ptr();
         int s_data_ptr_indx = 0;
         int s_data_ptr_indx_high = s_data_size - 1;
      
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "saxi burst_length is: " << s_burst_length << "\n"
            << "saxi burst_size is: " << s_burst_size << "\n"
            << "saxi start addr is: " << std::hex << s_addr << "\n"
            << "saxi end addr is: " << std::hex << s_data_ptr_indx_high << "\n"
            << "saxi data_ptr is: " << std::hex << s_data_ptr << "\n\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
      
         mmap_rd_si_to_mi_itr = mmap_rd_si_to_mi.find(trans_ptr);
   
         //Loop through all MI trans mapped to this SI trans
         while (mmap_rd_si_to_mi_itr != mmap_rd_si_to_mi.end()) {
      
            m_req_trans_ptr = mmap_rd_si_to_mi_itr->second;
            m_resp_trans_ptr = mmap_rd_si_to_mi_itr->second;
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "maxi transaction is: " << m_req_trans_ptr << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
      
            if (!mi_cascaded) { //MI not cascaded so these are orinigal trans responses  so extract read data here
               int m_burst_length = m_req_trans_ptr->get_burst_length();
               int m_burst_size = m_req_trans_ptr->get_burst_size();
               unsigned char* m_data_ptr = m_resp_trans_ptr->get_data_ptr();
         
               int m_burst_cnt = m_burst_length;
               int m_num_burst = m_burst_size;
               int m_data_size = m_req_trans_ptr->get_data_length();
         
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "BEGIN Regslice vector pop out READ information\n" << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
            m_resp_trans_ptr->get_log(payload_msg, 3);
	     	m_ss.str("");
	     	m_ss << this->name() << payload_msg << std::endl;
            m_ss << "END Regslice vector pop out READ information\n\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
            payload_msg = "";
	     }
         
               if (m_resp_trans_ptr->is_response_error()) {
                  trans_ptr->set_response_status(m_resp_trans_ptr->get_response_status());
         //         maxi_rd_resp_vec[slave_rd_resp].clear();
         //         break;
               } else {
                  for (int i = 0; i < m_burst_cnt; i++) {
                     for (int j = 0; j < m_num_burst; j++) {
                        s_data_ptr[s_data_ptr_indx] = (unsigned int) m_data_ptr[(i*m_num_burst) + j];
	                    if (m_report_handler->get_verbosity_level()
	                    		== xsc::common_cpp::VERBOSITY::DEBUG) {
	                    	m_ss.str("");
	                    	m_ss << this->name() << "Read s_data_ptr[" << s_data_ptr_indx << "] = m_data_ptr[" 
                            << (i*m_num_burst) + j << "]: "<< std::hex 
                            << static_cast<int>(m_data_ptr[(i*m_num_burst) + j]) << "\n" << std::endl;
	                    	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	                    			DEBUG);
	                    }
                        s_data_ptr_indx++;
                        if (s_data_ptr_indx > s_data_ptr_indx_high) {
	                        if (m_report_handler->get_verbosity_level()
	                        		== xsc::common_cpp::VERBOSITY::DEBUG) {
	                        	m_ss.str("");
	                        	m_ss << this->name() << "breaking loop \n" << std::endl;
	                        	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	                        			DEBUG);
	                        }
                           break;
                        }
                     } //for int j
                     if (s_data_ptr_indx > s_data_ptr_indx_high) {
	                    if (m_report_handler->get_verbosity_level()
	                    		== xsc::common_cpp::VERBOSITY::DEBUG) {
	                    	m_ss.str("");
	                    	m_ss << this->name() << "breaking loop \n" << std::endl;
	                    	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	                    			DEBUG);
	                    }
                        break;
                     }
                  } //for i
               } //else
            } else { //MI is cascaded so extract original MI trans from extension object 
               smartconnect_extension* exten = m_req_trans_ptr->get_extension<smartconnect_extension>();
               xtlm::aximm_payload* mi_trans_ptr = NULL;
   
               while ( !((exten->get_mi_trans_vec()).empty()) ) {
                  mi_trans_ptr = (exten->get_mi_trans_vec()).front();
                  (exten->get_mi_trans_vec()).pop_front();
   
                  if (mi_trans_ptr->is_response_error()) {
                     trans_ptr->set_response_status(mi_trans_ptr->get_response_status());
                  } else {
   
                     int m_burst_length = mi_trans_ptr->get_burst_length();
                     int m_burst_size = mi_trans_ptr->get_burst_size();
                     unsigned char* m_data_ptr = mi_trans_ptr->get_data_ptr();
               
                     int m_burst_cnt = m_burst_length;
                     int m_num_burst = m_burst_size;
                     int m_data_size = mi_trans_ptr->get_data_length();
         
	                 if (m_report_handler->get_verbosity_level()
	                 		== xsc::common_cpp::VERBOSITY::DEBUG) {
	                 	m_ss.str("");
	                 	m_ss << this->name() << "BEGIN Regslice vector pop out READ information\n" << std::endl;
	                 	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	                 			DEBUG);
	                 }
	                if (m_report_handler->get_verbosity_level()
	                		== xsc::common_cpp::VERBOSITY::DEBUG) {
	                	mi_trans_ptr->get_log(payload_msg, 3);
	                	m_ss.str("");
	                	m_ss << this->name() << payload_msg << std::endl;
                        m_ss << "END Regslice vector pop out READ information\n\n";
	                	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	                			DEBUG);
	                	payload_msg = "";
	                }
   
                     for (int i = 0; i < m_burst_cnt; i++) {
                        for (int j = 0; j < m_num_burst; j++) {
                           s_data_ptr[s_data_ptr_indx] = (unsigned int) m_data_ptr[(i*m_num_burst) + j];
	                        if (m_report_handler->get_verbosity_level()
	                        		== xsc::common_cpp::VERBOSITY::DEBUG) {
	                        	m_ss.str("");
	                        	m_ss << this->name() << "Read s_data_ptr[" << s_data_ptr_indx << "] = m_data_ptr[" 
                               << (i*m_num_burst) + j << "]: "<< std::hex 
                               << static_cast<int>(m_data_ptr[(i*m_num_burst) + j]) << "\n" << std::endl;
	                        	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	                        			DEBUG);
	                        }
                           s_data_ptr_indx++;
                           if (s_data_ptr_indx > s_data_ptr_indx_high) {
	                          if (m_report_handler->get_verbosity_level()
	                          		== xsc::common_cpp::VERBOSITY::DEBUG) {
	                          	m_ss.str("");
	                          	m_ss << this->name() << "breaking loop \n" << std::endl;
	                          	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	                          			DEBUG);
	                          }
                              break;
                           }
                        } //for int j
                        if (s_data_ptr_indx > s_data_ptr_indx_high) {
	                        if (m_report_handler->get_verbosity_level()
	                        		== xsc::common_cpp::VERBOSITY::DEBUG) {
	                        	m_ss.str("");
	                        	m_ss << this->name() << "breaking loop \n" << std::endl;
	                        	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	                        			DEBUG);
	                        }
                           break;
                        }
                     } //for i
   
                  }
                  mi_trans_ptr->release();
               }
   
            }
            
            mmap_rd_si_to_mi.erase(mmap_rd_si_to_mi_itr);
            map_rd_mi_to_si.erase(m_req_trans_ptr);
            mmap_rd_si_to_mi_itr = mmap_rd_si_to_mi.find(trans_ptr);
            m_req_trans_ptr->release();
            m_req_trans_ptr = NULL;
            m_resp_trans_ptr = NULL;
         } //while
      
      }
           
      if (trans_ptr->get_response_status() == NULL) {
         trans_ptr->set_response_status(xtlm::XTLM_GENERIC_ERROR_RESPONSE);
      }
   
      sc_time delay = SC_ZERO_TIME;
   
      if (trans_ptr != NULL) {
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	     	m_ss.str("");
	     	m_ss << this->name() << "BEGIN sending Read Response information on num_si " << num_si << "\n" << std::endl;
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     }
	     if (m_report_handler->get_verbosity_level()
	     		== xsc::common_cpp::VERBOSITY::DEBUG) {
	    	trans_ptr->get_log(payload_msg, 3);
	     	m_ss.str("");
	     	m_ss << this->name() << payload_msg << std::endl;
            m_ss << "RESPONSE: " << trans_ptr->get_response_string() << "\n"
            << "END sending Read Response information on num_si " << num_si << "\n\n";
	     	XSC_REPORT_INFO_VERB((*m_report_handler), "1", m_ss.str().c_str(),
	     			DEBUG);
	     	payload_msg = "";
	     }
   
         print_log("SI", num_si, "READ", "Response sent", trans_ptr);
   
         saxi_rd_util[num_si]->send_data(*trans_ptr, delay);
         map_rd_si_to_nummi.erase(trans_ptr);
         map_rd_si_to_numsi.erase(trans_ptr);
   //      trans_ptr->release();
      }

   } //end of while loop

   //Check for pending incoming rd trans
   check_saxi_rd_req.notify(sc_core::SC_ZERO_TIME);

   print_footer("process_saxi_rd_resp()");

}
unsigned int smartconnect_xtlm::transport_dbg_cb(xtlm::aximm_payload& trans,int si_num) {
    bool si_cascaded = (SI_m_properties[si_num].getInt("IS_CASCADED") == 1);
    int master_id = is_address_hit_lite(&trans, si_num);
    if(master_id==-1) {
      trans.get_log(payload_msg, 3);
	    m_ss.str("");
	    m_ss << this->name()<<" Transaction cannot be routed "<<std::endl;
      m_ss<<payload_msg << std::endl;
	    XSC_REPORT_ERROR((*m_report_handler), "1", m_ss.str().c_str());
        trans.set_response_status(xtlm::XTLM_ADDRESS_ERROR_RESPONSE);
        return 0;
    }
    /*
    bool mi_cascaded = (MI_m_properties[master_id].getInt("IS_CASCADED") == 1);

    if (!si_cascaded && mi_cascaded) {
        //Clear existing extension
        smartconnect_extension* exten =nullptr;
        trans.get_extension(exten);
        if (exten!=nullptr) {
          exten->set_sep_route(si_sep_route);
        } else {
          exten = new smartconnect_extension();
          exten->set_sep_route(si_sep_route);
          trans.set_auto_extension(exten);
        }
    }*/

    return maxi_rd_util[master_id]->transport_dbg(trans);
}
void smartconnect_xtlm::b_transport_cb(xtlm::aximm_payload & trans, sc_core::sc_time & t,int si_num){
}
