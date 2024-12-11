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

#ifndef _SMARTCONNECT_XTLM_IMPL_
#define _SMARTCONNECT_XTLM_IMPL_
#include "xtlm.h"

class smartconnect_xtlm;

namespace smartconnect_xtlm_impl {
class target_rd_util: public xtlm::xtlm_aximm_target_rd_socket_util {
public:
    int si_number;
	target_rd_util(sc_core::sc_module_name p_name,
			xtlm::aximm::granularity g_hint, int width_p,int si_number_,smartconnect_xtlm *_sxtlm_ptr); 
    //void register_b_transport(void (smartconnect_xtlm::*b_transport_handler)(xtlm::aximm_payload&, sc_core::sc_time& ,int si_num));
    //void register_transport_dbg(unsigned int (smartconnect_xtlm::*transport_dbg_handler)(xtlm::aximm_payload&,int si_num));
    private:
	unsigned int transport_dbg_cb(xtlm::aximm_payload& trans); 
	void b_transport(xtlm::aximm_payload & trans, sc_core::sc_time & t); 
    //void (*b_transport_handler)(xtlm::aximm_payload& trans, sc_core::sc_time& t,int si_num);
    //unsigned int (*transport_dbg_handler)(xtlm::aximm_payload& trans,int si_num);
    smartconnect_xtlm* sxtlm_ptr;
    
};

class target_wr_util: public xtlm::xtlm_aximm_target_wr_socket_util {
public:
    int si_number;
	target_wr_util(sc_core::sc_module_name p_name,
			xtlm::aximm::granularity g_hint, int width_p,int si_number_,smartconnect_xtlm *_sxtlm_ptr); 
    //void register_b_transport(void (*b_transport_handler)(xtlm::aximm_payload&, sc_core::sc_time& ,int si_num));
    //void register_transport_dbg(unsigned int (*transport_dbg_handler)(xtlm::aximm_payload&, int si_num));
    private:
	unsigned int transport_dbg_cb(xtlm::aximm_payload& trans); 
	void b_transport(xtlm::aximm_payload & trans, sc_core::sc_time & t); 
    //void (*b_transport_handler)(xtlm::aximm_payload& trans, sc_core::sc_time& t,int si_num);
    //unsigned int (*transport_dbg_handler)(xtlm::aximm_payload& trans,int si_num);
    smartconnect_xtlm* sxtlm_ptr;
};
}
#endif
