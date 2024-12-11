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

#ifndef XTLM_SIMPLE_INTERCONNECT_H_
#define XTLM_SIMPLE_INTERCONNECT_H_

#include "xtlm.h"
class xtlm_simple_interconnect_model;
class axi_crossbar: public sc_core::sc_module {
public:
	axi_crossbar(sc_module_name name, xsc::common_cpp::properties& properties);
	virtual ~axi_crossbar();
  xsc::common_cpp::report_handler* m_report_handler;
	//Socket_declaration
		xtlm::xtlm_aximm_initiator_socket* initiator_0_rd_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_0_wr_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_1_rd_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_1_wr_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_2_rd_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_2_wr_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_3_rd_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_3_wr_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_4_rd_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_4_wr_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_5_rd_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_5_wr_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_6_rd_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_6_wr_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_7_rd_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_7_wr_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_8_rd_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_8_wr_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_9_rd_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_9_wr_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_10_rd_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_10_wr_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_11_rd_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_11_wr_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_12_rd_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_12_wr_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_13_rd_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_13_wr_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_14_rd_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_14_wr_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_15_rd_socket;
		xtlm::xtlm_aximm_initiator_socket* initiator_15_wr_socket;
		
		xtlm::xtlm_aximm_target_socket* target_0_rd_socket;
		xtlm::xtlm_aximm_target_socket* target_0_wr_socket;
		xtlm::xtlm_aximm_target_socket* target_1_rd_socket;
		xtlm::xtlm_aximm_target_socket* target_1_wr_socket;
		xtlm::xtlm_aximm_target_socket* target_2_rd_socket;
		xtlm::xtlm_aximm_target_socket* target_2_wr_socket;
		xtlm::xtlm_aximm_target_socket* target_3_rd_socket;
		xtlm::xtlm_aximm_target_socket* target_3_wr_socket;
		xtlm::xtlm_aximm_target_socket* target_4_rd_socket;
		xtlm::xtlm_aximm_target_socket* target_4_wr_socket;
		xtlm::xtlm_aximm_target_socket* target_5_rd_socket;
		xtlm::xtlm_aximm_target_socket* target_5_wr_socket;
		xtlm::xtlm_aximm_target_socket* target_6_rd_socket;
		xtlm::xtlm_aximm_target_socket* target_6_wr_socket;
		xtlm::xtlm_aximm_target_socket* target_7_rd_socket;
		xtlm::xtlm_aximm_target_socket* target_7_wr_socket;
		xtlm::xtlm_aximm_target_socket* target_8_rd_socket;
		xtlm::xtlm_aximm_target_socket* target_8_wr_socket;
		xtlm::xtlm_aximm_target_socket* target_9_rd_socket;
		xtlm::xtlm_aximm_target_socket* target_9_wr_socket;
		xtlm::xtlm_aximm_target_socket* target_10_rd_socket;
		xtlm::xtlm_aximm_target_socket* target_10_wr_socket;
		xtlm::xtlm_aximm_target_socket* target_11_rd_socket;
		xtlm::xtlm_aximm_target_socket* target_11_wr_socket;
		xtlm::xtlm_aximm_target_socket* target_12_rd_socket;
		xtlm::xtlm_aximm_target_socket* target_12_wr_socket;
		xtlm::xtlm_aximm_target_socket* target_13_rd_socket;
		xtlm::xtlm_aximm_target_socket* target_13_wr_socket;
		xtlm::xtlm_aximm_target_socket* target_14_rd_socket;
		xtlm::xtlm_aximm_target_socket* target_14_wr_socket;
		xtlm::xtlm_aximm_target_socket* target_15_rd_socket;
		xtlm::xtlm_aximm_target_socket* target_15_wr_socket;	
		sc_in<bool> aclk;
		sc_in<bool> aresetn;
		private :
	  xtlm_simple_interconnect_model* m_model;
};

#endif /* XTLM_SIMPLE_INTERCONNECT_H_ */
