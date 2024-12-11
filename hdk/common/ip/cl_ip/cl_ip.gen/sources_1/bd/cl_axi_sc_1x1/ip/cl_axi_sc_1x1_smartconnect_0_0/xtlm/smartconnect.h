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

#ifndef __SMARTCONNECT__H__
#define __SMARTCONNECT__H__

#include "xtlm.h"
#include "utils/xtlm_aximm_target_stub.h"
#include "utils/xtlm_aximm_initiator_stub.h"
#include "utils/xtlm_aximm_passthru_module.h"
#include <map>
#include <string>
#include "smartconnect_xtlm.h"
#include "report_handler.h"
#include<sstream>

#define si_socket(idx) \
        xtlm::xtlm_aximm_target_socket* S##idx##_AXI_tlm_aximm_read_socket; \
        xtlm::xtlm_aximm_target_socket* S##idx##_AXI_tlm_aximm_write_socket; 

#define mi_socket(idx) \
        xtlm::xtlm_aximm_initiator_socket* M##idx##_AXI_tlm_aximm_read_socket; \
        xtlm::xtlm_aximm_initiator_socket* M##idx##_AXI_tlm_aximm_write_socket; 

using namespace std;

class smartconnect :  public sc_module {

    public: 
        SC_HAS_PROCESS (smartconnect);

        smartconnect(sc_module_name nm, xsc::common_cpp::properties& properties);

        si_socket(00)
        si_socket(01)
        si_socket(02)
        si_socket(03)
        si_socket(04)
        si_socket(05)
        si_socket(06)
        si_socket(07)
        si_socket(08)
        si_socket(09)
        si_socket(10)
        si_socket(11)
        si_socket(12)
        si_socket(13)
        si_socket(14)
        si_socket(15)
        si_socket(16)
        si_socket(17)
        si_socket(18)
        si_socket(19)
        si_socket(20)
        si_socket(21)
        si_socket(22)
        si_socket(23)
        si_socket(24)
        si_socket(25)
        si_socket(26)
        si_socket(27)
        si_socket(28)
        si_socket(29)
        si_socket(30)
        si_socket(31)
        si_socket(32)
        si_socket(33)
        si_socket(34)
        si_socket(35)
        si_socket(36)
        si_socket(37)
        si_socket(38)
        si_socket(39)
        si_socket(40)
        si_socket(41)
        si_socket(42)
        si_socket(43)
        si_socket(44)
        si_socket(45)
        si_socket(46)
        si_socket(47)
        si_socket(48)
        si_socket(49)
        si_socket(50)
        si_socket(51)
        si_socket(52)
        si_socket(53)
        si_socket(54)
        si_socket(55)
        si_socket(56)
        si_socket(57)
        si_socket(58)
        si_socket(59)
        si_socket(60)
        si_socket(61)
        si_socket(62)
        si_socket(63)

        mi_socket(00)
        mi_socket(01)
        mi_socket(02)
        mi_socket(03)
        mi_socket(04)
        mi_socket(05)
        mi_socket(06)
        mi_socket(07)
        mi_socket(08)
        mi_socket(09)
        mi_socket(10)
        mi_socket(11)
        mi_socket(12)
        mi_socket(13)
        mi_socket(14)
        mi_socket(15)
        mi_socket(16)
        mi_socket(17)
        mi_socket(18)
        mi_socket(19)
        mi_socket(20)
        mi_socket(21)
        mi_socket(22)
        mi_socket(23)
        mi_socket(24)
        mi_socket(25)
        mi_socket(26)
        mi_socket(27)
        mi_socket(28)
        mi_socket(29)
        mi_socket(30)
        mi_socket(31)
        mi_socket(32)
        mi_socket(33)
        mi_socket(34)
        mi_socket(35)
        mi_socket(36)
        mi_socket(37)
        mi_socket(38)
        mi_socket(39)
        mi_socket(40)
        mi_socket(41)
        mi_socket(42)
        mi_socket(43)
        mi_socket(44)
        mi_socket(45)
        mi_socket(46)
        mi_socket(47)
        mi_socket(48)
        mi_socket(49)
        mi_socket(50)
        mi_socket(51)
        mi_socket(52)
        mi_socket(53)
        mi_socket(54)
        mi_socket(55)
        mi_socket(56)
        mi_socket(57)
        mi_socket(58)
        mi_socket(59)
        mi_socket(60)
        mi_socket(61)
        mi_socket(62)
        mi_socket(63)

        sc_in<bool> aclk;
        sc_in<bool> aclk1;
        sc_in<bool> aclk2;
        sc_in<bool> aclk3;
        sc_in<bool> aclk4;
        sc_in<bool> aclk5;
        sc_in<bool> aclk6;
        sc_in<bool> aclk7;
        sc_in<bool> aclk8;
        sc_in<bool> aclk9;
        sc_in<bool> aclk10;
        sc_in<bool> aclk11;
        sc_in<bool> aclk12;
        sc_in<bool> aclk13;
        sc_in<bool> aclk14;
        sc_in<bool> aclk15;
        
        sc_in<bool> aresetn;
        void before_end_of_elaboration();

        vector<xtlm::xtlm_aximm_target_socket*> target_rd_sockets;
        vector<xtlm::xtlm_aximm_target_socket*> target_wr_sockets;
        vector<xtlm::xtlm_aximm_initiator_socket*> initiator_rd_sockets;
        vector<xtlm::xtlm_aximm_initiator_socket*> initiator_wr_sockets;
    private:         
        // Configuration handoff from HIP instance
        map<string, string> smartconnect_config;
        smartconnect_xtlm* core_model;

        std::string filename;
        std::stringstream m_ss;
	    xsc::common_cpp::report_handler* m_report_handler;
        
        sc_core::sc_signal<bool> aresetn_signal;
};


#endif // __SMARTCONNECT__H__
