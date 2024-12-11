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

#include "axi_crossbar.h"
#include "xtlm_simple_interconnect_model.h"
#include <cmath>
axi_crossbar::axi_crossbar(sc_module_name name, xsc::common_cpp::properties& properties) {
  uint64_t num_mi=properties.getLongLong("C_NUM_MASTER_SLOTS");
  uint64_t num_si=properties.getLongLong("C_NUM_SLAVE_SLOTS");
  uint64_t axi_data_width=properties.getLongLong("C_AXI_DATA_WIDTH");
  uint64_t axi_addr_width=properties.getLongLong("C_AXI_ADDR_WIDTH");
  properties.addLong("C_NUM_MI", std::to_string(num_mi));
  properties.addLong("C_NUM_SI", std::to_string(num_si));
  m_report_handler=new xsc::common_cpp::report_handler("report_handler");
  //m_report_handler->set_verbosity_level(xsc::common_cpp::VERBOSITY::DEBUG);
  for(uint64_t i=0;i<num_si;i++) {
    std::stringstream ss;
    ss<<"C_S";
    if(i<10) {
      ss<<"0";
    }
    ss<<i<<"_AXI_DATA_WIDTH";
    properties.addLong(ss.str().c_str(),std::to_string(axi_data_width));
  }
  for(uint64_t i=0;i<num_mi;i++) {
    std::stringstream ss;
    ss<<"C_M";
    if(i<10) {
      ss<<"0";
    }
    ss<<i<<"_AXI_DATA_WIDTH";
    properties.addLong(ss.str().c_str(),std::to_string(axi_data_width));
  }
  for(uint64_t i=0;i<num_si;i++) {
    std::stringstream ss;
    ss<<"C_S";
    if(i<10) {
      ss<<"0";
    }
    ss<<i<<"_AXI_ADDR_WIDTH";
    properties.addLong(ss.str().c_str(),std::to_string(axi_addr_width));
  }
  for(uint64_t i=0;i<num_mi;i++) {
    std::stringstream ss;
    ss<<"C_M";
    if(i<10) {
      ss<<"0";
    }
    ss<<i<<"_AXI_ADDR_WIDTH";
    properties.addLong(ss.str().c_str(),std::to_string(axi_addr_width));
  }
  unsigned int len;
  std::string axi_conn=properties.getBitString("C_M_AXI_WRITE_CONNECTIVITY",len);

 for(uint64_t j=0;j<num_mi;j++) {
  std::string m_axi_conn=axi_conn.substr(j*32,32);
  for(int start=0;start<num_si;start++)
  {
      int i=31-start;
      std::stringstream ss;
      ss.str("");
      ss<<"C_M";
      if(j<10) ss<<"0";
      ss<<j<<"_S";
      if(start<10) ss<<"0";
      ss<<start<<"_CONNECTIVITY";
      std::string connectivity=m_axi_conn.substr(i,1);
      properties.addLong(ss.str().c_str(),connectivity);
      if(m_report_handler->get_verbosity_level()==xsc::common_cpp::VERBOSITY::DEBUG) {
      std::stringstream m_ss;
      m_ss.str("");
      m_ss<<this->name()<<"ADD PROPERTY CONNECTIVITY"<<ss.str().c_str()<<" "<<connectivity<<std::endl;
      XSC_REPORT_INFO_VERB((*m_report_handler),"crossbar",m_ss.str().c_str(),DEBUG);
      }
    }
  }
  uint64_t num_addr_ranges= properties.getLongLong("C_NUM_ADDR_RANGES");
  properties.addLong("C_ADDR_RANGES",std::to_string(num_addr_ranges));
  unsigned int range;
  std::string addr_range=properties.getBitString("C_M_AXI_BASE_ADDR",range);
  for(int start=0;start<num_mi;start++)
  {
    std::string base_addr_range=addr_range.substr(start*num_addr_ranges*64,64*num_addr_ranges);
    auto tmpstr = base_addr_range.c_str();
    const char *ptr = nullptr;
    unsigned long long toValue;
    toValue = 0;
    for(uint64_t j=0;j<num_addr_ranges;j++) {
      int num_range=num_addr_ranges -j -1;
      toValue = 0;
      ptr = tmpstr +j*64;
      for(int i = 0 ; i < 64 ; i++)
      {
       if(ptr[63-i] != '0')
           toValue += ((unsigned long long)1 << i);
      }
      int t=num_mi-start-1;
      std::stringstream ss;
      ss.str("");
      ss<<"C_M";
      if(t<10) ss<<"0";
      ss<<t<<"_A";
      if(num_range<10) ss<<"0";
      ss<<num_range;
      ss<<"_BASE_ADDRESS";
      properties.addLong(ss.str().c_str(),std::to_string(toValue));
      if(m_report_handler->get_verbosity_level()==xsc::common_cpp::VERBOSITY::DEBUG) {
      std::stringstream m_ss;
      m_ss.str("");
      m_ss<<this->name()<<"ADD PROPERTY BASE"<<std::hex<<ss.str().c_str()<<" "<<toValue<<std::endl;
      XSC_REPORT_INFO_VERB((*m_report_handler),"crossbar",m_ss.str().c_str(),DEBUG);
      }
    }    
  }  
   unsigned int addr_rng;
  std::string master_addr_range=properties.getBitString("C_M_AXI_ADDR_WIDTH",addr_rng);
  for(int start=0;start<num_mi;start++)
  {
    std::string master_base_addr_range=master_addr_range.substr(start*32*num_addr_ranges,32*num_addr_ranges);
    auto tmpstr = master_base_addr_range.c_str();
    const char *ptr = nullptr;
    unsigned long long toValue;
    toValue = 0;
    for(uint64_t j=0;j<num_addr_ranges;j++) {
      int num_range=num_addr_ranges -j -1;
      toValue = 0;
      ptr = tmpstr +j*32 ;
      for(int i = 0 ; i < 32  ; i++)
      {
       if(ptr[31-i] != '0')
           toValue += ((unsigned long long)1 << i);
      }
      int t=num_mi-start-1;
      std::stringstream ss;
      ss.str("");
      ss<<"C_M";
      if(t<10) ss<<"0";
      ss<<t<<"_A";
      if(num_range<10) ss<<"0";
      ss<<num_range;
      ss<<"_ADDR_RANGE";
      toValue=((toValue<=64)?toValue:64);
      unsigned long long rangeVal= pow(2,toValue);
      properties.addLong(ss.str().c_str(),std::to_string(rangeVal));
      if(m_report_handler->get_verbosity_level()==xsc::common_cpp::VERBOSITY::DEBUG) {
      std::stringstream m_ss;
      m_ss.str("");
      m_ss<<this->name()<<"ADD PROPERTY RANGE"<<std::hex<<ss.str().c_str()<<" "<<rangeVal<<std::endl;
      XSC_REPORT_INFO_VERB((*m_report_handler),"crossbar",m_ss.str().c_str(),DEBUG);
      }
      if(toValue==0){
      std::stringstream ss;
      ss.str("");
      ss<<"C_M";
      if(t<10) ss<<"0";
      ss<<t<<"_A";
      if(num_range<10) ss<<"0";
      ss<<num_range;
      ss<<"_BASE_ADDRESS";
      properties.addLong(ss.str().c_str(),std::to_string(0));
      if(m_report_handler->get_verbosity_level()==xsc::common_cpp::VERBOSITY::DEBUG) {
      std::stringstream m_ss;
      m_ss.str("");
      m_ss<<this->name()<<"ADD PROPERTY BASE"<<std::hex<<ss.str().c_str()<<" "<<toValue<<std::endl;
      XSC_REPORT_INFO_VERB((*m_report_handler),"crossbar",m_ss.str().c_str(),DEBUG);
      }
      }
    }    
  }
  m_model = new xtlm_simple_interconnect_model("icn", properties);
  initiator_0_rd_socket = m_model->initiator_rd_sockets[0];
  initiator_0_wr_socket = m_model->initiator_wr_sockets[0];
  initiator_1_rd_socket = m_model->initiator_rd_sockets[1];
  initiator_1_wr_socket = m_model->initiator_wr_sockets[1];
  initiator_2_rd_socket = m_model->initiator_rd_sockets[2];
  initiator_2_wr_socket = m_model->initiator_wr_sockets[2];
  initiator_3_rd_socket = m_model->initiator_rd_sockets[3];
  initiator_3_wr_socket = m_model->initiator_wr_sockets[3];
  initiator_4_rd_socket = m_model->initiator_rd_sockets[4];
  initiator_4_wr_socket = m_model->initiator_wr_sockets[4];
  initiator_5_rd_socket = m_model->initiator_rd_sockets[5];
  initiator_5_wr_socket = m_model->initiator_wr_sockets[5];
  initiator_6_rd_socket = m_model->initiator_rd_sockets[6];
  initiator_6_wr_socket = m_model->initiator_wr_sockets[6];
  initiator_7_rd_socket = m_model->initiator_rd_sockets[7];
  initiator_7_wr_socket = m_model->initiator_wr_sockets[7];
  initiator_8_rd_socket = m_model->initiator_rd_sockets[8];
  initiator_8_wr_socket = m_model->initiator_wr_sockets[8];
  initiator_9_rd_socket = m_model->initiator_rd_sockets[9];
  initiator_9_wr_socket = m_model->initiator_wr_sockets[9];
  initiator_10_rd_socket = m_model->initiator_rd_sockets[10];
  initiator_10_wr_socket = m_model->initiator_wr_sockets[10];
  initiator_11_rd_socket = m_model->initiator_rd_sockets[11];
  initiator_11_wr_socket = m_model->initiator_wr_sockets[11];
  initiator_12_rd_socket = m_model->initiator_rd_sockets[12];
  initiator_12_wr_socket = m_model->initiator_wr_sockets[12];
  initiator_13_rd_socket = m_model->initiator_rd_sockets[13];

  initiator_13_wr_socket = m_model->initiator_wr_sockets[13];

  initiator_14_rd_socket = m_model->initiator_rd_sockets[14];

  initiator_14_wr_socket = m_model->initiator_wr_sockets[14];

  initiator_15_rd_socket = m_model->initiator_rd_sockets[15];

  initiator_15_wr_socket = m_model->initiator_wr_sockets[15];


  target_0_rd_socket = m_model->target_rd_sockets[0];

  target_0_wr_socket = m_model->target_wr_sockets[0];

  target_1_rd_socket = m_model->target_rd_sockets[1];

  target_1_wr_socket = m_model->target_wr_sockets[1];

  target_2_rd_socket = m_model->target_rd_sockets[2];

  target_2_wr_socket = m_model->target_wr_sockets[2];

  target_3_rd_socket = m_model->target_rd_sockets[3];

  target_3_wr_socket = m_model->target_wr_sockets[3];

  target_4_rd_socket = m_model->target_rd_sockets[4];

  target_4_wr_socket = m_model->target_wr_sockets[4];

  target_5_rd_socket = m_model->target_rd_sockets[5];

  target_5_wr_socket = m_model->target_wr_sockets[5];

  target_6_rd_socket = m_model->target_rd_sockets[6];

  target_6_wr_socket = m_model->target_wr_sockets[6];

  target_7_rd_socket = m_model->target_rd_sockets[7];

  target_7_wr_socket = m_model->target_wr_sockets[7];

  target_8_rd_socket = m_model->target_rd_sockets[8];

  target_8_wr_socket = m_model->target_wr_sockets[8];

  target_9_rd_socket = m_model->target_rd_sockets[9];

  target_9_wr_socket = m_model->target_wr_sockets[9];

  target_10_rd_socket = m_model->target_rd_sockets[10];

  target_10_wr_socket = m_model->target_wr_sockets[10];

  target_11_rd_socket = m_model->target_rd_sockets[11];

  target_11_wr_socket = m_model->target_wr_sockets[11];

  target_12_rd_socket = m_model->target_rd_sockets[12];
  target_12_wr_socket = m_model->target_wr_sockets[12];
  target_13_rd_socket = m_model->target_rd_sockets[13];
  target_13_wr_socket = m_model->target_wr_sockets[13];
  target_14_rd_socket = m_model->target_rd_sockets[14];
  target_14_wr_socket = m_model->target_wr_sockets[14];
  target_15_rd_socket = m_model->target_rd_sockets[15];
  target_15_wr_socket = m_model->target_wr_sockets[15];

}

axi_crossbar::~axi_crossbar() {
  delete m_model;
}
