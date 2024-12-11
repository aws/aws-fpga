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

#include <systemc>
#include "xtlm.h"
#include "hbmChannel.h"

#define HBM_AXI_DATA_WIDTH 256

//class customWrUtil;
//class customRdUtil;

class hbmModel : public sc_module {
 public:
  SC_HAS_PROCESS(hbmModel);
  explicit hbmModel(sc_core::sc_module_name, xsc::common_cpp::properties);
  virtual ~hbmModel();

  unsigned int transport_dbg(xtlm::aximm_payload&);
  xsc::common_cpp::report_handler* rH;
  xsc::memory* mem;

 protected:
 private:
  xsc::common_cpp::properties mProps;
  bool stack8Hi;
  unsigned numStack;
  sc_core::sc_vector<hbmChannel> chan;
  unsigned channelSize;
  float axiClkFreq;
  sc_time axiClkPrd;
  bool latencyEnabled;

 public:
  sc_core::sc_vector<xtlm::xtlm_aximm_target_socket> if_wr_socket;
  sc_core::sc_vector<xtlm::xtlm_aximm_target_socket> if_rd_socket;

 private:

  sc_core::sc_vector<xtlm::xtlm_aximm_initiator_socket> hbm_wr_socket;
  sc_core::sc_vector<xtlm::xtlm_aximm_initiator_socket> hbm_rd_socket;
  //sc_core::sc_vector<xtlm::xtlm_aximm_target_rd_socket_util> target_rd_sockets_util;
  //sc_core::sc_vector<xtlm::xtlm_aximm_target_wr_socket_util> target_wr_sockets_util;
  sc_core::sc_vector<customRdUtil> target_rd_sockets_util;
  sc_core::sc_vector<customWrUtil> target_wr_sockets_util;
  sc_core::sc_vector<xtlm::xtlm_aximm_initiator_rd_socket_util> initiator_rd_sockets_util;
  sc_core::sc_vector<xtlm::xtlm_aximm_initiator_wr_socket_util> initiator_wr_sockets_util;

  template <typename T>
  T* createSocketVector(sc_module_name);

  void handleSlaveReadCmd(int);
  void handleSlaveWriteCmd(int);
  void handleSlaveReadResp(int);
  void handleSlaveWriteResp(int);
  unsigned getHbmChannel(uint64_t);
  unsigned getSwitchLatency(unsigned, unsigned);
  uint64_t getUniqAxiId(std::pair<uint32_t, uint32_t>);
  std::pair<uint32_t, uint32_t> getOrigIds(uint64_t);
};
