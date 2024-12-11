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

#include "hbmModel.h"
#include <cmath>

hbmModel::hbmModel(sc_module_name nm, xsc::common_cpp::properties properties) : sc_module(nm), mProps(properties)
                                                                                ,stack8Hi(mProps.getBool("STACK_8HI"))
                                                                                //,stack8Hi(false)
                                                                                ,numStack(mProps.getLongLong("HBM_STACK"))
                                                                                ,chan("channel")
                                                                                ,channelSize((stack8Hi ? 0x20000000 : 0x10000000))
                                                                                ,axiClkFreq(mProps.getFloat("AXI_CLK_FREQ"))
                                                                                ,if_wr_socket("if_wr_socket")
                                                                                ,if_rd_socket("if_rd_socket")
                                                                                ,hbm_wr_socket("hbm_wr_skt")
                                                                                ,hbm_rd_socket("hbm_rd_skt")
                                                                                ,target_wr_sockets_util("target_wr_util")
                                                                                ,target_rd_sockets_util("target_rd_util")
                                                                                ,initiator_rd_sockets_util("Init_rd_util")
                                                                                ,initiator_wr_sockets_util("Init_wr_util")
                                                                                {
  axiClkPrd = sc_time(double(1000) / axiClkFreq, SC_NS);
  rH = new xsc::common_cpp::report_handler("reportHandlerHbm");
  uint64_t memSize = (uint64_t)channelSize * numStack * 16;

  std::string memName = this->name();
  memName += "_memory";
  if (getenv("HWEMU_MEMORY_PERSISTENCE")){
    mem = new xsc::memory(memName.c_str(), memSize, this->rH, true );  //memory instance created with persistent storage
  } else {
    mem = new xsc::memory(memName.c_str(), memSize, this->rH );  //memory instance created without persistent storage
  }

  chan.init(numStack * 16, [this](const char* nm, size_t i) -> hbmChannel* {
      std::string prop_1 = "USER_MC"+std::to_string(i/2)+"_ADDR_BIT";
      std::string prop_2 = "HBM_CLK_FREQ_"+std::to_string(i/16);
      uint64_t mapStart = i * channelSize;
      return new hbmChannel(nm, mapStart, this->channelSize, this->mProps.getString(prop_1), this->mProps.getLongLong(prop_2), this->rH, mem); });

  if_wr_socket.init(numStack * 16, [](const char* nm, size_t i) -> xtlm::xtlm_aximm_target_socket* { return new xtlm::xtlm_aximm_target_socket(nm, HBM_AXI_DATA_WIDTH); });
  if_rd_socket.init(numStack * 16, [](const char* nm, size_t i) -> xtlm::xtlm_aximm_target_socket* { return new xtlm::xtlm_aximm_target_socket(nm, HBM_AXI_DATA_WIDTH); });

  hbm_wr_socket.init(numStack * 16, [](const char* nm, size_t i) -> xtlm::xtlm_aximm_initiator_socket* {
    return new xtlm::xtlm_aximm_initiator_socket(nm, HBM_AXI_DATA_WIDTH); });
  hbm_rd_socket.init(numStack * 16, [](const char* nm, size_t i) -> xtlm::xtlm_aximm_initiator_socket* {
    return new xtlm::xtlm_aximm_initiator_socket(nm, HBM_AXI_DATA_WIDTH); });
  /*target_wr_sockets_util.init(numStack * 16, [](const char* nm, size_t i) -> xtlm::xtlm_aximm_target_wr_socket_util* {
    return new xtlm::xtlm_aximm_target_wr_socket_util(nm, xtlm::aximm::TRANSACTION, HBM_AXI_DATA_WIDTH);
    });*/
  target_wr_sockets_util.init(numStack * 16,[](const char* nm, size_t i)->customWrUtil*{ return new customWrUtil(nm, xtlm::aximm::TRANSACTION, HBM_AXI_DATA_WIDTH);});
  target_rd_sockets_util.init(numStack * 16,[](const char* nm, size_t i)->customRdUtil*{ return new customRdUtil(nm, xtlm::aximm::TRANSACTION, HBM_AXI_DATA_WIDTH);});

  initiator_rd_sockets_util.init(numStack * 16,[](const char* nm, size_t i)->xtlm::xtlm_aximm_initiator_rd_socket_util*{
    return new xtlm::xtlm_aximm_initiator_rd_socket_util(nm, xtlm::aximm::TRANSACTION, HBM_AXI_DATA_WIDTH); });
  initiator_wr_sockets_util.init(numStack * 16,[](const char* nm, size_t i)->xtlm::xtlm_aximm_initiator_wr_socket_util*{
    return new xtlm::xtlm_aximm_initiator_wr_socket_util(nm, xtlm::aximm::TRANSACTION, HBM_AXI_DATA_WIDTH); });

  //if_rd_socket.bind(sc_core::sc_assemble_vector(target_rd_sockets_util, &xtlm::xtlm_aximm_target_rd_socket_util::rd_socket));
  //if_wr_socket.bind(sc_core::sc_assemble_vector(target_wr_sockets_util, &xtlm::xtlm_aximm_target_wr_socket_util::wr_socket));
  if_wr_socket.bind(sc_core::sc_assemble_vector<customWrUtil, xtlm::xtlm_aximm_target_socket>(target_wr_sockets_util, &customWrUtil::wr_socket));
  if_rd_socket.bind(sc_core::sc_assemble_vector<customRdUtil, xtlm::xtlm_aximm_target_socket>(target_rd_sockets_util, &customRdUtil::rd_socket));

  sc_core::sc_assemble_vector(initiator_rd_sockets_util, &xtlm::xtlm_aximm_initiator_rd_socket_util::rd_socket).bind(hbm_rd_socket);
  hbm_rd_socket.bind(sc_core::sc_assemble_vector(chan, &hbmChannel::rd_skt));

  sc_core::sc_assemble_vector(initiator_wr_sockets_util, &xtlm::xtlm_aximm_initiator_wr_socket_util::wr_socket).bind(hbm_wr_socket);
  hbm_wr_socket.bind(sc_core::sc_assemble_vector(chan, &hbmChannel::wr_skt));

  for(auto& utl: target_wr_sockets_util){
    utl.cb_transport_dbg = std::bind(&hbmModel::transport_dbg, this, std::placeholders::_1);
  }
  for(auto& utl: target_rd_sockets_util){
    utl.cb_transport_dbg = std::bind(&hbmModel::transport_dbg, this, std::placeholders::_1);
  }

  for (unsigned i = 0; i < (numStack * 16); i++) {
    //std::stringstream ss;
    //ss << "target_rd_socket_" << i;
    //if_rd_socket[i] = new xtlm::xtlm_aximm_target_socket(ss.str().c_str(), HBM_AXI_DATA_WIDTH);
    //ss<< "_util";
    //target_rd_sockets_util[i] = new xtlm::xtlm_aximm_target_rd_socket_util(ss.str().c_str(), xtlm::aximm::TRANSACTION, HBM_AXI_DATA_WIDTH);
    // if_rd_socket[i].bind(target_rd_sockets_util[i].rd_socket);
    std::stringstream spawn_name;
    spawn_name << "handle_slave_rd_" << i;
    sc_core::sc_spawn_options opt;
    opt.spawn_method();
    opt.dont_initialize();
    opt.set_sensitivity(&(target_rd_sockets_util[i].transaction_available));
    sc_spawn(sc_bind(&hbmModel::handleSlaveReadCmd, this, i), spawn_name.str().c_str(), &opt);

    //ss.str("");
    //ss << "target_wr_socket_" << i;
    //if_wr_socket[i] = new xtlm::xtlm_aximm_target_socket(ss.str().c_str(), HBM_AXI_DATA_WIDTH);
    //ss << "_util";
    //target_wr_sockets_util[i] = new xtlm::xtlm_aximm_target_wr_socket_util(ss.str().c_str(), xtlm::aximm::TRANSACTION, HBM_AXI_DATA_WIDTH);
    //if_wr_socket[i].bind(target_wr_sockets_util[i].wr_socket);
    spawn_name.str("");
    spawn_name << "handle_slave_wr_" << i;
    sc_core::sc_spawn_options opt1;
    opt1.spawn_method();
    opt1.dont_initialize();
    opt1.set_sensitivity(&(target_wr_sockets_util[i].transaction_available));
    sc_spawn(sc_bind(&hbmModel::handleSlaveWriteCmd, this, i), spawn_name.str().c_str(), &opt1);
  }

  for (unsigned i = 0; i < (numStack * 16); i++) {
    //std::stringstream ss;
    //ss << "initiator_rd_socket_" << i;
    //hbm_rd_socket[i] = new xtlm::xtlm_aximm_initiator_socket(ss.str().c_str(), HBM_AXI_DATA_WIDTH);
    //ss << "_util";
    //initiator_rd_sockets_util[i] = new xtlm::xtlm_aximm_initiator_rd_socket_util(ss.str().c_str(), xtlm::aximm::TRANSACTION, HBM_AXI_DATA_WIDTH);
    //initiator_rd_sockets_util[i].rd_socket.bind(hbm_rd_socket[i]);
    //hbm_rd_socket[i].bind(*(chan[i].rd_skt));
    std::stringstream spawn_name;
    spawn_name << "handle_slave_rd_resp_" << i;
    sc_core::sc_spawn_options opt;
    opt.spawn_method();
    opt.dont_initialize();
    opt.set_sensitivity(&(initiator_rd_sockets_util[i].data_available));
    sc_spawn(sc_bind(&hbmModel::handleSlaveReadResp, this, i), spawn_name.str().c_str(), &opt);

    //ss.str("");
    //ss << "initiator_wr_socket_" << i;
    //hbm_wr_socket[i] = new xtlm::xtlm_aximm_initiator_socket(ss.str().c_str(), HBM_AXI_DATA_WIDTH);
    //ss << "_util";
    //initiator_wr_sockets_util[i] = new xtlm::xtlm_aximm_initiator_wr_socket_util(ss.str().c_str(), xtlm::aximm::TRANSACTION, HBM_AXI_DATA_WIDTH);
    //initiator_wr_sockets_util[i].wr_socket.bind(hbm_wr_socket[i]);
    //hbm_wr_socket[i].bind(*(chan[i].wr_skt));
    spawn_name.str("");
    spawn_name << "handle_slave_wr_resp_" << i;
    sc_core::sc_spawn_options opt1;
    opt1.spawn_method();
    opt1.dont_initialize();
    opt1.set_sensitivity(&(initiator_wr_sockets_util[i].resp_available));
    sc_spawn(sc_bind(&hbmModel::handleSlaveWriteResp, this, i), spawn_name.str().c_str(), &opt1);
  }

  const char* envHwEmuLatencyDis = std::getenv("HW_EM_DISABLE_LATENCY");
  bool latDisabled = (envHwEmuLatencyDis != nullptr) && ((strcmp(envHwEmuLatencyDis, "true") == 0) ||
                                                         (strcmp(envHwEmuLatencyDis, "TRUE") == 0) ||
                                                         (strcmp(envHwEmuLatencyDis, "1") == 0));
  if (latDisabled) {
    latencyEnabled = false;
  } else {
    latencyEnabled = true;
  }
}

hbmModel::~hbmModel() {
}

unsigned int hbmModel::transport_dbg(xtlm::aximm_payload& trans) {
  unsigned channel = getHbmChannel(trans.get_address());
  if (trans.get_command() == xtlm::XTLM_WRITE_COMMAND) {
    return initiator_wr_sockets_util[channel].transport_dbg(trans);
  } else if (trans.get_command() == xtlm::XTLM_READ_COMMAND) {
    return initiator_rd_sockets_util[channel].transport_dbg(trans);
  }else{
    return 0;
  }
}

void hbmModel::handleSlaveReadCmd(int i) {
  REPORT_DEBUG( rH, this->name()<<".tarRdSktUtilsCb" , this->name() << "Received read TX on Fabric port["<<dec<<i<<"]")
  xtlm::aximm_payload* trans = target_rd_sockets_util[i].peek_transaction();
  unsigned channel = getHbmChannel(trans->get_address());
  unsigned lat = getSwitchLatency(i, channel);
  sc_time latDelay = lat * axiClkPrd;

  if (initiator_rd_sockets_util[channel].is_slave_ready()) {
    trans = target_rd_sockets_util[i].get_transaction();
    trans->set_axi_id(getUniqAxiId(std::make_pair(trans->get_axi_id(), i)));
    REPORT_DEBUG(rH, this->name()<<".tarRdSktUtilsCb", "@"<<sc_time_stamp()<<" - Sending read TX to channel["<<dec<<channel<<"] with delay ="<<lat<<"Cks|"<<latDelay);
    initiator_rd_sockets_util[channel].send_transaction(*trans, latDelay);
  } else {
    next_trigger(initiator_rd_sockets_util[channel].transaction_sampled);
  }
}

void hbmModel::handleSlaveWriteCmd(int i) {
  REPORT_DEBUG( rH, this->name()<<".tarWrSktUtilsCb" , this->name() << "Received write TX on Fabric port[" <<dec<<i<<"]")
  xtlm::aximm_payload* trans = target_wr_sockets_util[i].peek_transaction();
  unsigned channel = getHbmChannel(trans->get_address());
  unsigned lat = getSwitchLatency(i, channel);
  sc_time latDelay = lat * axiClkPrd;

  if (initiator_wr_sockets_util[channel].is_slave_ready()) {
    trans = target_wr_sockets_util[i].get_transaction();
    trans->set_axi_id(getUniqAxiId(std::make_pair(trans->get_axi_id(), i)));
    REPORT_DEBUG(rH, this->name()<<".tarRdSktUtilsCb", "@"<<sc_time_stamp()<<" - Sending write TX to channel["<<dec<<channel<<"] with delay ="<<lat<<"Cks|"<<latDelay);
    initiator_wr_sockets_util[channel].send_transaction(*trans, latDelay);
  } else {
    next_trigger(initiator_wr_sockets_util[channel].transaction_sampled);
  }
}

void hbmModel::handleSlaveReadResp(int i) {
  REPORT_DEBUG( rH, this->name()<<".InitRdSktUtilsCb" , this->name() << "Received Read Response on Hbm Channel[" <<dec<<i<<"]")
  xtlm::aximm_payload* trans = initiator_rd_sockets_util[i].peek_data();
  std::pair<uint32_t, uint32_t> p = getOrigIds(trans->get_axi_id());
  unsigned lat = getSwitchLatency(p.second, i);
  sc_time latDelay = lat * axiClkPrd;

  if (target_rd_sockets_util[p.second].is_master_ready()) {
    trans = initiator_rd_sockets_util[i].get_data();
    trans->set_axi_id(p.first);
    REPORT_DEBUG(rH, this->name()<<".InitRdSktUtilsCb", "@"<<sc_time_stamp()<<" - Sending read data back on Fabric Port["<<dec<<p.second<<"] with delay ="<<lat<<"Cks|"<<latDelay);
    target_rd_sockets_util[p.second].send_data(*trans, latDelay);
  } else {
    next_trigger(initiator_rd_sockets_util[i].data_available);
  }
}

void hbmModel::handleSlaveWriteResp(int i) {
  REPORT_DEBUG( rH, this->name()<<".InitWrSktUtilsCb" , this->name() << "Received Write Response on Hbm Channel[" <<dec<<i<<"]")
  xtlm::aximm_payload* trans = initiator_wr_sockets_util[i].peek_resp();
  std::pair<uint32_t, uint32_t> p = getOrigIds(trans->get_axi_id());
  unsigned lat = getSwitchLatency(p.second, i);
  sc_time latDelay = lat * axiClkPrd;

  if (target_wr_sockets_util[p.second].is_master_ready()) {
    trans = initiator_wr_sockets_util[i].get_resp();
    trans->set_axi_id(p.first);
    REPORT_DEBUG(rH, this->name()<<".InitWrSktUtilsCb", "@"<<sc_time_stamp()<<" - Sending write resp on Fabric Port["<<dec<<p.second<<"] with delay ="<<lat<<"Cks|"<<latDelay);
    target_wr_sockets_util[p.second].send_resp(*trans, latDelay);
  } else {
    next_trigger(initiator_wr_sockets_util[i].resp_available);
  }
}

//function returns number of clks wrt switching latency on path b/w fabric master and hbm channel
unsigned hbmModel::getSwitchLatency(unsigned init, unsigned tar) {
  if (latencyEnabled) {
    unsigned switchXs = (init > tar) ? (init - tar) : (tar - init);
    switchXs = (switchXs / 4) + 1;
    return (10 + (switchXs * 2) + ((switchXs > 4) ? 10 : 0));
  } else {
    return 0;
  }
  //formula for total RD/Wr latency for full to&fropath
  //(Switch enabled? 20 : 0) + (# of Quad Switch crossings * 4) + (Async Bridge crossing? 20 : 0) + (Read open page? 86 : 104) + 4 (BLI)
  //the formula used has been modified for individual forward/backward; page latencies are taken care further in channel model.
}

unsigned hbmModel::getHbmChannel(uint64_t addr) {
  unsigned portBits = (addr >> (stack8Hi ? 29 : 28)) & 0x1F;  //for stack 4H/8H addr bits [31:28]/[32:29] are used to select AXI Port resp.
  return portBits;
}

uint64_t hbmModel::getUniqAxiId(std::pair<uint32_t, uint32_t> id) {  //see https://en.wikipedia.org/wiki/Pairing_function
  uint32_t axiId = id.first;
  uint32_t mstPortId = id.second;
  return ((uint64_t(axiId + mstPortId + 1) * uint64_t(axiId + mstPortId)) / 2) + mstPortId;
}
std::pair<uint32_t, uint32_t> hbmModel::getOrigIds(uint64_t uId) {
  double w = floorl(((sqrt(8 * uId + 1) - 1) / 2));
  long double t = ((w * w) + w) / 2;
  uint32_t mstPortId = uint32_t(uId - uint64_t(t));
  uint32_t axiId = uint32_t(uint64_t(w) - mstPortId);
  return std::make_pair(axiId, mstPortId);
}
