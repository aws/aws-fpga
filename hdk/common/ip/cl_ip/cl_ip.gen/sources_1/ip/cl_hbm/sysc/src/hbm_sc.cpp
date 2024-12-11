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

#include "hbm_sc.h"
#include <cmath>

hbm_sc::hbm_sc(sc_module_name nm, xsc::common_cpp::properties properties):
  sc_module(nm)
  ,SAXI_00_wr_socket(nullptr)
  ,SAXI_00_rd_socket(nullptr)
{
  unsigned numStack = properties.getLongLong("HBM_STACK");
  std::vector<bool> SAXIxExists(32);
  for (int i = 0; i < 32; i++){
    std::string propName = "SAXI_xx"; sprintf(&propName[5], "%02d", i);
    SAXIxExists[i] = properties.getBool(propName);
  }
  bool stack8Hi = properties.getBool("STACK_8HI");
  mdl = new hbmModel("hbmIp", properties);

  if (SAXIxExists[0]) {
    if(stack8Hi){
      SAXI_00_8HI_wr_socket = &(mdl->if_wr_socket[0]);
      SAXI_00_8HI_rd_socket = &(mdl->if_rd_socket[0]);
    }else{
      SAXI_00_wr_socket = &(mdl->if_wr_socket[0]);
      SAXI_00_rd_socket = &(mdl->if_rd_socket[0]);
    }
  } else {
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt0", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[0]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt0", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[0]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    AXI_00_ACLK.bind(AXI_00_ACLK_sig);
    AXI_00_ARESET_N.bind(AXI_00_ARESET_N_sig);
  }
  if (SAXIxExists[1]) {
    if(stack8Hi){
      SAXI_01_8HI_wr_socket = &(mdl->if_wr_socket[1]);
      SAXI_01_8HI_rd_socket = &(mdl->if_rd_socket[1]);
    }else{
      SAXI_01_wr_socket = &(mdl->if_wr_socket[1]);
      SAXI_01_rd_socket = &(mdl->if_rd_socket[1]);
    }
  } else {
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt1", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[1]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt1", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[1]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    AXI_01_ACLK.bind(AXI_01_ACLK_sig);
    AXI_01_ARESET_N.bind(AXI_01_ARESET_N_sig);
  }
  if (SAXIxExists[2]) {
    if(stack8Hi){
      SAXI_02_8HI_wr_socket = &(mdl->if_wr_socket[2]);
      SAXI_02_8HI_rd_socket = &(mdl->if_rd_socket[2]);
    }else{
      SAXI_02_wr_socket = &(mdl->if_wr_socket[2]);
      SAXI_02_rd_socket = &(mdl->if_rd_socket[2]);
    }
  } else {
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt2", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[2]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt2", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[2]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    AXI_02_ACLK.bind(AXI_02_ACLK_sig);
    AXI_02_ARESET_N.bind(AXI_02_ARESET_N_sig);
  }
  if (SAXIxExists[3]) {
    if(stack8Hi){
      SAXI_03_8HI_wr_socket = &(mdl->if_wr_socket[3]);
      SAXI_03_8HI_rd_socket = &(mdl->if_rd_socket[3]);
    }else{
      SAXI_03_wr_socket = &(mdl->if_wr_socket[3]);
      SAXI_03_rd_socket = &(mdl->if_rd_socket[3]);
    }
  } else {
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt3", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[3]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt3", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[3]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    AXI_03_ACLK.bind(AXI_03_ACLK_sig);
    AXI_03_ARESET_N.bind(AXI_03_ARESET_N_sig);
  }
  if (SAXIxExists[4]) {
    if(stack8Hi){
      SAXI_04_8HI_wr_socket = &(mdl->if_wr_socket[4]);
      SAXI_04_8HI_rd_socket = &(mdl->if_rd_socket[4]);
    }else{
      SAXI_04_wr_socket = &(mdl->if_wr_socket[4]);
      SAXI_04_rd_socket = &(mdl->if_rd_socket[4]);
    }
  } else {
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt4", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[4]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt4", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[4]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    AXI_04_ACLK.bind(AXI_04_ACLK_sig);
    AXI_04_ARESET_N.bind(AXI_04_ARESET_N_sig);
  }
  if (SAXIxExists[5]) {
    if(stack8Hi){
      SAXI_05_8HI_wr_socket = &(mdl->if_wr_socket[5]);
      SAXI_05_8HI_rd_socket = &(mdl->if_rd_socket[5]);
    }else{
      SAXI_05_wr_socket = &(mdl->if_wr_socket[5]);
      SAXI_05_rd_socket = &(mdl->if_rd_socket[5]);
    }
  } else {
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt5", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[5]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt5", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[5]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    AXI_05_ACLK.bind(AXI_05_ACLK_sig);
    AXI_05_ARESET_N.bind(AXI_05_ARESET_N_sig);
  }
  if (SAXIxExists[6]) {
    if(stack8Hi){
      SAXI_06_8HI_wr_socket = &(mdl->if_wr_socket[6]);
      SAXI_06_8HI_rd_socket = &(mdl->if_rd_socket[6]);
    }else{
      SAXI_06_wr_socket = &(mdl->if_wr_socket[6]);
      SAXI_06_rd_socket = &(mdl->if_rd_socket[6]);
    }
  } else {
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt6", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[6]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt6", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[6]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    AXI_06_ACLK.bind(AXI_06_ACLK_sig);
    AXI_06_ARESET_N.bind(AXI_06_ARESET_N_sig);
  }
  if (SAXIxExists[7]) {
    if(stack8Hi){
      SAXI_07_8HI_wr_socket = &(mdl->if_wr_socket[7]);
      SAXI_07_8HI_rd_socket = &(mdl->if_rd_socket[7]);
    }else{
      SAXI_07_wr_socket = &(mdl->if_wr_socket[7]);
      SAXI_07_rd_socket = &(mdl->if_rd_socket[7]);
    }
  } else {
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt7", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[7]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt7", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[7]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    AXI_07_ACLK.bind(AXI_07_ACLK_sig);
    AXI_07_ARESET_N.bind(AXI_07_ARESET_N_sig);
  }
  if (SAXIxExists[8]) {
    if(stack8Hi){
      SAXI_08_8HI_wr_socket = &(mdl->if_wr_socket[8]);
      SAXI_08_8HI_rd_socket = &(mdl->if_rd_socket[8]);
    }else{
      SAXI_08_wr_socket = &(mdl->if_wr_socket[8]);
      SAXI_08_rd_socket = &(mdl->if_rd_socket[8]);
    }
  } else {
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt8", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[8]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt8", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[8]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    AXI_08_ACLK.bind(AXI_08_ACLK_sig);
    AXI_08_ARESET_N.bind(AXI_08_ARESET_N_sig);
  }
  if (SAXIxExists[9]) {
    if(stack8Hi){
      SAXI_09_8HI_wr_socket = &(mdl->if_wr_socket[9]);
      SAXI_09_8HI_rd_socket = &(mdl->if_rd_socket[9]);
    }else{
      SAXI_09_wr_socket = &(mdl->if_wr_socket[9]);
      SAXI_09_rd_socket = &(mdl->if_rd_socket[9]);
    }
  } else {
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt9", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[9]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt9", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[9]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    AXI_09_ACLK.bind(AXI_09_ACLK_sig);
    AXI_09_ARESET_N.bind(AXI_09_ARESET_N_sig);
  }
  if (SAXIxExists[10]) {
    if(stack8Hi){
      SAXI_10_8HI_wr_socket = &(mdl->if_wr_socket[10]);
      SAXI_10_8HI_rd_socket = &(mdl->if_rd_socket[10]);
    }else{
      SAXI_10_wr_socket = &(mdl->if_wr_socket[10]);
      SAXI_10_rd_socket = &(mdl->if_rd_socket[10]);
    }
  } else {
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt10", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[10]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt10", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[10]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    AXI_10_ACLK.bind(AXI_10_ACLK_sig);
    AXI_10_ARESET_N.bind(AXI_10_ARESET_N_sig);
  }
  if (SAXIxExists[11]) {
    if(stack8Hi){
      SAXI_11_8HI_wr_socket = &(mdl->if_wr_socket[11]);
      SAXI_11_8HI_rd_socket = &(mdl->if_rd_socket[11]);
    }else{
      SAXI_11_wr_socket = &(mdl->if_wr_socket[11]);
      SAXI_11_rd_socket = &(mdl->if_rd_socket[11]);
    }
  } else {
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt11", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[11]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt11", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[11]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    AXI_11_ACLK.bind(AXI_11_ACLK_sig);
    AXI_11_ARESET_N.bind(AXI_11_ARESET_N_sig);
  }
  if (SAXIxExists[12]) {
    if(stack8Hi){
      SAXI_12_8HI_wr_socket = &(mdl->if_wr_socket[12]);
      SAXI_12_8HI_rd_socket = &(mdl->if_rd_socket[12]);
    }else{
      SAXI_12_wr_socket = &(mdl->if_wr_socket[12]);
      SAXI_12_rd_socket = &(mdl->if_rd_socket[12]);
    }
  } else {
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt12", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[12]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt12", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[12]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    AXI_12_ACLK.bind(AXI_12_ACLK_sig);
    AXI_12_ARESET_N.bind(AXI_12_ARESET_N_sig);
  }
  if (SAXIxExists[13]) {
    if(stack8Hi){
      SAXI_13_8HI_wr_socket = &(mdl->if_wr_socket[13]);
      SAXI_13_8HI_rd_socket = &(mdl->if_rd_socket[13]);
    }else{
      SAXI_13_wr_socket = &(mdl->if_wr_socket[13]);
      SAXI_13_rd_socket = &(mdl->if_rd_socket[13]);
    }
  } else {
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt13", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[13]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt13", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[13]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    AXI_13_ACLK.bind(AXI_13_ACLK_sig);
    AXI_13_ARESET_N.bind(AXI_13_ARESET_N_sig);
  }
  if (SAXIxExists[14]) {
    if(stack8Hi){
      SAXI_14_8HI_wr_socket = &(mdl->if_wr_socket[14]);
      SAXI_14_8HI_rd_socket = &(mdl->if_rd_socket[14]);
    }else{
      SAXI_14_wr_socket = &(mdl->if_wr_socket[14]);
      SAXI_14_rd_socket = &(mdl->if_rd_socket[14]);
    }
  } else {
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt14", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[14]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt14", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[14]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    AXI_14_ACLK.bind(AXI_14_ACLK_sig);
    AXI_14_ARESET_N.bind(AXI_14_ARESET_N_sig);
  }
  if (SAXIxExists[15]) {
    if(stack8Hi){
      SAXI_15_8HI_wr_socket = &(mdl->if_wr_socket[15]);
      SAXI_15_8HI_rd_socket = &(mdl->if_rd_socket[15]);
    }else{
      SAXI_15_wr_socket = &(mdl->if_wr_socket[15]);
      SAXI_15_rd_socket = &(mdl->if_rd_socket[15]);
    }
  } else {
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt15", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[15]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt15", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[15]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    AXI_15_ACLK.bind(AXI_15_ACLK_sig);
    AXI_15_ARESET_N.bind(AXI_15_ARESET_N_sig);
  }
  if (SAXIxExists[16]) {
    if(stack8Hi){
      SAXI_16_8HI_wr_socket = &(mdl->if_wr_socket[16]);
      SAXI_16_8HI_rd_socket = &(mdl->if_rd_socket[16]);
    }else{
      SAXI_16_wr_socket = &(mdl->if_wr_socket[16]);
      SAXI_16_rd_socket = &(mdl->if_rd_socket[16]);
    }
  } else {
    if(numStack == 2){
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt16", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[16]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt16", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[16]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    }
    AXI_16_ACLK.bind(AXI_16_ACLK_sig);
    AXI_16_ARESET_N.bind(AXI_16_ARESET_N_sig);
  }
  if (SAXIxExists[17]) {
    if(stack8Hi){
      SAXI_17_8HI_wr_socket = &(mdl->if_wr_socket[17]);
      SAXI_17_8HI_rd_socket = &(mdl->if_rd_socket[17]);
    }else{
      SAXI_17_wr_socket = &(mdl->if_wr_socket[17]);
      SAXI_17_rd_socket = &(mdl->if_rd_socket[17]);
    }
  } else {
    if(numStack == 2){
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt17", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[17]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt17", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[17]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    }
    AXI_17_ACLK.bind(AXI_17_ACLK_sig);
    AXI_17_ARESET_N.bind(AXI_17_ARESET_N_sig);
  }
  if (SAXIxExists[18]) {
    if(stack8Hi){
      SAXI_18_8HI_wr_socket = &(mdl->if_wr_socket[18]);
      SAXI_18_8HI_rd_socket = &(mdl->if_rd_socket[18]);
    }else{
      SAXI_18_wr_socket = &(mdl->if_wr_socket[18]);
      SAXI_18_rd_socket = &(mdl->if_rd_socket[18]);
    }
  } else {
    if(numStack == 2){
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt18", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[18]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt18", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[18]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    }
    AXI_18_ACLK.bind(AXI_18_ACLK_sig);
    AXI_18_ARESET_N.bind(AXI_18_ARESET_N_sig);
  }
  if (SAXIxExists[19]) {
    if(stack8Hi){
      SAXI_19_8HI_wr_socket = &(mdl->if_wr_socket[19]);
      SAXI_19_8HI_rd_socket = &(mdl->if_rd_socket[19]);
    }else{
      SAXI_19_wr_socket = &(mdl->if_wr_socket[19]);
      SAXI_19_rd_socket = &(mdl->if_rd_socket[19]);
    }
  } else {
    if(numStack == 2){
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt19", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[19]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt19", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[19]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    }
    AXI_19_ACLK.bind(AXI_19_ACLK_sig);
    AXI_19_ARESET_N.bind(AXI_19_ARESET_N_sig);
  }
  if (SAXIxExists[20]) {
    if(stack8Hi){
      SAXI_20_8HI_wr_socket = &(mdl->if_wr_socket[20]);
      SAXI_20_8HI_rd_socket = &(mdl->if_rd_socket[20]);
    }else{
      SAXI_20_wr_socket = &(mdl->if_wr_socket[20]);
      SAXI_20_rd_socket = &(mdl->if_rd_socket[20]);
    }
  } else {
    if(numStack == 2){
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt20", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[20]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt20", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[20]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    }
    AXI_20_ACLK.bind(AXI_20_ACLK_sig);
    AXI_20_ARESET_N.bind(AXI_20_ARESET_N_sig);
  }
  if (SAXIxExists[21]) {
    if(stack8Hi){
      SAXI_21_8HI_wr_socket = &(mdl->if_wr_socket[21]);
      SAXI_21_8HI_rd_socket = &(mdl->if_rd_socket[21]);
    }else{
      SAXI_21_wr_socket = &(mdl->if_wr_socket[21]);
      SAXI_21_rd_socket = &(mdl->if_rd_socket[21]);
    }
  } else {
    if(numStack == 2){
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt21", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[21]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt21", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[21]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    }
    AXI_21_ACLK.bind(AXI_21_ACLK_sig);
    AXI_21_ARESET_N.bind(AXI_21_ARESET_N_sig);
  }
  if (SAXIxExists[22]) {
    if(stack8Hi){
      SAXI_22_8HI_wr_socket = &(mdl->if_wr_socket[22]);
      SAXI_22_8HI_rd_socket = &(mdl->if_rd_socket[22]);
    }else{
      SAXI_22_wr_socket = &(mdl->if_wr_socket[22]);
      SAXI_22_rd_socket = &(mdl->if_rd_socket[22]);
    }
  } else {
    if(numStack == 2){
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt22", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[22]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt22", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[22]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    }
    AXI_22_ACLK.bind(AXI_22_ACLK_sig);
    AXI_22_ARESET_N.bind(AXI_22_ARESET_N_sig);
  }
  if (SAXIxExists[23]) {
    if(stack8Hi){
      SAXI_23_8HI_wr_socket = &(mdl->if_wr_socket[23]);
      SAXI_23_8HI_rd_socket = &(mdl->if_rd_socket[23]);
    }else{
      SAXI_23_wr_socket = &(mdl->if_wr_socket[23]);
      SAXI_23_rd_socket = &(mdl->if_rd_socket[23]);
    }
  } else {
    if(numStack == 2){
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt23", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[23]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt23", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[23]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    }
    AXI_23_ACLK.bind(AXI_23_ACLK_sig);
    AXI_23_ARESET_N.bind(AXI_23_ARESET_N_sig);
  }
  if (SAXIxExists[24]) {
    if(stack8Hi){
      SAXI_24_8HI_wr_socket = &(mdl->if_wr_socket[24]);
      SAXI_24_8HI_rd_socket = &(mdl->if_rd_socket[24]);
    }else{
      SAXI_24_wr_socket = &(mdl->if_wr_socket[24]);
      SAXI_24_rd_socket = &(mdl->if_rd_socket[24]);
    }
  } else {
    if(numStack == 2){
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt24", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[24]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt24", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[24]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    }
    AXI_24_ACLK.bind(AXI_24_ACLK_sig);
    AXI_24_ARESET_N.bind(AXI_24_ARESET_N_sig);
  }
  if (SAXIxExists[25]) {
    if(stack8Hi){
      SAXI_25_8HI_wr_socket = &(mdl->if_wr_socket[25]);
      SAXI_25_8HI_rd_socket = &(mdl->if_rd_socket[25]);
    }else{
      SAXI_25_wr_socket = &(mdl->if_wr_socket[25]);
      SAXI_25_rd_socket = &(mdl->if_rd_socket[25]);
    }
  } else {
    if(numStack == 2){
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt25", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[25]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt25", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[25]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    }
    AXI_25_ACLK.bind(AXI_25_ACLK_sig);
    AXI_25_ARESET_N.bind(AXI_25_ARESET_N_sig);
  }
  if (SAXIxExists[26]) {
    if(stack8Hi){
      SAXI_26_8HI_wr_socket = &(mdl->if_wr_socket[26]);
      SAXI_26_8HI_rd_socket = &(mdl->if_rd_socket[26]);
    }else{
      SAXI_26_wr_socket = &(mdl->if_wr_socket[26]);
      SAXI_26_rd_socket = &(mdl->if_rd_socket[26]);
    }
  } else {
    if(numStack == 2){
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt26", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[26]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt26", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[26]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    }
    AXI_26_ACLK.bind(AXI_26_ACLK_sig);
    AXI_26_ARESET_N.bind(AXI_26_ARESET_N_sig);
  }
  if (SAXIxExists[27]) {
    if(stack8Hi){
      SAXI_27_8HI_wr_socket = &(mdl->if_wr_socket[27]);
      SAXI_27_8HI_rd_socket = &(mdl->if_rd_socket[27]);
    }else{
      SAXI_27_wr_socket = &(mdl->if_wr_socket[27]);
      SAXI_27_rd_socket = &(mdl->if_rd_socket[27]);
    }
  } else {
    if(numStack == 2){
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt27", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[27]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt27", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[27]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    }
    AXI_27_ACLK.bind(AXI_27_ACLK_sig);
    AXI_27_ARESET_N.bind(AXI_27_ARESET_N_sig);
  }
  if (SAXIxExists[28]) {
    if(stack8Hi){
      SAXI_28_8HI_wr_socket = &(mdl->if_wr_socket[28]);
      SAXI_28_8HI_rd_socket = &(mdl->if_rd_socket[28]);
    }else{
      SAXI_28_wr_socket = &(mdl->if_wr_socket[28]);
      SAXI_28_rd_socket = &(mdl->if_rd_socket[28]);
    }
  } else {
    if(numStack == 2){
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt28", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[28]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt28", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[28]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    }
    AXI_28_ACLK.bind(AXI_28_ACLK_sig);
    AXI_28_ARESET_N.bind(AXI_28_ARESET_N_sig);
  }
  if (SAXIxExists[29]) {
    if(stack8Hi){
      SAXI_29_8HI_wr_socket = &(mdl->if_wr_socket[29]);
      SAXI_29_8HI_rd_socket = &(mdl->if_rd_socket[29]);
    }else{
      SAXI_29_wr_socket = &(mdl->if_wr_socket[29]);
      SAXI_29_rd_socket = &(mdl->if_rd_socket[29]);
    }
  } else {
    if(numStack == 2){
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt29", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[29]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt29", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[29]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    }
    AXI_29_ACLK.bind(AXI_29_ACLK_sig);
    AXI_29_ARESET_N.bind(AXI_29_ARESET_N_sig);
  }
  if (SAXIxExists[30]) {
    if(stack8Hi){
      SAXI_30_8HI_wr_socket = &(mdl->if_wr_socket[30]);
      SAXI_30_8HI_rd_socket = &(mdl->if_rd_socket[30]);
    }else{
      SAXI_30_wr_socket = &(mdl->if_wr_socket[30]);
      SAXI_30_rd_socket = &(mdl->if_rd_socket[30]);
    }
  } else {
    if(numStack == 2){
    auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt30", HBM_AXI_DATA_WIDTH);
    stubWr->bind(mdl->if_wr_socket[30]);
    auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt30", HBM_AXI_DATA_WIDTH);
    stubRd->bind(mdl->if_rd_socket[30]);
    stubInitSkt.push_back(stubWr);
    stubInitSkt.push_back(stubRd);
    }
    AXI_30_ACLK.bind(AXI_30_ACLK_sig);
    AXI_30_ARESET_N.bind(AXI_30_ARESET_N_sig);
  }
  if (SAXIxExists[31]) {
    if(stack8Hi){
      SAXI_31_8HI_wr_socket = &(mdl->if_wr_socket[31]);
      SAXI_31_8HI_rd_socket = &(mdl->if_rd_socket[31]);
    }else{
      SAXI_31_wr_socket = &(mdl->if_wr_socket[31]);
      SAXI_31_rd_socket = &(mdl->if_rd_socket[31]);
    }
  } else {
    if(numStack == 2){
      auto* stubWr = new xtlm::xtlm_aximm_initiator_stub("ifWrStubskt31", HBM_AXI_DATA_WIDTH);
      stubWr->bind(mdl->if_wr_socket[31]);
      auto* stubRd = new xtlm::xtlm_aximm_initiator_stub("ifRdStubskt31", HBM_AXI_DATA_WIDTH);
      stubRd->bind(mdl->if_rd_socket[31]);
      stubInitSkt.push_back(stubWr);
      stubInitSkt.push_back(stubRd);
    }
    AXI_31_ACLK.bind(AXI_31_ACLK_sig);
    AXI_31_ARESET_N.bind(AXI_31_ARESET_N_sig);
  }

  if(numStack < 2){
    HBM_REF_CLK_1.bind(HBM_REF_CLK_1_sig);
  }
  if (numStack < 1) {
    HBM_REF_CLK_0.bind(HBM_REF_CLK_0_sig);
  }
}

hbm_sc::~hbm_sc(){
  delete mdl; 
  for(auto pSkt: stubInitSkt){
    delete pSkt;
  }
}
