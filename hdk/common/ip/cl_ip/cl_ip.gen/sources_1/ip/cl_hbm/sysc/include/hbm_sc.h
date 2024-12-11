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

#ifndef HBM_V1_0_H
#define HBM_V1_0_H

#include <systemc>
#include "xtlm.h"
#include "hbmModel.h"
#include "utils/xtlm_aximm_initiator_stub.h"

class hbm_sc : public sc_module{
  public:
    SC_HAS_PROCESS(hbm_sc);
    explicit hbm_sc(sc_core::sc_module_name, xsc::common_cpp::properties);
    virtual ~hbm_sc();

    xtlm::xtlm_aximm_target_socket *SAXI_00_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_01_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_02_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_03_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_04_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_05_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_06_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_07_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_08_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_09_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_10_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_11_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_12_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_13_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_14_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_15_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_16_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_17_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_18_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_19_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_20_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_21_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_22_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_23_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_24_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_25_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_26_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_27_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_28_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_29_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_30_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_31_wr_socket;

    xtlm::xtlm_aximm_target_socket *SAXI_00_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_01_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_02_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_03_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_04_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_05_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_06_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_07_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_08_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_09_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_10_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_11_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_12_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_13_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_14_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_15_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_16_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_17_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_18_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_19_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_20_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_21_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_22_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_23_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_24_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_25_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_26_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_27_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_28_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_29_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_30_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_31_rd_socket;

    xtlm::xtlm_aximm_target_socket *SAXI_00_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_00_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_01_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_01_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_02_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_02_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_03_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_03_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_04_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_04_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_05_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_05_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_06_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_06_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_07_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_07_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_08_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_08_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_09_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_09_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_10_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_10_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_11_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_11_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_12_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_12_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_13_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_13_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_14_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_14_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_15_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_15_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_16_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_16_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_17_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_17_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_18_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_18_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_19_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_19_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_20_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_20_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_21_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_21_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_22_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_22_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_23_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_23_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_24_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_24_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_25_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_25_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_26_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_26_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_27_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_27_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_28_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_28_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_29_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_29_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_30_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_30_8HI_rd_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_31_8HI_wr_socket;
    xtlm::xtlm_aximm_target_socket *SAXI_31_8HI_rd_socket;

    std::vector<xtlm::xtlm_aximm_initiator_stub*> stubInitSkt;

    sc_in<bool> HBM_REF_CLK_0;
    sc_in<bool> HBM_REF_CLK_1;

    sc_in<bool> AXI_00_ACLK;
    sc_in<bool> AXI_01_ACLK;
    sc_in<bool> AXI_02_ACLK;
    sc_in<bool> AXI_03_ACLK;
    sc_in<bool> AXI_04_ACLK;
    sc_in<bool> AXI_05_ACLK;
    sc_in<bool> AXI_06_ACLK;
    sc_in<bool> AXI_07_ACLK;
    sc_in<bool> AXI_08_ACLK;
    sc_in<bool> AXI_09_ACLK;
    sc_in<bool> AXI_10_ACLK;
    sc_in<bool> AXI_11_ACLK;
    sc_in<bool> AXI_12_ACLK;
    sc_in<bool> AXI_13_ACLK;
    sc_in<bool> AXI_14_ACLK;
    sc_in<bool> AXI_15_ACLK;
    sc_in<bool> AXI_16_ACLK;
    sc_in<bool> AXI_17_ACLK;
    sc_in<bool> AXI_18_ACLK;
    sc_in<bool> AXI_19_ACLK;
    sc_in<bool> AXI_20_ACLK;
    sc_in<bool> AXI_21_ACLK;
    sc_in<bool> AXI_22_ACLK;
    sc_in<bool> AXI_23_ACLK;
    sc_in<bool> AXI_24_ACLK;
    sc_in<bool> AXI_25_ACLK;
    sc_in<bool> AXI_26_ACLK;
    sc_in<bool> AXI_27_ACLK;
    sc_in<bool> AXI_28_ACLK;
    sc_in<bool> AXI_29_ACLK;
    sc_in<bool> AXI_30_ACLK;
    sc_in<bool> AXI_31_ACLK;

    sc_in<bool> AXI_00_ARESET_N;
    sc_in<bool> AXI_01_ARESET_N;
    sc_in<bool> AXI_02_ARESET_N;
    sc_in<bool> AXI_03_ARESET_N;
    sc_in<bool> AXI_04_ARESET_N;
    sc_in<bool> AXI_05_ARESET_N;
    sc_in<bool> AXI_06_ARESET_N;
    sc_in<bool> AXI_07_ARESET_N;
    sc_in<bool> AXI_08_ARESET_N;
    sc_in<bool> AXI_09_ARESET_N;
    sc_in<bool> AXI_10_ARESET_N;
    sc_in<bool> AXI_11_ARESET_N;
    sc_in<bool> AXI_12_ARESET_N;
    sc_in<bool> AXI_13_ARESET_N;
    sc_in<bool> AXI_14_ARESET_N;
    sc_in<bool> AXI_15_ARESET_N;
    sc_in<bool> AXI_16_ARESET_N;
    sc_in<bool> AXI_17_ARESET_N;
    sc_in<bool> AXI_18_ARESET_N;
    sc_in<bool> AXI_19_ARESET_N;
    sc_in<bool> AXI_20_ARESET_N;
    sc_in<bool> AXI_21_ARESET_N;
    sc_in<bool> AXI_22_ARESET_N;
    sc_in<bool> AXI_23_ARESET_N;
    sc_in<bool> AXI_24_ARESET_N;
    sc_in<bool> AXI_25_ARESET_N;
    sc_in<bool> AXI_26_ARESET_N;
    sc_in<bool> AXI_27_ARESET_N;
    sc_in<bool> AXI_28_ARESET_N;
    sc_in<bool> AXI_29_ARESET_N;
    sc_in<bool> AXI_30_ARESET_N;
    sc_in<bool> AXI_31_ARESET_N;

    xsc::utils::xsc_stub_port AXI_00_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_01_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_02_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_03_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_04_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_05_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_06_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_07_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_08_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_09_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_10_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_11_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_12_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_13_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_14_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_15_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_16_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_17_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_18_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_19_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_20_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_21_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_22_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_23_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_24_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_25_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_26_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_27_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_28_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_29_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_30_WDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_31_WDATA_PARITY;
    xsc::utils::xsc_stub_port APB_0_PWDATA;
    xsc::utils::xsc_stub_port APB_0_PADDR;
    xsc::utils::xsc_stub_port APB_0_PCLK;
    xsc::utils::xsc_stub_port APB_0_PENABLE;
    xsc::utils::xsc_stub_port APB_0_PRESET_N;
    xsc::utils::xsc_stub_port APB_0_PSEL;
    xsc::utils::xsc_stub_port APB_0_PWRITE;
    xsc::utils::xsc_stub_port APB_1_PWDATA;
    xsc::utils::xsc_stub_port APB_1_PADDR;
    xsc::utils::xsc_stub_port APB_1_PCLK;
    xsc::utils::xsc_stub_port APB_1_PENABLE;
    xsc::utils::xsc_stub_port APB_1_PRESET_N;
    xsc::utils::xsc_stub_port APB_1_PSEL;
    xsc::utils::xsc_stub_port APB_1_PWRITE;
    xsc::utils::xsc_stub_port AXI_00_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_01_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_02_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_03_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_04_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_05_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_06_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_07_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_08_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_09_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_10_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_11_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_12_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_13_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_14_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_15_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_16_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_17_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_18_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_19_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_20_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_21_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_22_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_23_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_24_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_25_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_26_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_27_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_28_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_29_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_30_RDATA_PARITY;
    xsc::utils::xsc_stub_port AXI_31_RDATA_PARITY;
    xsc::utils::xsc_stub_port APB_0_PRDATA;
    xsc::utils::xsc_stub_port APB_0_PREADY;
    xsc::utils::xsc_stub_port APB_0_PSLVERR;
    xsc::utils::xsc_stub_port APB_1_PRDATA;
    xsc::utils::xsc_stub_port APB_1_PREADY;
    xsc::utils::xsc_stub_port APB_1_PSLVERR;
    xsc::utils::xsc_stub_port apb_complete_0;
    xsc::utils::xsc_stub_port apb_complete_1;
    xsc::utils::xsc_stub_port DRAM_0_STAT_CATTRIP;
    xsc::utils::xsc_stub_port DRAM_0_STAT_TEMP;
    xsc::utils::xsc_stub_port DRAM_1_STAT_CATTRIP;
    xsc::utils::xsc_stub_port DRAM_1_STAT_TEMP;

  private:
    sc_signal<bool> HBM_REF_CLK_0_sig;
    sc_signal<bool> HBM_REF_CLK_1_sig;

    sc_signal<bool> AXI_00_ACLK_sig;
    sc_signal<bool> AXI_01_ACLK_sig;
    sc_signal<bool> AXI_02_ACLK_sig;
    sc_signal<bool> AXI_03_ACLK_sig;
    sc_signal<bool> AXI_04_ACLK_sig;
    sc_signal<bool> AXI_05_ACLK_sig;
    sc_signal<bool> AXI_06_ACLK_sig;
    sc_signal<bool> AXI_07_ACLK_sig;
    sc_signal<bool> AXI_08_ACLK_sig;
    sc_signal<bool> AXI_09_ACLK_sig;
    sc_signal<bool> AXI_10_ACLK_sig;
    sc_signal<bool> AXI_11_ACLK_sig;
    sc_signal<bool> AXI_12_ACLK_sig;
    sc_signal<bool> AXI_13_ACLK_sig;
    sc_signal<bool> AXI_14_ACLK_sig;
    sc_signal<bool> AXI_15_ACLK_sig;
    sc_signal<bool> AXI_16_ACLK_sig;
    sc_signal<bool> AXI_17_ACLK_sig;
    sc_signal<bool> AXI_18_ACLK_sig;
    sc_signal<bool> AXI_19_ACLK_sig;
    sc_signal<bool> AXI_20_ACLK_sig;
    sc_signal<bool> AXI_21_ACLK_sig;
    sc_signal<bool> AXI_22_ACLK_sig;
    sc_signal<bool> AXI_23_ACLK_sig;
    sc_signal<bool> AXI_24_ACLK_sig;
    sc_signal<bool> AXI_25_ACLK_sig;
    sc_signal<bool> AXI_26_ACLK_sig;
    sc_signal<bool> AXI_27_ACLK_sig;
    sc_signal<bool> AXI_28_ACLK_sig;
    sc_signal<bool> AXI_29_ACLK_sig;
    sc_signal<bool> AXI_30_ACLK_sig;
    sc_signal<bool> AXI_31_ACLK_sig;

    sc_signal<bool> AXI_00_ARESET_N_sig;
    sc_signal<bool> AXI_01_ARESET_N_sig;
    sc_signal<bool> AXI_02_ARESET_N_sig;
    sc_signal<bool> AXI_03_ARESET_N_sig;
    sc_signal<bool> AXI_04_ARESET_N_sig;
    sc_signal<bool> AXI_05_ARESET_N_sig;
    sc_signal<bool> AXI_06_ARESET_N_sig;
    sc_signal<bool> AXI_07_ARESET_N_sig;
    sc_signal<bool> AXI_08_ARESET_N_sig;
    sc_signal<bool> AXI_09_ARESET_N_sig;
    sc_signal<bool> AXI_10_ARESET_N_sig;
    sc_signal<bool> AXI_11_ARESET_N_sig;
    sc_signal<bool> AXI_12_ARESET_N_sig;
    sc_signal<bool> AXI_13_ARESET_N_sig;
    sc_signal<bool> AXI_14_ARESET_N_sig;
    sc_signal<bool> AXI_15_ARESET_N_sig;
    sc_signal<bool> AXI_16_ARESET_N_sig;
    sc_signal<bool> AXI_17_ARESET_N_sig;
    sc_signal<bool> AXI_18_ARESET_N_sig;
    sc_signal<bool> AXI_19_ARESET_N_sig;
    sc_signal<bool> AXI_20_ARESET_N_sig;
    sc_signal<bool> AXI_21_ARESET_N_sig;
    sc_signal<bool> AXI_22_ARESET_N_sig;
    sc_signal<bool> AXI_23_ARESET_N_sig;
    sc_signal<bool> AXI_24_ARESET_N_sig;
    sc_signal<bool> AXI_25_ARESET_N_sig;
    sc_signal<bool> AXI_26_ARESET_N_sig;
    sc_signal<bool> AXI_27_ARESET_N_sig;
    sc_signal<bool> AXI_28_ARESET_N_sig;
    sc_signal<bool> AXI_29_ARESET_N_sig;
    sc_signal<bool> AXI_30_ARESET_N_sig;
    sc_signal<bool> AXI_31_ARESET_N_sig;

    hbmModel *mdl;
};

#endif
