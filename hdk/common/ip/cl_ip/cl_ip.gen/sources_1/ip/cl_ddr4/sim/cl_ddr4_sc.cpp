// (c) Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
// (c) Copyright 2022-2024 Advanced Micro Devices, Inc. All rights reserved.
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
// 
// DO NOT MODIFY THIS FILE.


#include "cl_ddr4_sc.h"

#include "sim_ddr_v2_0.h"

#include <map>
#include <string>

cl_ddr4_sc::cl_ddr4_sc(const sc_core::sc_module_name& nm) : sc_core::sc_module(nm), mp_impl(NULL)
{
  // configure connectivity manager
  xsc::utils::xsc_sim_manager::addInstance("cl_ddr4", this);

  // initialize module
    xsc::common_cpp::properties model_param_props;
    model_param_props.addBool("C0.DDR4_AUTO_AP_COL_A3", "true");
    model_param_props.addBool("C0.DDR4_Ecc", "true");
    model_param_props.addLong("C0.APP_ADDR_WIDTH", "33");
    model_param_props.addLong("C0.DDR4_CS_ADDR", "33");
    model_param_props.addLong("C0.DDR4_DQ_WIDTH", "72");
    model_param_props.addLong("C0.DDR4_nCK_PER_CLK", "4");
    model_param_props.addLong("C0.DDR4_DM_WIDTH", "9");
    model_param_props.addLong("C0.DDR4_DQS_WIDTH", "18");
    model_param_props.addLong("C0.DDR4_nCS_PER_RANK", "2");
    model_param_props.addLong("C0.DDR4_MEM_DEVICE_WIDTH", "72");
    model_param_props.addLong("C0.DDR4_ROW_WIDTH", "18");
    model_param_props.addLong("C0.DDR4_ADDR_WIDTH", "18");
    model_param_props.addLong("C0.DDR4_BANK_WIDTH", "2");
    model_param_props.addLong("C0.DDR4_BANK_GROUP_WIDTH", "2");
    model_param_props.addLong("LR_WIDTH", "1");
    model_param_props.addLong("C0.DDR4_CK_WIDTH", "2");
    model_param_props.addLong("C0.DDR4_CKE_WIDTH", "2");
    model_param_props.addLong("C0.DDR4_CS_WIDTH", "2");
    model_param_props.addLong("C0.DDR4_ODT_WIDTH", "2");
    model_param_props.addLong("C0.DDR4_COLUMN_WIDTH", "10");
    model_param_props.addLong("C0.DDR4_MEM_COMP_WIDTH", "4");
    model_param_props.addLong("C0.DDR4_DATABITS_PER_STROBE", "4");
    model_param_props.addLong("C0.DDR4_RANK_WIDTH", "2");
    model_param_props.addLong("C0.DDR4_MIN_PERIOD", "938");
    model_param_props.addLong("C0.DDR4_MAX_PERIOD", "1600");
    model_param_props.addLong("C0.DDR4_tCK", "938");
    model_param_props.addLong("C0.DDR4_CLKOUT0_DIVIDE", "6");
    model_param_props.addLong("C0.DDR4_CLKOUT1_DIVIDE", "0");
    model_param_props.addLong("C0.DDR4_CLKFBOUT_MULT", "16");
    model_param_props.addLong("C0.DDR4_DIVCLK_DIVIDE", "1");
    model_param_props.addLong("CAL_INPUT_CLK_PERIOD", "10005");
    model_param_props.addLong("C0.DDR4_CLKIN_PERIOD", "10005");
    model_param_props.addLong("C0.DDR4_DCI_CASCADE_CUTOFF", "938");
    model_param_props.addLong("C0.DDR4_AXI_ID_WIDTH", "16");
    model_param_props.addLong("C0.DDR4_AXI_ADDR_WIDTH", "36");
    model_param_props.addLong("C0.DDR4_AXI_DATA_WIDTH", "512");
    model_param_props.addLong("C0.DDR4_MEM_SIZE", "68719476736");
    model_param_props.addLong("C0.DDR4_Slot", "1");
    model_param_props.addLong("C0.APP_DATA_WIDTH", "512");
    model_param_props.addLong("C0.APP_MASK_WIDTH", "64");
    model_param_props.addLong("C0.DDR4_StackHeight", "1");
    model_param_props.addLong("CLKOUT0_DIVIDE", "0");
    model_param_props.addLong("CLKOUT1_DIVIDE", "0");
    model_param_props.addLong("CLKOUT2_DIVIDE", "0");
    model_param_props.addLong("CLKOUT3_DIVIDE", "0");
    model_param_props.addLong("CLKOUT4_DIVIDE", "0");
    model_param_props.addLong("CLKOUT6_DIVIDE", "0");
    model_param_props.addFloat("C0.DDR4_VrefVoltage", "0.84");
    model_param_props.addFloat("C0.DDR4_UI_CLOCK", "266500000");
    model_param_props.addFloat("M_ADDN_UI_CLKOUT1_FREQ_HZ", "0.0");
    model_param_props.addFloat("M_ADDN_UI_CLKOUT2_FREQ_HZ", "0.0");
    model_param_props.addFloat("M_ADDN_UI_CLKOUT3_FREQ_HZ", "0.0");
    model_param_props.addFloat("M_ADDN_UI_CLKOUT4_FREQ_HZ", "0.0");
    model_param_props.addFloat("M_ADDN_UI_CLKOUT1_PHASE", "0");
    model_param_props.addFloat("M_ADDN_UI_CLKOUT2_PHASE", "0");
    model_param_props.addFloat("M_ADDN_UI_CLKOUT3_PHASE", "0");
    model_param_props.addFloat("M_ADDN_UI_CLKOUT4_PHASE", "0");
    model_param_props.addString("C0.DDR4_Mem_Add_Map", "ROW_COLUMN_BANK_INTLV");
    model_param_props.addString("System_Clock", "Differential");
    model_param_props.addString("C0.ControllerType", "DDR4_SDRAM");
    model_param_props.addString("C0.MEM_TYPE", "DDR4");
    model_param_props.addString("C0.BUFG_LOC_1", "X0Y46");
    model_param_props.addString("C0.BUFG_LOC_2", "X0Y7");
    model_param_props.addString("C0.BUFG_DIV_LOC_1", "X0Y7");
    model_param_props.addString("C0.BUFG_DIV_LOC_2", "X0Y6");
    model_param_props.addString("C0.PBLOCK_SLICE_LOC", "0");
    model_param_props.addString("C0.PBLOCK_RAMB36_LOC", "0");
    model_param_props.addString("C0.PBLOCK_RAMB18_LOC", "0");
    model_param_props.addString("C0.PBLOCK_SLICE_LOC_SC", "0");
    model_param_props.addString("C0.PBLOCK_RAMB36_LOC_SC", "0");
    model_param_props.addString("C0.PBLOCK_RAMB18_LOC_SC", "0");
    model_param_props.addString("C0.MMCM_IDX_BANK", "1");
    model_param_props.addString("C0.CENTER_BANK_CLOCK_REGION", "0");
    model_param_props.addString("C0.CENTER_BANK_MMCME3_ADV_SITE", "0");
    model_param_props.addString("C0.SYSCLK_CENTER_INFO", "FALSE");
    model_param_props.addString("PING_PONG_PHY", "1");
    model_param_props.addString("C0.DDR4_AL", "0");
    model_param_props.addString("C0.DDR4_USE_DM_PORT", "0");
    model_param_props.addString("C0.DDR4_USE_CS_PORT", "1");
    model_param_props.addString("C0.DDR4_MEMORY_TYPE", "RDIMMs");
    model_param_props.addString("C0.DDR4_MEMORY_PART", "M393A8G40BB4-CWE_64GB_CUSTOM");
    model_param_props.addString("C0.DDR4_DATA_MASK", "18");
    model_param_props.addString("C0.DDR4_SPEED_GRADE", "2133");
    model_param_props.addString("C0.DDR4_MEM_DENSITY", "64GB");
    model_param_props.addString("C0.DDR4_MEM_DENSITY_MB", "16384");
    model_param_props.addString("C0.DDR4_MEM_DENSITY_GB", "16");
    model_param_props.addString("C0.DDR4_COMP_DENSITY", "16Gb");
    model_param_props.addString("C0.DDR4_MODEL_SPEED_GRADE", "");
    model_param_props.addString("C0.DDR4_IO_VOLTAGE", "1.2V");
    model_param_props.addString("C0.DDR4_MR0", "0");
    model_param_props.addString("C0.DDR4_MR2", "0");
    model_param_props.addString("C0.DDR4_nAL", "0");
    model_param_props.addString("C0.DDR4_BURST_MODE", "0");
    model_param_props.addString("C0.DDR4_BURST_TYPE", "0");
    model_param_props.addString("C0.DDR4_CL", "0");
    model_param_props.addString("C0.DDR4_CWL", "0");
    model_param_props.addString("C0.DDR4_OUTPUT_DRV", "0");
    model_param_props.addString("C0.DDR4_RTT_NOM", "0");
    model_param_props.addString("C0.DDR4_RTT_WR", "0");
    model_param_props.addString("C0.DDR4_MEM", "0");
    model_param_props.addString("C0.DDR4_DBAW", "0");
    model_param_props.addString("C0.DDR4_Configuration", "0");
    model_param_props.addString("C0.DDR4_tCKE", "0");
    model_param_props.addString("C0.DDR4_tFAW", "16");
    model_param_props.addString("C0.DDR4_tFAW_dlr", "");
    model_param_props.addString("C0.DDR4_tMRD", "2");
    model_param_props.addString("C0.DDR4_tRAS", "36");
    model_param_props.addString("C0.DDR4_tRCD", "15");
    model_param_props.addString("C0.DDR4_tREFI", "8315");
    model_param_props.addString("C0.DDR4_tRFC", "374");
    model_param_props.addString("C0.DDR4_tRFC_dlr", "");
    model_param_props.addString("C0.DDR4_tRP", "15");
    model_param_props.addString("C0.DDR4_tWR", "16");
    model_param_props.addString("C0.DDR4_tRRD", "");
    model_param_props.addString("C0.DDR4_tRTP", "8");
    model_param_props.addString("C0.DDR4_tRRD_S", "4");
    model_param_props.addString("C0.DDR4_tRRD_L", "6");
    model_param_props.addString("C0.DDR4_tRRD_dlr", "");
    model_param_props.addString("C0.DDR4_tWTR", "");
    model_param_props.addString("C0.DDR4_tWTR_S", "3");
    model_param_props.addString("C0.DDR4_tWTR_L", "8");
    model_param_props.addString("C0.DDR4_tXPR", "96");
    model_param_props.addString("C0.DDR4_tZQI", "0");
    model_param_props.addString("C0.DDR4_tZQCS", "128");
    model_param_props.addString("C0.DDR4_tZQINIT", "256");
    model_param_props.addString("C0.DDR4_tCCD_3ds", "");
    model_param_props.addString("C0.DDR4_CLKOUTPHY_MODE", "VCO_2X");
    model_param_props.addString("C0.DDR4_HR_MIN_FREQ", "0");
    model_param_props.addString("C0.DDR4_IS_FASTER_SPEED_RAM", "No");
    model_param_props.addString("C0.DDR4_CA_MIRROR", "1");
    model_param_props.addString("C0.DDR4_IS_CUSTOM", "true");
    model_param_props.addString("C0.DDR4_MCS_ECC", "0");
    model_param_props.addString("CUSTOM_PART_ATTRIBUTES", "CustomPart_Address__width 18$CustomPart_Bank__group__width 2$CustomPart_Bank__width 2$CustomPart_CA__Mirror 1$CustomPart_CKE__width 2$CustomPart_CK__width 2$CustomPart_CS__width 2$CustomPart_Column__width 10$CustomPart_Component__density 16Gb$CustomPart_Data__bits__per__strobe 4$CustomPart_Data__mask 0$CustomPart_Data__widths 72$CustomPart_IO__Voltages 1.2V$CustomPart_Max__period 1600$CustomPart_Memory__component__width 4$CustomPart_Memory__density 64GB$CustomPart_Memory__device__width 72$CustomPart_Memory__speed__grade 2133$CustomPart_Min__period 938$CustomPart_ODT__width 2$CustomPart_Part__name M393A8G40BB4-CWE_64GB_CUSTOM$CustomPart_Part__type RDIMMs$CustomPart_Rank 2$CustomPart_Row__width 18$CustomPart_StackHeight 1$CustomPart_burst__length 8$CustomPart_cas__latency 15$CustomPart_cas__write__latency 11$CustomPart_tCCD_3ds 0$CustomPart_tCKE 5000 ps$CustomPart_tFAW 15000 ps$CustomPart_tFAW_dlr 0$CustomPart_tMRD 8 tck$CustomPart_tRAS 33000 ps$CustomPart_tRCD 14060 ps$CustomPart_tREFI 7800000 ps$CustomPart_tRFC 350000 ps$CustomPart_tRFC_dlr 0$CustomPart_tRP 14060 ps$CustomPart_tRRD_L 5300 ps$CustomPart_tRRD_S 3700 ps$CustomPart_tRRD_dlr 0$CustomPart_tRTP 7500 ps$CustomPart_tWR 15000 ps$CustomPart_tWTR_L 7500 ps$CustomPart_tWTR_S 2500 ps$CustomPart_tXPR 360 ns$CustomPart_tZQCS 128 tck$CustomPart_tZQINIT 1024 tck$");
    model_param_props.addString("Debug_Signal", "Disable");
    model_param_props.addString("Simulation_Mode", "BFM");
    model_param_props.addString("COMPONENT_NAME", "cl_ddr4");

  mp_impl = new sim_ddr_v2_0("inst", model_param_props);

  // initialize AXI sockets
  C0_DDR_SAXI_CTRL_rd_socket = mp_impl->C0_DDR_SAXI_CTRL_rd_socket;
  C0_DDR_SAXI_CTRL_wr_socket = mp_impl->C0_DDR_SAXI_CTRL_wr_socket;
  C0_DDR_SAXI_rd_socket = mp_impl->C0_DDR_SAXI_rd_socket;
  C0_DDR_SAXI_wr_socket = mp_impl->C0_DDR_SAXI_wr_socket;
}

cl_ddr4_sc::~cl_ddr4_sc()
{
  xsc::utils::xsc_sim_manager::clean();

  delete mp_impl;
}

