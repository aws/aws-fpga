// (c) Copyright 2023 Advanced Micro Devices, Inc. All rights reserved.
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
/*******************************************************************************

 *Device: All
 *Purpose:
 *  ILA constant values library
 * 
 *******************************************************************************/

  //--
  //--  ILA Pro command types:
  //--
  //--    These command values match those found in the documentation.  The
  //--    CONTROL bus bit offset can be derived by adding CONTROL_OFFSET to
  //--    these values.
  //--
  `define READ_STATIC_STAT_CMD      0
  `define READ_DYNAMIC_STAT_CMD     1
  `define READ_DATA_CMD             2
  `define READ_TSTAMP_CMD           3
  `define WRITE_TRIG_SETUP_CMD      4
  `define WRITE_CAP_CTRL_SETUP_CMD  5
  `define WRITE_ENABLE_EXTCAP_CMD   6
  `define WRITE_DISABLE_EXTCAP_CMD  7
  `define WRITE_ARM_CMD             8
  `define WRITE_HALT_CMD            9
  `define WRITE_RESET_CMD           10
  `define WRITE_RESET_DCM_CMD       11
  `define RESERVED_0C_CMD           12
  `define RESERVED_0D_CMD           13
  `define RESERVED_0E_CMD           14
  `define WRITE_TSEQ_TRIGOUT        15
  `define WRITE_M0_SETUP_CMD        16
  `define WRITE_M1_SETUP_CMD        17
  `define WRITE_M2_SETUP_CMD        18
  `define WRITE_M3_SETUP_CMD        19
  `define WRITE_M4_SETUP_CMD        20
  `define WRITE_M5_SETUP_CMD        21
  `define WRITE_M6_SETUP_CMD        22
  `define WRITE_M7_SETUP_CMD        23
  `define WRITE_M8_SETUP_CMD        24
  `define WRITE_M9_SETUP_CMD        25
  `define WRITE_M10_SETUP_CMD       26
  `define WRITE_M11_SETUP_CMD       27
  `define WRITE_M12_SETUP_CMD       28
  `define WRITE_M13_SETUP_CMD       29
  `define WRITE_M14_SETUP_CMD       30
  `define WRITE_M15_SETUP_CMD       31

  `define CONTROL_CMD_OFFSET        3

  `define CFG_CLK_BIT               0
  `define CFG_DIN_BIT               1
  `define UNUSED_BIT                2
  `define CFG_DOUT_BIT              3
  `define READ_STATIC_STAT_CMD_BIT      `READ_STATIC_STAT_CMD     + `CONTROL_CMD_OFFSET
  `define READ_DYNAMIC_STAT_CMD_BIT     `READ_DYNAMIC_STAT_CMD    + `CONTROL_CMD_OFFSET
  `define READ_DATA_CMD_BIT             `READ_DATA_CMD            + `CONTROL_CMD_OFFSET
  `define READ_TSTAMP_CMD_BIT           `READ_TSTAMP_CMD          + `CONTROL_CMD_OFFSET
  `define WRITE_TRIG_SETUP_CMD_BIT      `WRITE_TRIG_SETUP_CMD     + `CONTROL_CMD_OFFSET
  `define WRITE_CAP_CTRL_SETUP_CMD_BIT  `WRITE_CAP_CTRL_SETUP_CMD + `CONTROL_CMD_OFFSET
  `define WRITE_ENABLE_EXTCAP_CMD_BIT   `WRITE_ENABLE_EXTCAP_CMD  + `CONTROL_CMD_OFFSET
  `define WRITE_DISABLE_EXTCAP_CMD_BIT  `WRITE_DISABLE_EXTCAP_CMD + `CONTROL_CMD_OFFSET
  `define WRITE_ARM_CMD_BIT             `WRITE_ARM_CMD            + `CONTROL_CMD_OFFSET
  `define WRITE_HALT_CMD_BIT            `WRITE_HALT_CMD           + `CONTROL_CMD_OFFSET
  `define WRITE_RESET_CMD_BIT           `WRITE_RESET_CMD          + `CONTROL_CMD_OFFSET
  `define WRITE_RESET_DCM_CMD_BIT       `WRITE_RESET_DCM_CMD      + `CONTROL_CMD_OFFSET
  `define RESERVED_0C_CMD_BIT           `RESERVED_0C_CMD          + `CONTROL_CMD_OFFSET
  `define RESERVED_0D_CMD_BIT           `RESERVED_0D_CMD          + `CONTROL_CMD_OFFSET
  `define RESERVED_0E_CMD_BIT           `RESERVED_0E_CMD          + `CONTROL_CMD_OFFSET
  `define WRITE_TSEQ_TRIGOUT_BIT        `WRITE_TSEQ_TRIGOUT       + `CONTROL_CMD_OFFSET
  `define WRITE_M0_SETUP_CMD_BIT        `WRITE_M0_SETUP_CMD       + `CONTROL_CMD_OFFSET
  `define WRITE_M1_SETUP_CMD_BIT        `WRITE_M1_SETUP_CMD       + `CONTROL_CMD_OFFSET
  `define WRITE_M2_SETUP_CMD_BIT        `WRITE_M2_SETUP_CMD       + `CONTROL_CMD_OFFSET
  `define WRITE_M3_SETUP_CMD_BIT        `WRITE_M3_SETUP_CMD       + `CONTROL_CMD_OFFSET
  `define WRITE_M4_SETUP_CMD_BIT        `WRITE_M4_SETUP_CMD       + `CONTROL_CMD_OFFSET
  `define WRITE_M5_SETUP_CMD_BIT        `WRITE_M5_SETUP_CMD       + `CONTROL_CMD_OFFSET
  `define WRITE_M6_SETUP_CMD_BIT        `WRITE_M6_SETUP_CMD       + `CONTROL_CMD_OFFSET
  `define WRITE_M7_SETUP_CMD_BIT        `WRITE_M7_SETUP_CMD       + `CONTROL_CMD_OFFSET
  `define WRITE_M8_SETUP_CMD_BIT        `WRITE_M8_SETUP_CMD       + `CONTROL_CMD_OFFSET
  `define WRITE_M9_SETUP_CMD_BIT        `WRITE_M9_SETUP_CMD       + `CONTROL_CMD_OFFSET
  `define WRITE_M10_SETUP_CMD_BIT       `WRITE_M10_SETUP_CMD      + `CONTROL_CMD_OFFSET
  `define WRITE_M11_SETUP_CMD_BIT       `WRITE_M11_SETUP_CMD      + `CONTROL_CMD_OFFSET
  `define WRITE_M12_SETUP_CMD_BIT       `WRITE_M12_SETUP_CMD      + `CONTROL_CMD_OFFSET
  `define WRITE_M13_SETUP_CMD_BIT       `WRITE_M13_SETUP_CMD      + `CONTROL_CMD_OFFSET
  `define WRITE_M14_SETUP_CMD_BIT       `WRITE_M14_SETUP_CMD      + `CONTROL_CMD_OFFSET
  `define WRITE_M15_SETUP_CMD_BIT       `WRITE_M15_SETUP_CMD      + `CONTROL_CMD_OFFSET

  //--
  //-- Delay of data due to trigger delay
  //--
  `define ILA_PRO_DATA_DELAY         9
  //--constant ILA_PRO_DATA_DELAY : integer := 8;

  //-- Width of vector used to encode each Trigger Width value (see ila_core)
  `define GC_MAX_NUM_MU              1024
  `define GC_TRIG_WIDTH_VEC_W        16
  `define GC_TRIG_WIDTH_VEC_ARRAY_W  `GC_TRIG_WIDTH_VEC_W*`GC_MAX_NUM_MU
  `define GC_TRIG_TYPEID_VEC_W       16
  `define GC_TRIG_TYPEID_VEC_ARRAY_W `GC_TRIG_TYPEID_VEC_W*`GC_MAX_NUM_MU
  `define GC_MU_CNT_VEC_W            4
  `define GC_MU_CNT_VEC_ARRAY_W      `GC_MU_CNT_VEC_W*`GC_MAX_NUM_MU

  //-- Width of vector used to encode each Trigger Width value (see ila_core)  
  `define GC_TRIG_TYPE_ID_W        15

  
  //-- Static Status Width
  `define GC_STATIC_STAT_W           672
  

