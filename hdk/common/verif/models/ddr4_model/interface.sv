// (c) Copyright 2023 Advanced Micro Devices, Inc. All rights reserved.
`ifndef DDR4_INT_DEF
`define DDR4_INT_DEF
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
interface DDR4_if #(parameter CONFIGURED_DQ_BITS = 8) ();
    timeunit 1ps;
    timeprecision 1ps;
    import arch_package::*;
    parameter CONFIGURED_DQS_BITS = (16 == CONFIGURED_DQ_BITS) ? 2 : 1;
    parameter CONFIGURED_DM_BITS = (16 == CONFIGURED_DQ_BITS) ? 2 : 1;
    logic[1:0] CK; // CK[0]==CK_c CK[1]==CK_t
    logic ACT_n;
    logic RAS_n_A16;
    logic CAS_n_A15;
    logic WE_n_A14;
    logic ALERT_n;
    logic PARITY;
    logic RESET_n;
    logic TEN;
    logic CS_n;
    logic CKE;
    logic ODT;
    logic[MAX_RANK_BITS-1:0] C;
    logic[MAX_BANK_GROUP_BITS-1:0] BG;
    logic[MAX_BANK_BITS-1:0] BA;
    logic[13:0] ADDR;
    logic ADDR_17;
    wire[CONFIGURED_DM_BITS-1:0] DM_n;
    wire[CONFIGURED_DQ_BITS-1:0] DQ;
    wire[CONFIGURED_DQS_BITS-1:0] DQS_t;
    wire[CONFIGURED_DQS_BITS-1:0] DQS_c;
    logic ZQ;
    logic PWR;
    logic VREF_CA;
    logic VREF_DQ;
endinterface

`endif
