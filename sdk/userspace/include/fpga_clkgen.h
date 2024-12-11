/*
 * Copyright 2015-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may
 * not use this file except in compliance with the License. A copy of the
 * License is located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

/**
 * The fpga_clkgen library contains helper functions for interacting with AWS_CLK_GEN IP in the design.
 * It can be used as is or as an example for implementing
 * your own interfaces to your drivers, optimized for your own application.
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

//
// AWS_CLK_GEN PF/BAR
//
static const int AWS_CLKGEN_PF  = 1;
static const int AWS_CLKGEN_BAR = 4;

//
// AWS_CLK_GEN Expected Reg Values
//
#define AWS_CLKGEN_ID   0x90481D0F
#define AWS_CLKGEN_VER  0x02010000
#define AWS_CLKGEN_BLD  0x09232223
#define AWS_CLKGEN_LOCK 0x151

#define FPGA_CLKGEN_GROUP_CLKS_MAX    3

#define CLKGEN_A_1_MAX 125
#define CLKGEN_A_2_MAX 375
#define CLKGEN_A_3_MAX 500
#define CLKGEN_B_0_MAX 450
#define CLKGEN_B_1_MAX 225
#define CLKGEN_C_0_MAX 300
#define CLKGEN_C_1_MAX 400
#define CLKGEN_HBM_MAX 450

struct fpga_clkgen_group {
  double clocks[FPGA_CLKGEN_GROUP_CLKS_MAX];
};

struct fpga_clkgen_info {
  /** FPGA clock metrics */
  struct fpga_clkgen_group clock_group_a;
  struct fpga_clkgen_group clock_group_b;
  struct fpga_clkgen_group clock_group_c;
  struct fpga_clkgen_group clock_group_hbm;
};

struct clkgen_recipe {
  uint32_t mult;
  uint32_t mult_frac;
  uint32_t div;
  uint32_t div0;
  uint32_t div0_frac;
  uint32_t div1;
  uint32_t div2;
};

//============================================================================================================
//
// aws_clkgen_get_dynamic() : Dynamically change clock frequency for all MMCMs in AWS_CLK_GEN
// arguements:
// -----------
// int slot_id                    : PCIe slot id value for FPGA card
// struct fpga_clkgen_info* info  : struct with clkgen group frequencies
//
//=============================================================================================================
int aws_clkgen_get_dynamic(int slot_id, struct fpga_clkgen_info* info);

//============================================================================================================
//
// aws_clkgen_recipe() : Set a clock frequency recipe for all MMCMs in AWS_CLK_GEN
// arguements:
// -----------
// int slot_id            : PCIe slot id value for FPGA card
// uint32_t recipe_a      : Recipe for frequencies to set to all clks on MMCM_A in AWS_CLK_GEN
// uint32_t recipe_b      : Recipe for frequencies to set to all clks on MMCM_B in AWS_CLK_GEN
// uint32_t recipe_c      : Recipe for frequencies to set to all clks on MMCM_C in AWS_CLK_GEN
// uint32_t recipe_hbm    : Recipe for frequencies to set to all clks on MMCM_HBM in AWS_CLK_GEN
// uint32_t reset         : Reset to default MMCM frequency
//
//=============================================================================================================
int aws_clkgen_set_recipe(int slot_id, uint32_t clk_a_recipe, uint32_t clk_b_recipe, uint32_t clk_c_recipe, uint32_t clk_hbm_recipe, uint32_t reset);

//============================================================================================================
//
// aws_clkgen_recipe() : Dynamically set clock frequency for all MMCMs in AWS_CLK_GEN
// arguements:
// -----------
// int slot_id            : PCIe slot id value for FPGA card
// uint32_t freq_clk_a    : Frequency of clk_extra_a1 from MMCM_A in AWS_CLK_GEN
// uint32_t freq_clk_b    : Frequency of clk_extra_b0 from MMCM_B in AWS_CLK_GEN
// uint32_t freq_clk_c    : Frequency of clk_extra_c0 from MMCM_C in AWS_CLK_GEN
// uint32_t freq_clk_hbm  : Frequency of clk_hbm_axi  from MMCM_HBM in AWS_CLK_GEN
// uint32_t reset         : Reset to default MMCM frequency
//
//=============================================================================================================
int aws_clkgen_set_dynamic(int slot_id, uint32_t clk_a_freq, uint32_t clk_b_freq, uint32_t clk_c_freq, uint32_t clk_hbm_freq, uint32_t reset);

#ifdef __cplusplus
}
#endif
