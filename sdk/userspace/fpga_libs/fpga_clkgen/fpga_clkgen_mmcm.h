/*
 * Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#pragma once

#include <fpga_pci.h>

//
// AWS_CLK_GEN API specific macros
//
#ifndef MAX_CLKGEN_LOOP_RETRIES
#define MAX_CLKGEN_LOOP_RETRIES (1000000)
#endif

#ifndef AWS_CLKGEN_DEBUG_LEVEL
#define AWS_CLKGEN_DEBUG_LEVEL (0)
#endif

#define FPGA_CLKGEN_GROUP_A_CLKS      3
#define FPGA_CLKGEN_GROUP_B_CLKS      2
#define FPGA_CLKGEN_GROUP_C_CLKS      2
#define FPGA_CLKGEN_GROUP_HBM_CLKS    1

//
// MMCM Base address in AWS_CLK_GEN IP
//
#define AWS_CLKGEN_BASE_B   ((uint64_t) 0x50000)
#define AWS_CLKGEN_BASE_C   ((uint64_t) 0x51000)
#define AWS_CLKGEN_BASE_A   ((uint64_t) 0x52000)
#define AWS_CLKGEN_BASE_HBM ((uint64_t) 0x54000)
#define AWS_CLKGEN_BASE_REG ((uint64_t) 0x58000)

// Expected values
#define MMCM_STATUS_LOCKED 0x1 // Status locked = bit[0]

//
// MMCM Regs address used by AWS_CLK_GEN
//
#define MMCM_STATUS_REG    ((uint64_t) 0x04)
#define MMCM_MAIN_CFG_REG  ((uint64_t) 0x200) // Main clock multiplier/dividers
#define MMCM_CLK0_CFG_REG  ((uint64_t) 0x208) // clk0 dividers
#define MMCM_CLK1_CFG_REG  ((uint64_t) 0x214) // clk1 divider
#define MMCM_CLK2_CFG_REG  ((uint64_t) 0x220) // clk2 divider
#define MMCM_LOAD_CFG_REG  ((uint64_t) 0x25C) // LOAD/SEN register

//
// AWS_CLK_GEN Specific Regs
//
#define AWS_CLKGEN_ID_REG     ((uint64_t)(AWS_CLKGEN_BASE_REG + 0x0))
#define AWS_CLKGEN_VER_REG    ((uint64_t)(AWS_CLKGEN_BASE_REG + 0x4))
#define AWS_CLKGEN_BLD_REG    ((uint64_t)(AWS_CLKGEN_BASE_REG + 0x8))
#define AWS_CLKGEN_CLKS_AVAIL ((uint64_t)(AWS_CLKGEN_BASE_REG + 0xC))
#define AWS_CLKGEN_GRST_REG   ((uint64_t)(AWS_CLKGEN_BASE_REG + 0x10))
#define AWS_CLKGEN_SYSRST_REG ((uint64_t)(AWS_CLKGEN_BASE_REG + 0x14))
#define AWS_CLKGEN_LOCK_REG   ((uint64_t)(AWS_CLKGEN_BASE_REG + 0x20))

#define MAX_CLKS_IN_MMCM 3

struct fpga_clkgen_mmcm {
    uint64_t mmcm_base_offset;
    uint64_t clk_cfg_regs[MAX_CLKS_IN_MMCM];
    pci_bar_handle_t handle;
    uint32_t lock_bit;
    uint32_t avail_bit_start;
    uint32_t num_clocks;
    uint32_t clk_avails[MAX_CLKS_IN_MMCM];
    bool clk_div_has_frac[MAX_CLKS_IN_MMCM];
};

enum fpga_clkgen_mmcm_group {
    clkgen_group_a,
    clkgen_group_b,
    clkgen_group_c,
    clkgen_group_hbm
};

int mmcm_init(enum fpga_clkgen_mmcm_group group, pci_bar_handle_t handle);
int mmcm_clk_avail(enum fpga_clkgen_mmcm_group group, uint32_t clk_index, bool* is_avail);
int mmcm_is_locked(enum fpga_clkgen_mmcm_group group, bool* is_locked);
int mmcm_wait_for_locked(enum fpga_clkgen_mmcm_group group);
int mmcm_set_shared_clock(enum fpga_clkgen_mmcm_group group, uint32_t mult, uint32_t mult_frac, uint32_t div);
int mmcm_get_shared_clock(enum fpga_clkgen_mmcm_group group, uint32_t* mult, uint32_t* mult_frac, uint32_t* div);
int mmcm_set_clk_div(enum fpga_clkgen_mmcm_group group, uint32_t clk_index, uint32_t div, uint32_t div_frac);
int mmcm_get_clk_div(enum fpga_clkgen_mmcm_group group, uint32_t clk_index, uint32_t* div, uint32_t* div_frac);
int mmcm_load_cfg(enum fpga_clkgen_mmcm_group group, uint32_t reset);
