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

#include "fpga_clkgen_mmcm.h"
#include <utils/log.h>
#include <hal/fpga_common.h>

static struct fpga_clkgen_mmcm_private {
    struct fpga_clkgen_mmcm group_a;
    struct fpga_clkgen_mmcm group_b;
    struct fpga_clkgen_mmcm group_c;
    struct fpga_clkgen_mmcm group_hbm;
} private;

static struct fpga_clkgen_mmcm* get_mmcm(enum fpga_clkgen_mmcm_group group) {
    struct fpga_clkgen_mmcm* mmcm_ptr = NULL;
    switch (group) {
        case clkgen_group_a:
            mmcm_ptr = &private.group_a;
            break;
        case clkgen_group_b:
             mmcm_ptr = &private.group_b;
             break;
        case clkgen_group_c:
             mmcm_ptr = &private.group_c;
             break;
        case clkgen_group_hbm:
             mmcm_ptr = &private.group_hbm;
             break;
    }
    return mmcm_ptr;
}

// Ensure clkgen ip is part of the image before calling mmcm_init.
int mmcm_init(enum fpga_clkgen_mmcm_group group, pci_bar_handle_t handle) {
    int rc = 0;
    struct fpga_clkgen_mmcm* mmcm = get_mmcm(group);
    fail_on_with_code(mmcm == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "mmcm invalid pointer");

    mmcm->handle = handle;

    switch (group) {
        case clkgen_group_a: {
            mmcm->mmcm_base_offset = AWS_CLKGEN_BASE_A;
            mmcm->avail_bit_start = 1;
            mmcm->num_clocks = 3;
            mmcm->lock_bit = 0;
            break;
        }
        case clkgen_group_b: {
            mmcm->mmcm_base_offset = AWS_CLKGEN_BASE_B;
            mmcm->avail_bit_start = 4;
            mmcm->num_clocks = 2;
            mmcm->lock_bit = 4;
            break;
        }
        case clkgen_group_c: {
            mmcm->mmcm_base_offset = AWS_CLKGEN_BASE_C;
            mmcm->avail_bit_start = 6;
            mmcm->num_clocks = 2;
            mmcm->lock_bit = 6;
            break;
        }
        case clkgen_group_hbm: {
            mmcm->mmcm_base_offset = AWS_CLKGEN_BASE_HBM;
            mmcm->avail_bit_start = 8;
            mmcm->num_clocks = 1;
            mmcm->lock_bit = 8;
            break;
        }
        default:
            fail_on_with_code(mmcm == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "unexpected mmcm group");
    }

    uint64_t clks_avail_offset = AWS_CLKGEN_CLKS_AVAIL;
    uint32_t clks_avail_value = 0;
    rc = fpga_pci_peek(handle, clks_avail_offset, &clks_avail_value);
    fail_on(rc, out, "Unable to read AWS_CLKGEN_CLKS_AVAIL");

    uint64_t clk_cfg_regs[] = {MMCM_CLK0_CFG_REG, MMCM_CLK1_CFG_REG, MMCM_CLK2_CFG_REG};
    bool clk_div_has_frac[] = {true, false, false};

    uint32_t clks_avail_shifted = clks_avail_value >> mmcm->avail_bit_start;
    for (uint32_t i = 0; i < mmcm->num_clocks; ++i) {
        uint32_t clock_avail_mask = 1 << i;
        mmcm->clk_avails[i] = clks_avail_shifted & clock_avail_mask;
        mmcm->clk_cfg_regs[i] = clk_cfg_regs[i];
        mmcm->clk_div_has_frac[i] = clk_div_has_frac[i];
    }

out:
    return rc;
}

int mmcm_clk_avail(enum fpga_clkgen_mmcm_group group, uint32_t clk_index, bool* is_avail) {
    int rc = 0;
    struct fpga_clkgen_mmcm* mmcm = get_mmcm(group);
    fail_on_with_code(mmcm == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid mmcm pointer");
    fail_on_with_code(clk_index >= mmcm->num_clocks, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid clk_index");
    fail_on_with_code(is_avail == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid is_avail pointer");

    *is_avail = mmcm->clk_avails[clk_index];
out:
    return rc;
}

int mmcm_is_locked(enum fpga_clkgen_mmcm_group group, bool* is_locked) {
    int rc = 0;
    struct fpga_clkgen_mmcm* mmcm = get_mmcm(group);
    fail_on_with_code(mmcm == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid mmcm pointer");
    fail_on_with_code(is_locked == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid is_locked pointer");

    uint64_t status_reg_offset = mmcm->mmcm_base_offset + MMCM_STATUS_REG;
    uint32_t status_reg_value = 0;
    rc = fpga_pci_peek(mmcm->handle, status_reg_offset, &status_reg_value);
    fail_on(rc, out, "Failed to read from register @0x%08lx", status_reg_offset);

    *is_locked = ((status_reg_value & MMCM_STATUS_LOCKED) != 0);
out:
    return rc;
}

int mmcm_wait_for_locked(enum fpga_clkgen_mmcm_group group) {
    int rc = 0;
    struct fpga_clkgen_mmcm* mmcm = get_mmcm(group);
    fail_on_with_code(mmcm == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid mmcm pointer");
    int loop_count = 0;

    uint64_t status_reg_offset = mmcm->mmcm_base_offset + MMCM_STATUS_REG;
    uint32_t status_reg_value = 0;
    do {
        rc = fpga_pci_peek(mmcm->handle, status_reg_offset, &status_reg_value);
        fail_on(rc, out, "Failed to read from register @0x%08lx", status_reg_offset);
    } while ((status_reg_value != MMCM_STATUS_LOCKED) && (loop_count < MAX_CLKGEN_LOOP_RETRIES));

    fail_on_with_code(loop_count >= MAX_CLKGEN_LOOP_RETRIES, out, rc, FPGA_ERR_HARDWARE_BUSY, "Timeout: MMCM not locked after %d iterations. MMCM address = 0x%08lx\n", loop_count, status_reg_offset);

out:
    return rc;
}

int mmcm_set_shared_clock(enum fpga_clkgen_mmcm_group group, uint32_t mult, uint32_t mult_frac, uint32_t div) {
    int rc = 0;
    struct fpga_clkgen_mmcm* mmcm = get_mmcm(group);
    fail_on_with_code(mmcm == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid mmcm pointer");

    uint64_t main_cfg_reg_offset = mmcm->mmcm_base_offset + MMCM_MAIN_CFG_REG;
    uint32_t tmp_mult = (mult == 0) ? 1 : mult;
    uint32_t tmp_div  = (div  == 0) ? 1 : div;
    uint32_t main_cfg_reg_value = ((tmp_div << 0) & 0xFF) | ((tmp_mult << 8) & 0xFF00) | ((mult_frac << 16) & 0x0FFF0000);

    rc = fpga_pci_poke(mmcm->handle, main_cfg_reg_offset, main_cfg_reg_value);
    fail_on(rc, out, "Failed to write to register @ 0x%08lx, value = 0x%08x", main_cfg_reg_offset, main_cfg_reg_value);

out:
    return rc;
}


int mmcm_get_shared_clock(enum fpga_clkgen_mmcm_group group, uint32_t* mult, uint32_t* mult_frac, uint32_t* div) {
    int rc = 0;
    struct fpga_clkgen_mmcm* mmcm = get_mmcm(group);
    fail_on_with_code(mmcm == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid mmcm pointer");
    fail_on_with_code(mult == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid mult pointer");
    fail_on_with_code(mult_frac == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid mult_frac pointer");
    fail_on_with_code(div == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid div pointer");

    uint64_t main_cfg_reg_offset = mmcm->mmcm_base_offset + MMCM_MAIN_CFG_REG;
    uint32_t main_cfg_reg_value = 0;
    rc = fpga_pci_peek(mmcm->handle, main_cfg_reg_offset, &main_cfg_reg_value);
    fail_on(rc, out, "Failed to read from register @0x%08lx", main_cfg_reg_offset);

    *mult = (main_cfg_reg_value >> 8) & 0xFF;
    *mult_frac = (main_cfg_reg_value >> 16) & 0x3FF;
    *div = (main_cfg_reg_value >> 0) & 0xFF;

out:
    return rc;
}

int mmcm_set_clk_div(enum fpga_clkgen_mmcm_group group, uint32_t clk_index, uint32_t div, uint32_t div_frac) {
    int rc = 0;
    struct fpga_clkgen_mmcm* mmcm = get_mmcm(group);
    fail_on_with_code(mmcm == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid mmcm pointer");
    fail_on_with_code(clk_index >= mmcm->num_clocks, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid clk_index");

    uint64_t clk_cfg_reg_offset = mmcm->mmcm_base_offset + mmcm->clk_cfg_regs[clk_index];
    uint32_t tmp_div  = (div  == 0) ? 1 : div;
    uint32_t clk_cfg_reg_value = mmcm->clk_div_has_frac[clk_index] ? ((tmp_div << 0) & 0xFF) | ((div_frac << 8) & 0x000FFF00) : ((tmp_div << 0) & 0xFF);
    rc = fpga_pci_poke(mmcm->handle, clk_cfg_reg_offset, clk_cfg_reg_value);
    fail_on(rc, out, "Failed to write to register @ 0x%08lx, value = 0x%08x", clk_cfg_reg_offset, clk_cfg_reg_value);

out:
    return rc;
}

int mmcm_get_clk_div(enum fpga_clkgen_mmcm_group group, uint32_t clk_index, uint32_t* div, uint32_t* div_frac) {
    int rc = 0;
    struct fpga_clkgen_mmcm* mmcm = get_mmcm(group);
    fail_on_with_code(mmcm == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid mmcm pointer");
    fail_on_with_code(clk_index >= mmcm->num_clocks, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid clk_index");
    fail_on_with_code(div == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid div pointer");
    fail_on_with_code(div_frac == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid div_frac pointer");

    uint64_t clk_cfg_reg_offset = mmcm->mmcm_base_offset + mmcm->clk_cfg_regs[clk_index];
    uint32_t clk_cfg_reg_value = 0;
    rc = fpga_pci_peek(mmcm->handle, clk_cfg_reg_offset, &clk_cfg_reg_value);
    fail_on(rc, out, "Failed to read from register @0x%08lx", clk_cfg_reg_offset);

    *div = (clk_cfg_reg_value >> 0) & 0xFF;
    if (mmcm->clk_div_has_frac[clk_index]) {
        *div_frac = (clk_cfg_reg_value >> 8) & 0x3FF;
    } else {
        *div_frac = 0;
    }

out:
    return rc;
}

int mmcm_load_cfg(enum fpga_clkgen_mmcm_group group, uint32_t reset) {
    int rc = 0;
    struct fpga_clkgen_mmcm* mmcm = get_mmcm(group);
    fail_on_with_code(mmcm == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "invalid mmcm pointer");

    uint64_t load_cfg_reg_offset  = mmcm->mmcm_base_offset + MMCM_LOAD_CFG_REG;
    uint32_t load_cfg_reg_value = reset ? 0x1 : 0x3;
    rc = fpga_pci_poke(mmcm->handle, load_cfg_reg_offset, load_cfg_reg_value);
    fail_on(rc, out, "Failed to write to register @ 0x%08lx, value = 0x%08x", load_cfg_reg_offset, load_cfg_reg_value);

out:
    return rc;
}
