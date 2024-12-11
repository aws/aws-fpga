/*
 * Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include "utils/log.h"
#include "fpga_clkgen.h"
#include "fpga_clkgen_mmcm.h"

//
// Frequency Table with multiplier and divider values for MMCM, sorted as per increasing frequency order.
//
#define AWS_CLKGEN_TABLE_ROWS 42
#define AWS_CLKGEN_TABLE_COLS 6

static const uint32_t FREQ_TABLE [AWS_CLKGEN_TABLE_ROWS][AWS_CLKGEN_TABLE_COLS] = {
  /*idx=0 */ {/*freq*/  87, /*sharedMult*/   8,  /*sharedDiv*/  1, /*sharedMultFrac*/ 750, /*div0*/ 10, /*div0Frac*/   0},
  /*idx=1 */ {/*freq*/  97, /*sharedMult*/   9,  /*sharedDiv*/  1, /*sharedMultFrac*/ 750, /*div0*/ 10, /*div0Frac*/   0},
  /*idx=2 */ {/*freq*/ 100, /*sharedMult*/  12,  /*sharedDiv*/  1, /*sharedMultFrac*/   0, /*div0*/ 12, /*div0Frac*/   0},
  /*idx=3 */ {/*freq*/ 109, /*sharedMult*/  10,  /*sharedDiv*/  1, /*sharedMultFrac*/ 875, /*div0*/ 10, /*div0Frac*/   0},
  /*idx=4 */ {/*freq*/ 125, /*sharedMult*/  11,  /*sharedDiv*/  1, /*sharedMultFrac*/ 875, /*div0*/  9, /*div0Frac*/ 500},
  /*idx=5 */ {/*freq*/ 136, /*sharedMult*/  13,  /*sharedDiv*/  1, /*sharedMultFrac*/ 625, /*div0*/ 10, /*div0Frac*/   0},
  /*idx=6 */ {/*freq*/ 150, /*sharedMult*/  12,  /*sharedDiv*/  1, /*sharedMultFrac*/   0, /*div0*/  8, /*div0Frac*/   0},
  /*idx=7 */ {/*freq*/ 156, /*sharedMult*/  15,  /*sharedDiv*/  1, /*sharedMultFrac*/ 625, /*div0*/ 10, /*div0Frac*/   0},
  /*idx=8 */ {/*freq*/ 166, /*sharedMult*/  16,  /*sharedDiv*/  1, /*sharedMultFrac*/ 625, /*div0*/ 10, /*div0Frac*/   0},
  /*idx=9 */ {/*freq*/ 171, /*sharedMult*/  17,  /*sharedDiv*/  1, /*sharedMultFrac*/ 125, /*div0*/ 10, /*div0Frac*/   0},
  /*idx=10*/ {/*freq*/ 177, /*sharedMult*/  17,  /*sharedDiv*/  1, /*sharedMultFrac*/ 750, /*div0*/ 10, /*div0Frac*/   0},
  /*idx=11*/ {/*freq*/ 182, /*sharedMult*/  18,  /*sharedDiv*/  1, /*sharedMultFrac*/ 250, /*div0*/ 10, /*div0Frac*/   0},
  /*idx=12*/ {/*freq*/ 187, /*sharedMult*/  18,  /*sharedDiv*/  1, /*sharedMultFrac*/ 750, /*div0*/ 10, /*div0Frac*/   0},
  /*idx=13*/ {/*freq*/ 196, /*sharedMult*/  19,  /*sharedDiv*/  1, /*sharedMultFrac*/ 625, /*div0*/ 10, /*div0Frac*/   0},
  /*idx=14*/ {/*freq*/ 200, /*sharedMult*/  12,  /*sharedDiv*/  1, /*sharedMultFrac*/   0, /*div0*/  6, /*div0Frac*/   0},
  /*idx=15*/ {/*freq*/ 218, /*sharedMult*/  21,  /*sharedDiv*/  1, /*sharedMultFrac*/ 750, /*div0*/ 10, /*div0Frac*/   0},
  /*idx=16*/ {/*freq*/ 227, /*sharedMult*/  22,  /*sharedDiv*/  1, /*sharedMultFrac*/ 750, /*div0*/ 10, /*div0Frac*/   0},
  /*idx=17*/ {/*freq*/ 250, /*sharedMult*/  11,  /*sharedDiv*/  1, /*sharedMultFrac*/ 875, /*div0*/  4, /*div0Frac*/ 750},
  /*idx=18*/ {/*freq*/ 265, /*sharedMult*/  26,  /*sharedDiv*/  2, /*sharedMultFrac*/ 500, /*div0*/  5, /*div0Frac*/   0},
  /*idx=19*/ {/*freq*/ 266, /*sharedMult*/   8,  /*sharedDiv*/  1, /*sharedMultFrac*/   0, /*div0*/  3, /*div0Frac*/   0},
  /*idx=20*/ {/*freq*/ 273, /*sharedMult*/  27,  /*sharedDiv*/  2, /*sharedMultFrac*/ 250, /*div0*/  5, /*div0Frac*/   0},
  /*idx=21*/ {/*freq*/ 291, /*sharedMult*/  29,  /*sharedDiv*/  2, /*sharedMultFrac*/   0, /*div0*/  5, /*div0Frac*/   0},
  /*idx=22*/ {/*freq*/ 300, /*sharedMult*/  12,  /*sharedDiv*/  1, /*sharedMultFrac*/   0, /*div0*/  4, /*div0Frac*/   0},
  /*idx=23*/ {/*freq*/ 318, /*sharedMult*/  31,  /*sharedDiv*/  2, /*sharedMultFrac*/ 750, /*div0*/  5, /*div0Frac*/   0},
  /*idx=24*/ {/*freq*/ 333, /*sharedMult*/  10,  /*sharedDiv*/  1, /*sharedMultFrac*/   0, /*div0*/  3, /*div0Frac*/   0},
  /*idx=25*/ {/*freq*/ 343, /*sharedMult*/  34,  /*sharedDiv*/  4, /*sharedMultFrac*/ 250, /*div0*/  2, /*div0Frac*/ 500},
  /*idx=26*/ {/*freq*/ 364, /*sharedMult*/  36,  /*sharedDiv*/  4, /*sharedMultFrac*/ 750, /*div0*/  2, /*div0Frac*/ 500},
  /*idx=27*/ {/*freq*/ 375, /*sharedMult*/  37,  /*sharedDiv*/  4, /*sharedMultFrac*/ 500, /*div0*/  2, /*div0Frac*/ 500},
  /*idx=28*/ {/*freq*/ 400, /*sharedMult*/  12,  /*sharedDiv*/  1, /*sharedMultFrac*/   0, /*div0*/  3, /*div0Frac*/   0},
  /*idx=29*/ {/*freq*/ 405, /*sharedMult*/  20,  /*sharedDiv*/  1, /*sharedMultFrac*/ 250, /*div0*/  5, /*div0Frac*/   0},
  /*idx=30*/ {/*freq*/ 410, /*sharedMult*/  20,  /*sharedDiv*/  1, /*sharedMultFrac*/ 500, /*div0*/  5, /*div0Frac*/   0},
  /*idx=31*/ {/*freq*/ 415, /*sharedMult*/  20,  /*sharedDiv*/  1, /*sharedMultFrac*/ 750, /*div0*/  5, /*div0Frac*/   0},
  /*idx=32*/ {/*freq*/ 420, /*sharedMult*/  21,  /*sharedDiv*/  1, /*sharedMultFrac*/   0, /*div0*/  5, /*div0Frac*/   0},
  /*idx=33*/ {/*freq*/ 425, /*sharedMult*/  21,  /*sharedDiv*/  1, /*sharedMultFrac*/ 250, /*div0*/  5, /*div0Frac*/   0},
  /*idx=34*/ {/*freq*/ 430, /*sharedMult*/  21,  /*sharedDiv*/  1, /*sharedMultFrac*/ 500, /*div0*/  5, /*div0Frac*/   0},
  /*idx=35*/ {/*freq*/ 435, /*sharedMult*/  21,  /*sharedDiv*/  1, /*sharedMultFrac*/ 750, /*div0*/  5, /*div0Frac*/   0},
  /*idx=36*/ {/*freq*/ 437, /*sharedMult*/  43,  /*sharedDiv*/  4, /*sharedMultFrac*/ 625, /*div0*/  2, /*div0Frac*/ 500},
  /*idx=37*/ {/*freq*/ 440, /*sharedMult*/  22,  /*sharedDiv*/  1, /*sharedMultFrac*/   0, /*div0*/  5, /*div0Frac*/   0},
  /*idx=38*/ {/*freq*/ 445, /*sharedMult*/  22,  /*sharedDiv*/  1, /*sharedMultFrac*/ 250, /*div0*/  5, /*div0Frac*/   0},
  /*idx=39*/ {/*freq*/ 450, /*sharedMult*/  11,  /*sharedDiv*/  1, /*sharedMultFrac*/ 250, /*div0*/  2, /*div0Frac*/ 500},
  /*idx=40*/ {/*freq*/ 458, /*sharedMult*/  45,  /*sharedDiv*/  4, /*sharedMultFrac*/ 750, /*div0*/  2, /*div0Frac*/ 500},
  /*idx=41*/ {/*freq*/ 500, /*sharedMult*/  15,  /*sharedDiv*/  1, /*sharedMultFrac*/   0, /*div0*/  3, /*div0Frac*/   0},
};

#define CLKGEN_A_RECIPE_TABLE_ROWS 3

static const struct clkgen_recipe clkgen_a_recipes[CLKGEN_A_RECIPE_TABLE_ROWS] = {
  {/*index 0*/ /*mult*/ 15, /*mult_frac*/   0, /*div*/ 1, /*div0*/ 24, /*div0_frac*/ 0, /*div1*/  8, /*div2*/ 6},
  {/*index 1*/ /*mult*/ 15, /*mult_frac*/   0, /*div*/ 1, /*div0*/ 12, /*div0_frac*/ 0, /*div1*/  4, /*div2*/ 3},
  {/*index 2*/ /*mult*/ 12, /*mult_frac*/ 500, /*div*/ 1, /*div0*/ 80, /*div0_frac*/ 0, /*div1*/ 10, /*div2*/ 20}
};

#define CLKGEN_B_RECIPE_TABLE_ROWS 6

static const struct clkgen_recipe clkgen_b_recipes[CLKGEN_B_RECIPE_TABLE_ROWS] = {
  {/*index 0*/ /*mult*/ 12, /*mult_frac*/ 500, /*div*/ 1, /*div0*/ 5, /*div0_frac*/   0, /*div1*/ 10, /*div2*/ 1},
  {/*index 1*/ /*mult*/ 11, /*mult_frac*/ 875, /*div*/ 1, /*div0*/ 9, /*div0_frac*/ 500, /*div1*/ 19, /*div2*/ 1},
  {/*index 2*/ /*mult*/ 11, /*mult_frac*/ 250, /*div*/ 1, /*div0*/ 2, /*div0_frac*/ 500, /*div1*/  5, /*div2*/ 1},
  {/*index 3*/ /*mult*/ 11, /*mult_frac*/ 875, /*div*/ 1, /*div0*/ 4, /*div0_frac*/ 750, /*div1*/ 19, /*div2*/ 1},
  {/*index 4*/ /*mult*/ 12, /*mult_frac*/   0, /*div*/ 1, /*div0*/ 4, /*div0_frac*/   0, /*div1*/ 16, /*div2*/ 1},
  {/*index 5*/ /*mult*/ 12, /*mult_frac*/   0, /*div*/ 1, /*div0*/ 3, /*div0_frac*/   0, /*div1*/ 12, /*div2*/ 1}
};

#define CLKGEN_C_RECIPE_TABLE_ROWS 4

static const struct clkgen_recipe clkgen_c_recipes[CLKGEN_C_RECIPE_TABLE_ROWS] = {
  {/*index 0*/ /*mult*/ 12, /*mult_frac*/ 0, /*div*/ 1, /*div0*/  4, /*div0_frac*/ 0, /*div1*/  3, /*div2*/ 1},
  {/*index 1*/ /*mult*/ 12, /*mult_frac*/ 0, /*div*/ 1, /*div0*/  8, /*div0_frac*/ 0, /*div1*/  6, /*div2*/ 1},
  {/*index 2*/ /*mult*/ 12, /*mult_frac*/ 0, /*div*/ 1, /*div0*/ 16, /*div0_frac*/ 0, /*div1*/ 12, /*div2*/ 1},
  {/*index 3*/ /*mult*/  8, /*mult_frac*/ 0, /*div*/ 1, /*div0*/  4, /*div0_frac*/ 0, /*div1*/  3, /*div2*/ 1}
};

#define CLKGEN_HBM_RECIPE_TABLE_ROWS 5

static const struct clkgen_recipe clkgen_hbm_recipes[CLKGEN_HBM_RECIPE_TABLE_ROWS] = {
  {/*index 0*/ /*mult*/ 12, /*mult_frac*/ 500, /*div*/ 1, /*div0*/ 5, /*div0_frac*/   0, /*div1*/ 1, /*div2*/ 1},
  {/*index 1*/ /*mult*/ 11, /*mult_frac*/ 875, /*div*/ 1, /*div0*/ 9, /*div0_frac*/ 500, /*div1*/ 1, /*div2*/ 1},
  {/*index 2*/ /*mult*/ 11, /*mult_frac*/ 250, /*div*/ 1, /*div0*/ 2, /*div0_frac*/ 500, /*div1*/ 1, /*div2*/ 1},
  {/*index 3*/ /*mult*/ 12, /*mult_frac*/   0, /*div*/ 1, /*div0*/ 4, /*div0_frac*/   0, /*div1*/ 1, /*div2*/ 1},
  {/*index 4*/ /*mult*/ 12, /*mult_frac*/   0, /*div*/ 1, /*div0*/ 3, /*div0_frac*/   0, /*div1*/ 1, /*div2*/ 1}
};

static int aws_clkgen_mmcm_init(pci_bar_handle_t pci_bar_handle) {
    int rc = 0;

    rc = mmcm_init(clkgen_group_a, pci_bar_handle);
    fail_on(rc, out, "ERROR: Failed to mmcm_init\n");

    rc = mmcm_init(clkgen_group_b, pci_bar_handle);
    fail_on(rc, out, "ERROR: Failed to mmcm_init\n");

    rc = mmcm_init(clkgen_group_c, pci_bar_handle);
    fail_on(rc, out, "ERROR: Failed to mmcm_init\n");

    rc = mmcm_init(clkgen_group_hbm, pci_bar_handle);
    fail_on(rc, out, "ERROR: Failed to mmcm_init\n");

out:
    return rc;
}

static int aws_clkgen_get_freq(enum fpga_clkgen_mmcm_group group, double* cfg_freq, uint32_t num_clocks) {

    int rc = 0;
    fail_on_with_code(cfg_freq == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "cfg_freq invalid pointer");
    fail_on_with_code(num_clocks < 1, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "num_clocks less than 1");
    fail_on_with_code(num_clocks > FPGA_CLKGEN_GROUP_CLKS_MAX, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "num_clocks greater than FPGA_CLKGEN_GROUP_CLKS_MAX");

    uint32_t mult = 0;
    uint32_t mult_frac = 0;
    uint32_t div = 0;

    rc = mmcm_get_shared_clock(group, &mult, &mult_frac, &div);
    fail_on(rc, out, "ERROR: Failed to mmcm_get_shared_clock");

    double shared_group_freq = 100.0; // start with the 100 MHz reference clock
    double global_multiplier = mult + (double)mult_frac / 1000;
    shared_group_freq *= global_multiplier;
    shared_group_freq /= div;

    for (uint32_t i = 0; i < num_clocks; ++i) {
      uint32_t clk_cfg_div = 0;
      uint32_t clk_cfg_div_frac = 0;
      rc = mmcm_get_clk_div(group, i, &clk_cfg_div, &clk_cfg_div_frac);
      fail_on(rc, out, "ERROR: Failed to mmcm_get_shared_clock");

      double clock_divider = clk_cfg_div;
      clock_divider += (double)clk_cfg_div_frac / 1000;
      double clock = shared_group_freq / clock_divider;
      *(cfg_freq + i) = clock;
    }

out:
    return rc;
}

static int aws_clkgen_set_mmcm(enum fpga_clkgen_mmcm_group group, const struct clkgen_recipe* recipe, uint32_t reset) {

    int rc = 0;
    fail_on_with_code(recipe == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "recipe invalid pointer");

    uint32_t divs[] = {recipe->div0, recipe->div1, recipe->div2};
    uint32_t div_fracs[] = {recipe->div0_frac, 0, 0};
    const int div_size = sizeof(divs)/sizeof(uint32_t);

    if (!reset) {
      mmcm_set_shared_clock(group, recipe->mult, recipe->mult_frac, recipe->div);
      fail_on(rc, out, "ERROR: Failed to mmcm_set_shared_clock");

      for (int i = 0; i < div_size; ++i) {
        mmcm_set_clk_div(group, i, divs[i], div_fracs[i]);
        fail_on(rc, out, "ERROR: Failed to mmcm_set_clk_div");
      }
    }

    mmcm_wait_for_locked(group);
    fail_on(rc, out, "ERROR: Failed to mmcm_wait_for_locked");

    mmcm_load_cfg(group, reset);
    fail_on(rc, out, "ERROR: Failed to mmcm_load_cfg");

    mmcm_wait_for_locked(group);
    fail_on(rc, out, "ERROR: Failed to mmcm_wait_for_locked");

 out:
    return rc;
}

static int aws_clkgen_set_freq(enum fpga_clkgen_mmcm_group group, uint32_t req_freq, uint32_t reset) {
    int rc = 0;
    fail_on_with_code(!reset && req_freq < FREQ_TABLE[0][0], out, rc, FPGA_ERR_INVALID_CLKGEN_INPUTS, "freq for clock group invalid");

    int idx_choice = 0;

    struct clkgen_recipe recipe;

    // get index of closest match to the target freq from the FREQ_TABLE
    if (!reset) {
      for (int i = AWS_CLKGEN_TABLE_ROWS - 1; i >= 0; --i) {
        if (FREQ_TABLE[i][0] <= req_freq) {
          idx_choice = i;
          break;
        }
      }

      recipe.mult = FREQ_TABLE[idx_choice][1];
      recipe.div = FREQ_TABLE[idx_choice][2];
      recipe.mult_frac = FREQ_TABLE[idx_choice][3];
      recipe.div0 = FREQ_TABLE[idx_choice][4];
      recipe.div0_frac = FREQ_TABLE[idx_choice][5];
      recipe.div1 = 0xF;
      recipe.div2 = 0xF;
    }

    rc = aws_clkgen_set_mmcm (group, &recipe, reset);
    fail_on(rc, out, "ERROR: Failed to aws_clkgen_set_mmcm");

 out:
    return rc;
}

static int aws_clkgen_reset(pci_bar_handle_t pci_bar_handle, uint32_t reset) {

    int rc = 0;

    uint64_t grst_reg_offset = AWS_CLKGEN_GRST_REG;
    uint32_t grst_reg_value = 0;
    rc = fpga_pci_poke(pci_bar_handle, grst_reg_offset, grst_reg_value);
    fail_on(rc, out, "Failed to write to register @ 0x%08lx, value = 0x%08x", grst_reg_offset, grst_reg_value);

    // Wait for MMCM lock if de-asserting resets
    if (!reset) {
      int loop_count = 0;
      uint64_t lock_reg_offset = AWS_CLKGEN_LOCK_REG;
      uint32_t lock_reg_value = 0;
      do {
        rc = fpga_pci_peek(pci_bar_handle, lock_reg_offset, &lock_reg_value);
        fail_on(rc, out, "Failed to read from register @0x%08lx", lock_reg_offset);
        loop_count++;
      } while ((lock_reg_value != AWS_CLKGEN_LOCK) && (loop_count < MAX_CLKGEN_LOOP_RETRIES));

      fail_on((loop_count >= MAX_CLKGEN_LOOP_RETRIES), out, "Timeout: Failed to achieve MMCM lock after %d iterations.", loop_count);
    }

    uint64_t sysrst_reg_offset = AWS_CLKGEN_SYSRST_REG;
    uint32_t sysrst_reg_value = reset ? 0xFFFFFFFF : 0;
    rc = fpga_pci_poke(pci_bar_handle, sysrst_reg_offset, sysrst_reg_value);
    fail_on(rc, out, "Failed to write to register @ 0x%08lx, value = 0x%08x", sysrst_reg_offset, sysrst_reg_value);

out:
    return rc;
}

static int aws_clkgen_check_id(pci_bar_handle_t pci_bar_handle) {

    int rc = 0;

    uint64_t id_reg_offset = AWS_CLKGEN_ID_REG;
    uint32_t id_reg_value = 0;
    rc = fpga_pci_peek(pci_bar_handle, id_reg_offset, &id_reg_value);
    fail_on(rc, out, "Failed to read from register @0x%08lx", id_reg_offset);
    fail_on(rc = (id_reg_value != AWS_CLKGEN_ID), out, "ERROR: ID_REG mismatch.");

    uint64_t ver_reg_offset = AWS_CLKGEN_VER_REG;
    uint32_t ver_reg_value = 0;
    rc = fpga_pci_peek(pci_bar_handle, ver_reg_offset, &ver_reg_value);
    fail_on(rc, out, "Failed to read from register @0x%08lx", ver_reg_offset);
    fail_on(rc = (ver_reg_value != AWS_CLKGEN_VER), out, "ERROR: VER_REG mismatch.");

    uint64_t bld_reg_offset = AWS_CLKGEN_BLD_REG;
    uint32_t bld_reg_value = 0;
    rc = fpga_pci_peek(pci_bar_handle, bld_reg_offset, &bld_reg_value);
    fail_on(rc, out, "Failed to read from register @0x%08lx", bld_reg_offset);
    fail_on(rc = (bld_reg_value != AWS_CLKGEN_BLD), out, "ERROR: BUILD_REG mismatch.");

out:
    return rc;
}

int aws_clkgen_get_dynamic(int slot_id, struct fpga_clkgen_info* info) {

    int rc = 0;
    fail_on_with_code(info == NULL, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "info invalid pointer");

    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
    int fpga_attach_flags = 0;

    // Attach to PCIe PF/BAR
    rc = fpga_pci_attach(slot_id, AWS_CLKGEN_PF, AWS_CLKGEN_BAR, fpga_attach_flags, &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to the AFI on slot id %d", fpga_attach_flags);

    aws_clkgen_mmcm_init(pci_bar_handle);
    fail_on(rc, out, "ERROR: Failed to aws_clkgen_mmcm_init\n");

    rc = aws_clkgen_check_id(pci_bar_handle);
    fail_on_with_code(rc, out, rc, FPGA_ERR_CLKGEN_NOT_FOUND, "aws_clkgen_check_id() check failed.");

    // Configure MMCMs in AWS_CLK_GEN
    rc = aws_clkgen_get_freq(clkgen_group_a, info->clock_group_a.clocks, FPGA_CLKGEN_GROUP_A_CLKS);
    fail_on(rc, out, "aws_clkgen_get_freq(pci_bar_handle, AWS_CLKGEN_BASE_A, freq_clk_a) failed.");

    rc = aws_clkgen_get_freq(clkgen_group_b, info->clock_group_b.clocks, FPGA_CLKGEN_GROUP_B_CLKS);
    fail_on(rc, out, "aws_clkgen_get_freq(pci_bar_handle, AWS_CLKGEN_BASE_B, freq_clk_b) failed.");

    rc = aws_clkgen_get_freq(clkgen_group_c, info->clock_group_c.clocks, FPGA_CLKGEN_GROUP_C_CLKS);
    fail_on(rc, out, "aws_clkgen_get_freq(pci_bar_handle, AWS_CLKGEN_BASE_C, freq_clk_c) failed.");

    rc = aws_clkgen_get_freq(clkgen_group_hbm, info->clock_group_hbm.clocks, FPGA_CLKGEN_GROUP_HBM_CLKS);
    fail_on(rc, out, "aws_clkgen_get_freq(pci_bar_handle, AWS_CLKGEN_BASE_HBM, freq_clk_hbm) failed.");

out:
    if (pci_bar_handle != PCI_BAR_HANDLE_INIT) {
      fpga_pci_detach(pci_bar_handle);
    }
    return rc;
}

int aws_clkgen_set_recipe(int slot_id, uint32_t recipe_a, uint32_t recipe_b, uint32_t recipe_c, uint32_t recipe_hbm, uint32_t reset) {

    int rc = 0;
    if (!reset) {
      fail_on_with_code(recipe_a >= CLKGEN_A_RECIPE_TABLE_ROWS, out, rc, FPGA_ERR_INVALID_CLKGEN_INPUTS, "recipe for clock group a invalid");
      fail_on_with_code(recipe_b >= CLKGEN_B_RECIPE_TABLE_ROWS, out, rc, FPGA_ERR_INVALID_CLKGEN_INPUTS, "recipe for clock group b invalid");
      fail_on_with_code(recipe_c >= CLKGEN_C_RECIPE_TABLE_ROWS, out, rc, FPGA_ERR_INVALID_CLKGEN_INPUTS, "recipe for clock group c invalid");
      fail_on_with_code(recipe_hbm >= CLKGEN_HBM_RECIPE_TABLE_ROWS, out, rc, FPGA_ERR_INVALID_CLKGEN_INPUTS, "recipe for clock group hbm invalid");
    } else {
      recipe_a = recipe_b = recipe_c = recipe_hbm = 0;
    }

    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
    int fpga_attach_flags = 0;

    rc = fpga_pci_attach(slot_id, AWS_CLKGEN_PF, AWS_CLKGEN_BAR, fpga_attach_flags, &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to the AFI on slot id %d", fpga_attach_flags);

    aws_clkgen_mmcm_init(pci_bar_handle);
    fail_on(rc, out, "ERROR: Failed to aws_clkgen_mmcm_init\n");

    rc = aws_clkgen_check_id(pci_bar_handle);
    fail_on_with_code(rc, out, rc, FPGA_ERR_CLKGEN_NOT_FOUND, "aws_clkgen_check_id() check failed.");

    rc = aws_clkgen_reset(pci_bar_handle, 1);
    fail_on(rc, out, "aws_clkgen_reset(1) failed.");

    rc = aws_clkgen_set_mmcm(clkgen_group_a, &clkgen_a_recipes[recipe_a], reset);
    fail_on(rc, out, "aws_clkgen_set_mmcm(clkgen_group_a, ...) failed.");

    rc = aws_clkgen_set_mmcm(clkgen_group_b, &clkgen_b_recipes[recipe_b], reset);
    fail_on(rc, out, "aws_clkgen_set_mmcm(clkgen_group_b, ...) failed.");

    rc = aws_clkgen_set_mmcm(clkgen_group_c, &clkgen_c_recipes[recipe_c], reset);
    fail_on(rc, out, "aws_clkgen_set_mmcm(clkgen_group_c, ...) failed.");

    rc = aws_clkgen_set_mmcm(clkgen_group_hbm, &clkgen_hbm_recipes[recipe_hbm], reset);
    fail_on(rc, out, "aws_clkgen_set_mmcm(clkgen_group_hbm, ...) failed.");

    // De-assert all resets
    rc = aws_clkgen_reset(pci_bar_handle, 0);
    fail_on(rc, out, "aws_clkgen_reset(0) failed.");

out:
    if (pci_bar_handle != PCI_BAR_HANDLE_INIT) {
      fpga_pci_detach(pci_bar_handle);
    }
    return rc;
}

int aws_clkgen_set_dynamic(int slot_id, uint32_t clk_a_freq, uint32_t clk_b_freq, uint32_t clk_c_freq, uint32_t clk_hbm_freq, uint32_t reset) {
    int rc = 0;
    if (!reset) {
      fail_on_with_code(clk_a_freq > CLKGEN_A_1_MAX, out, rc, FPGA_ERR_INVALID_CLKGEN_INPUTS, "frequency for clock group a invalid");
      fail_on_with_code(clk_b_freq > CLKGEN_B_0_MAX, out, rc, FPGA_ERR_INVALID_CLKGEN_INPUTS, "frequency for clock group b invalid");
      fail_on_with_code(clk_c_freq > CLKGEN_C_0_MAX, out, rc, FPGA_ERR_INVALID_CLKGEN_INPUTS, "frequency for clock group c invalid");
      fail_on_with_code(clk_hbm_freq > CLKGEN_HBM_MAX, out, rc, FPGA_ERR_INVALID_CLKGEN_INPUTS, "frequency for clock group hbm invalid");
    } else {
      clk_a_freq = clk_b_freq = clk_c_freq = clk_hbm_freq = 0;
    }

    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
    int fpga_attach_flags = 0;

    // Attach to PCIe PF/BAR
    rc = fpga_pci_attach(slot_id, AWS_CLKGEN_PF, AWS_CLKGEN_BAR, fpga_attach_flags, &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to the AFI on slot id %d", fpga_attach_flags);

    aws_clkgen_mmcm_init(pci_bar_handle);
    fail_on(rc, out, "ERROR: Failed to aws_clkgen_mmcm_init\n");

    rc = aws_clkgen_check_id(pci_bar_handle);
    fail_on_with_code(rc, out, rc, FPGA_ERR_CLKGEN_NOT_FOUND, "aws_clkgen_check_id() check failed.");

    rc = aws_clkgen_reset(pci_bar_handle, 1);
    fail_on(rc, out, "aws_clkgen_reset(1) failed.");

    rc = aws_clkgen_set_freq(clkgen_group_a, clk_a_freq, reset);
    fail_on(rc, out, "aws_clkgen_set_freq(clkgen_group_a, ...) failed.");

    rc = aws_clkgen_set_freq(clkgen_group_b, clk_b_freq, reset);
    fail_on(rc, out, "aws_clkgen_set_freq(clkgen_group_b, ...) failed.");

    rc = aws_clkgen_set_freq(clkgen_group_c, clk_c_freq, reset);
    fail_on(rc, out, "aws_clkgen_set_freq(clkgen_group_c, ...) failed.");

    rc = aws_clkgen_set_freq(clkgen_group_hbm, clk_hbm_freq, reset);
    fail_on(rc, out, "aws_clkgen_set_freq(clkgen_group_hbm, ...) failed.");

    // De-assert all resets
    rc = aws_clkgen_reset(pci_bar_handle, 0);
    fail_on(rc, out, "aws_clkgen_reset(0) failed.");

out:
    if (pci_bar_handle != PCI_BAR_HANDLE_INIT) {
      fpga_pci_detach(pci_bar_handle);
    }
    return rc;
}
