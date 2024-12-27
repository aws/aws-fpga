// ============================================================================
// Amazon FPGA Hardware Development Kit
//
// Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
//
//    http://aws.amazon.com/asl/
//
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.
// ============================================================================


//--------------------------------------------------------------------------------------
// Measure frequency of clocks from AWS_CLK_GEN IP
// NOTE: Works only on cl_dram_hbm_dma bitstreams
//--------------------------------------------------------------------------------------

#include <stdio.h>
#include <fcntl.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <poll.h>

#include "fpga_pci.h"
#include "fpga_mgmt.h"
#include "fpga_dma.h"
#include "utils/lcd.h"

#include "test_dram_dma_common.h"

#define MAX_LOOP_COUNT       (1000000)

/* use the standard out logger */
static const struct logger *logger = &logger_stdout;

//
// CL_CLK_FREQ measurement regs
//
#define OCL_OFFSET   ((uint64_t) 0x600)
#define CTL_REG      ((uint64_t)(OCL_OFFSET + 0x00))
#define REF_FREQ_CTR ((uint64_t)(OCL_OFFSET + 0x04))
#define FREQ_CTR_0   ((uint64_t)(OCL_OFFSET + 0x10))
#define FREQ_CTR_1   ((uint64_t)(OCL_OFFSET + 0x14))
#define FREQ_CTR_2   ((uint64_t)(OCL_OFFSET + 0x18))
#define FREQ_CTR_3   ((uint64_t)(OCL_OFFSET + 0x1C))
#define FREQ_CTR_4   ((uint64_t)(OCL_OFFSET + 0x20))
#define FREQ_CTR_5   ((uint64_t)(OCL_OFFSET + 0x24))
#define FREQ_CTR_6   ((uint64_t)(OCL_OFFSET + 0x28))
#define FREQ_CTR_7   ((uint64_t)(OCL_OFFSET + 0x2C))
#define FREQ_CTR_8   ((uint64_t)(OCL_OFFSET + 0x30))
#define FREQ_CTR_9   ((uint64_t)(OCL_OFFSET + 0x34))

// Function declarations
void usage(const char* program_name);
int measure_clk_freq(int slot_id);
int display_results(int slot_id);

//=================================================================
//
// MAIN
//
//=================================================================
int main(int argc, char **argv) {
    int rc;
    int slot_id = 0;

    switch (argc) {
    case 1:
      break;
    case 3:
      sscanf(argv[2], "%x", &slot_id);
      break;
    default:
      usage(argv[0]);
      return 1;
    }

    // setup logging to print to stdout
    rc = log_init("test_aws_clk_gen");
    fail_on(rc, out, "Unable to initialize the log.");
    rc = log_attach(logger, NULL, 0);
    fail_on(rc, out, "%s", "Unable to attach to the log.");

    // initialize the fpga_plat library
    rc = fpga_mgmt_init();
    fail_on(rc, out, "Unable to initialize the fpga_mgmt library");

    //
    // Display Test Variables
    //
    printf("===================================================\n");
    printf("Running test_aws_clk_gen \n");
    printf("===================================================\n");
    printf("slot_id     = %d\n", slot_id);
    printf("===================================================\n");

    //=============================================================
    // Run the test
    //=============================================================
    rc = deassert_clk_resets(slot_id);
    fail_on(rc, out, "Failed deassert_clk_resets()");

    rc = measure_clk_freq(slot_id);
    fail_on(rc, out, "measure_clk_freq()");

    rc = display_results(slot_id);
    fail_on(rc, out, "Failed display_results()");

out:
    log_info("TEST %s", (rc == 0) ? "PASSED" : "FAILED");
    return rc;
}


//=============================================================
//
// usage()
//
//=============================================================
void usage(const char* program_name) {
    printf("usage: %s [--slot <slot>]\n", program_name);
}


//=============================================================
//
// measure_clk_freq()
//
//=============================================================
int measure_clk_freq(int slot_id) {
    int rc;
    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
    int fpga_attach_flags = 0;
    int loop_count = 0;
    uint64_t addr  = 0;
    uint32_t wdata = 0;
    uint32_t read_data = 0;
    uint32_t expected_value = 0;

    // Config space is on PF0-BAR0
    int pf_id  = 0;
    int bar_id = 0;

    printf("__INFO__: measure_clk_freq()\n");
    rc = fpga_pci_attach(slot_id, pf_id, bar_id, fpga_attach_flags, &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to the AFI on slot id %d", slot_id);

    //
    // Reset all freq counters
    //
    addr = CTL_REG;
    wdata = 0x80000000;
    rc = fpga_pci_poke(pci_bar_handle, addr, wdata);
    fail_on(rc, out, "Failed to write to register @ 0x%08lx, value = 0x%08x", addr, wdata);

    addr = CTL_REG;
    wdata = 0x0;
    rc = fpga_pci_poke(pci_bar_handle, addr, wdata);
    fail_on(rc, out, "Failed to write to register @ 0x%08lx, value = 0x%08x", addr, wdata);

    // Trigger clock frequency counters
    addr = CTL_REG;
    wdata = 0x1;
    rc = fpga_pci_poke(pci_bar_handle, addr, wdata);
    fail_on(rc, out, "Failed to write to register @ 0x%08lx, value = 0x%08x", addr, wdata);

    // Wait until frequency is measured
    loop_count = 0;
    addr = CTL_REG;
    do {
      sleep(1); // CL_CLK_FREQ block needs atleast 1s of time to measure frequency
      rc = fpga_pci_peek(pci_bar_handle, addr, &read_data);
      fail_on(rc, out, "Failed to read from register @0x%08lx", addr);
      loop_count++;
    } while ((read_data != expected_value) && (loop_count < MAX_LOOP_COUNT));

    if (loop_count >= MAX_LOOP_COUNT) {
      rc = 1;
      fail_on(rc, out, "Timeout: measure_clk_freq() trigger still active after %d iterations", loop_count);
    }

 out:
    return rc;
}

//=============================================================
//
// display_results()
//
//=============================================================
int display_results(int slot_id) {
    int rc;
    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
    int fpga_attach_flags = 0;
    uint64_t addr  = 0;
    uint32_t read_data = 0;
    int ii;

    // Config space is on PF0-BAR0
    int pf_id  = 0;
    int bar_id = 0;

    // Kind of hash-table clk_freq{clk_names[0]} = %f MHz
    float clk_freq [10];
    char  *clk_names [] = {
      "clk_main_a0",
      "clk_extra_a1",
      "clk_extra_a2",
      "clk_extra_a3",
      "clk_extra_b0",
      "clk_extra_b1",
      "clk_extra_c0",
      "clk_extra_c1",
      "clk_hbm_axi",
      "clk_hbm_ref",
    };
    char ref_freq[] = "REF_FREQ_CTR";

    // Expected values
    int clk_freq_exp [10] = {
      250, /* Default Freq for clk_main_a0  */
      125, /* Default Freq for clk_extra_a1 */
      375, /* Default Freq for clk_extra_a2 */
      500, /* Default Freq for clk_extra_a3 */
      450, /* Default Freq for clk_extra_b0 */
      225, /* Default Freq for clk_extra_b1 */
      300, /* Default Freq for clk_extra_c0 */
      400, /* Default Freq for clk_extra_c1 */
      450, /* Default Freq for clk_hbm_axi  */
      100, /* Default Freq for clk_hbm_ref  */
    };
    unsigned int ref_freq_exp = 100000000;

    printf("__INFO__: display_results()\n");
    rc = fpga_pci_attach(slot_id, pf_id, bar_id, fpga_attach_flags, &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to the AFI on slot id %d", slot_id);

    // read reference counter and check for expected value
    addr = REF_FREQ_CTR;
    rc = fpga_pci_peek(pci_bar_handle, addr, &read_data);
    fail_on(rc, out, "Failed to read from register @0x%08lx", addr);
    rc = (read_data != (uint32_t) ref_freq_exp);
    fail_on(rc, out, "__ERROR__: %-15s = %d | Expected = %d\n", ref_freq, read_data, ref_freq_exp);
    printf("__INFO__: %-15s = %d\n", ref_freq, read_data);

    //
    // Read all freq counters
    //
    ii = 0;
    for (addr = FREQ_CTR_0; addr <= FREQ_CTR_9; addr += 0x4) {
      rc = fpga_pci_peek(pci_bar_handle, addr, &read_data);
      fail_on(rc, out, "Failed to read from register @0x%08lx", addr);
      // Convert hex to frequency in MHz
      clk_freq[ii] = ((float) read_data) / 1000000.0;

      // check for expected default value
      rc = ((int) clk_freq[ii] != clk_freq_exp[ii]);
      fail_on(rc, out, "__ERROR__: %-15s = %4.4f MHz | Expected = %4.4f MHz", clk_names[ii], clk_freq[ii], (float) clk_freq_exp[ii]);

      printf("__INFO__: %-15s = %4.4f MHz\n", clk_names[ii], clk_freq[ii]);
      ii++;
    }

out:
    return rc;
}
