// ============================================================================
// Amazon FPGA Hardware Development Kit
//
// Copyright 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include "fpga_pci.h"
#include "fpga_mgmt.h"
#include "fpga_clkgen.h"
#include "utils/lcd.h"

#include "cl_clk_gen_def.h"
#include "cl_clk_gen_utils.h"

static const struct logger *logger = &logger_stdout;

void usage(const char *program_name)
{
    printf("usage: %s [--slot <slot>]\n", program_name);
}

int verify_clk_freq(int slot_id)
{
    int rc;
    struct fpga_clkgen_info info;

    rc = aws_clkgen_get_dynamic(slot_id, &info);
    fail_on(rc, out, "aws_clkgen_get_dynamic failed");

    printf("\nClock frequencies from aws_clk_gen (Clock Recipe A2):\n");
    printf("  clk_extra_a1 = %.3f MHz (expected 15.625 MHz)\n",
           info.clock_group_a.clocks[0]);
    printf("  clk_extra_a2 = %.3f MHz (expected 125.000 MHz)\n",
           info.clock_group_a.clocks[1]);
    printf("  clk_extra_a3 = %.3f MHz (expected 62.500 MHz)\n",
           info.clock_group_a.clocks[2]);

    if (info.clock_group_a.clocks[0] != 15.625 ||
        info.clock_group_a.clocks[1] != 125.0 ||
        info.clock_group_a.clocks[2] != 62.5) {
        printf("FAIL: Clock frequency mismatch\n");
        rc = 1;
        goto out;
    }

    printf("PASS: Expected clock frequencies match\n");
    rc = 0;

out:
    return rc;
}

int main(int argc, char **argv)
{
    int rc;
    int slot_id = SLOT_ID;
    uint32_t sum, carry;
    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;

    for (int i = 1; i < argc; i++)
    {
        if (strncmp(argv[i], "--slot", sizeof("--slot") - 1) == 0 && i + 1 < argc)
            slot_id = atoi(argv[++i]);
        else {
            usage(argv[0]);
            return 1;
        }
    }

    rc = log_init("test_clk_adder");
    fail_on(rc, out, "Unable to initialize the log.");
    rc = log_attach(logger, NULL, 0);
    fail_on(rc, out, "Unable to attach to the log.");

    rc = fpga_mgmt_init();
    fail_on(rc, out, "Unable to initialize the fpga_mgmt library");

    printf("===================================================\n");
    printf("Running test_clk_adder (cl_clk_gen)\n");
    printf("===================================================\n");

    // Step 1: Set Clock Recipe A2 and de-assert resets
    printf("\nStep 1: Set Clock Recipe A2 and de-assert resets...\n");
    rc = aws_clkgen_set_recipe(slot_id, /*recipe_a=*/2, /*recipe_b=*/0, /*recipe_c=*/0, /*recipe_hbm=*/0, /*reset=*/0);
    fail_on(rc, out, "aws_clkgen_set_recipe failed");

    // Step 2: Verify clock frequency
    printf("\nStep 2: Verify clock frequency...\n");
    rc = verify_clk_freq(slot_id);
    fail_on(rc, out, "Clock frequency verification failed");

    // Step 3: Adder operations across clock domain
    printf("\nStep 3: Adder operations across clock domain...\n\n");
    rc = fpga_pci_attach(slot_id, CL_CLK_GEN_APP_PF, CL_CLK_GEN_BAR_ID, CL_CLK_GEN_PCI_FLAGS, &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to OCL BAR on slot %d", slot_id);

    rc  = cl_add_validate(pci_bar_handle, 0x100, 0x200, &sum, &carry);
    rc |= cl_add_validate(pci_bar_handle, 0xFFFFFFFF, 0x1, &sum, &carry);
    rc |= cl_add_validate(pci_bar_handle, 0xFFFFFFFF, 0xFFFFFFFF, &sum, &carry);
    rc |= cl_add_validate(pci_bar_handle, 0x12345678, 0x9ABCDEF0, &sum, &carry);
    fail_on(rc, out, "Adder validation failed");

    printf("\n===================================================\n");
    printf("TEST PASSED\n");
    printf("===================================================\n");

out:
    if (pci_bar_handle != PCI_BAR_HANDLE_INIT)
        fpga_pci_detach(pci_bar_handle);
    return rc;
}
