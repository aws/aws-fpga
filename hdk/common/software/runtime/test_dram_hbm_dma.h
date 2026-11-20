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

#pragma once

#include <stddef.h>
#include <stdint.h>

#include "fpga_pci.h"

#define USER_INTERRUPTS_MAX (16)

/* Structure to hold command-line parameters */
typedef struct {
  uint32_t slot_id;
} test_parameters_t;

/**
 * Prints usage information for the test program.
 *
 * @param program_name Name of the executable
 */
void usage(const char *program_name);

/**
 * Runs the DMA bandwidth and verification legs on a single XDMA channel.
 *
 * @param slot_id FPGA slot ID to test
 * @returns 0 on success, non-zero on failure
 */
int dma_example(int slot_id);

/**
 * Tests MSI-X interrupt functionality.
 *
 * @param slot_id FPGA slot ID
 * @param interrupt_number Interrupt number to test (0 to USER_INTERRUPTS_MAX-1)
 * @returns 0 on success, non-zero on failure
 */
int interrupt_example(int slot_id, int interrupt_number);

/**
 * Tests AXI Master functionality for DDR and HBM access.
 *
 * @param slot_id FPGA slot ID
 * @returns 0 on success, non-zero on failure
 */
int axi_mstr_example(int slot_id);

/**
 * Helper function for accessing DDR/HBM controllers via AXI Master block.
 * Performs a write followed by a read to verify data integrity.
 *
 * @param slot_id FPGA slot ID
 * @param pci_bar_handle PCI BAR handle for FPGA access
 * @param axi_mstr_test_addr_upper Upper 32 bits of the target memory address
 * @param axi_mstr_test_addr_lower Lower 32 bits of the target memory address
 * @param axi_mstr_test_data Data to write and verify
 * @returns 0 on success, non-zero on failure
 */
int axi_mstr_addr_access(int slot_id, pci_bar_handle_t pci_bar_handle, uint32_t axi_mstr_test_addr_upper, uint32_t axi_mstr_test_addr_lower,
                         uint32_t axi_mstr_test_data);
