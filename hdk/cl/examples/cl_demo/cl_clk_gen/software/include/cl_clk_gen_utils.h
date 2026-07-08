// =============================================================================
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
// =============================================================================

#pragma once

#include <stdint.h>
#include "fpga_pci.h"

/**
 * Performs addition of op_a + op_b using the CL hardware.
 */
int cl_add(pci_bar_handle_t pci_bar_handle, uint32_t op_a, uint32_t op_b,
           uint32_t *sum, uint32_t *carry);

/**
 * Performs addition using CL and validates against golden model.
 */
int cl_add_validate(pci_bar_handle_t pci_bar_handle, uint32_t op_a, uint32_t op_b,
                    uint32_t *sum, uint32_t *carry);
