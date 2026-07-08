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

// OCL register offsets (PF0-BAR0) - adder registers
#define CL_AXIL_REG_OFFSET_A         0x00
#define CL_AXIL_REG_OFFSET_B         0x04
#define CL_AXIL_REG_OFFSET_SUM       0x08
#define CL_AXIL_REG_OFFSET_CARRY     0x0C
#define CL_AXIL_REG_OFFSET_CONTROL   0x10

// Control reg masks
#define CONTROL_READY_MASK 0x02
#define CONTROL_START_MASK 0x01

// FPGA Slot 0
#define SLOT_ID 0

// OCL BAR: PF0-BAR0
#define CL_CLK_GEN_APP_PF      0
#define CL_CLK_GEN_BAR_ID      0
#define CL_CLK_GEN_PCI_FLAGS   0
