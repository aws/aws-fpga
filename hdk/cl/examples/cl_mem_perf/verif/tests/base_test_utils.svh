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


`include "common_base_test.svh"

`define DDR_BASE_ADDR 64'h0
`define DDR_LEVEL_1 `_16_GB
`define DDR_LEVEL_2 `_32_GB
`define DDR_LEVEL_3 `_48_GB
`define HBM_BASE_ADDR `_64_GB


`include "aws_clk_gen_utils.svh"
`include "cl_dram_hbm_dma_utils.svh"
`include "cl_mem_perf_utils.svh"
