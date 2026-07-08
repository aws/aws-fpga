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

`ifndef CL_CLK_GEN_DEFINES
`define CL_CLK_GEN_DEFINES

//Put module name of the CL design here.  This is used to instantiate in top.sv
`define CL_NAME cl_clk_gen

// Uncomment to disable ILA debug
`define NO_CL_CLK_GEN_ILA

// Register address offsets (OCL interface - adder registers)
`define ADDR_OPERAND_A      32'h00
`define ADDR_OPERAND_B      32'h04
`define ADDR_SUM            32'h08
`define ADDR_CARRY          32'h0C
`define ADDR_CONTROL_STATUS 32'h10
`define INVALID_ADDR_RESP   32'hDEADBEEF

// AXI constants
`define AXI_PROT_DEFAULT    3'h0
`define AXI_RESP_OKAY       2'b00

`endif
