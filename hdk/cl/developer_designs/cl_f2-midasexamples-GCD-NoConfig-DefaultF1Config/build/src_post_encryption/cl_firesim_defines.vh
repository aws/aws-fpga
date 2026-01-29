// Amazon FPGA Hardware Development Kit
//
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

`ifndef CL_FIRESIM_DEFINES
`define CL_FIRESIM_DEFINES

//Put module name of the CL design here.  This is used to instantiate in top.sv
`define CL_NAME cl_firesim

//Highly recommeneded.  For lib FIFO block, uses less async reset (take advantage of
// FPGA flop init capability).  This will help with routing resources.
`define FPGA_LESS_RST

// Uncomment to disable Virtual JTAG
//`define DISABLE_VJTAG_DEBUG

// Default AXI values
`define DEF_AXSIZE    3'd6   // 64 Bytes per beat
`define DEF_AXBURST   2'd1   // INCR burst
`define DEF_AXCACHE   4'd1   // Bufferable, Non-Cacheable, No Read-Allocate, No Write-Allocate
`define DEF_AXLOCK    1'd0   // Normal access
`define DEF_AXPROT    3'd2   // Unprivileged access, Non-Secure Access
`define DEF_AXQOS     4'd0   // Regular Identifier
`define DEF_AXREGION  4'd0   // Single region

`endif
