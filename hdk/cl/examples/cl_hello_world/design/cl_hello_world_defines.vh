//---------------------------------------------------------------------------------------
// Amazon FGPA Hardware Development Kit
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
//---------------------------------------------------------------------------------------

`ifndef CL_HELLO_WORLD_DEFINES
`define CL_HELLO_WORLD_DEFINES

//Put module name of the CL design here.  This is used to instantiate in top.sv
`define CL_NAME cl_hello_world

//Highly recommeneded.  For lib FIFO block, uses less async reset (take advantage of
// FPGA flop init capability).  This will help with routing resources.
`define FPGA_LESS_RST

// PCIe Vendor/Device ID Values
//    31:16: PCIe Device ID
//    15: 0: PCIe Vendor ID
//    - A Vendor ID value of 0x8086 is not valid.
//    - If using a Vendor ID value of 0x1D0F (Amazon) then valid
//      values for Device ID's are in the range of 0xF000 - 0xF0FF.
`define CL_SH_ID0       32'hF000_1D0F

// PCIe Subsystem/Subsystem Vendor ID Values
//    31:16: PCIe Subsystem ID
//    15: 0: PCIe Subsystem Vendor ID
`define CL_SH_ID1       32'h1D51_FEDD

`endif
