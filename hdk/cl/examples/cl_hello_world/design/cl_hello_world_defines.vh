// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

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


