// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

//Put module name of the CL design here.  This is used to instantiate in top.sv
`define CL_NAME cl_template

//Highly recommeneded.  For lib FIFO block, uses less async reset (take advantage of
// FPGA flop init capability).  This will help with routing resources.
`define FPGA_LESS_RST

//Must have this define or will get syntax errors.  Curretly XDMA not supported.
`define NO_XDMA
