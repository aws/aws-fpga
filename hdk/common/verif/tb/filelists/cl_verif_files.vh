//------------------------------------------------------------------------------
// Amazon FPGA Hardware Development Kit
//
// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
//------------------------------------------------------------------------------

// File: cl_verif_files.vh
// File that includes all of the CL common testbench sources.

`ifndef __CL_VERIF_FILES_VH__
`define __CL_VERIF_FILES_VH__

`include "verif/models/xilinx_axi_pc/axi_protocol_checker_v1_1_vl_rfs.v"
`include "verif/packages/anp_base_pkg.sv"
`include "verif/tb/sv/tb_type_defines_pkg.sv"
`include "verif/models/sh_bfm/axil_bfm.sv"
`include "verif/models/sh_bfm/axis_bfm_pkg.sv"
`include "verif/models/sh_bfm/axis_bfm.sv"
`include "verif/models/sh_bfm/sh_bfm.sv"
`include "verif/models/fpga/fpga.sv"
`include "verif/models/fpga/card.sv"
`include "verif/tb/sv/tb.sv"

`endif//__CL_VERIF_FILES_VH__

