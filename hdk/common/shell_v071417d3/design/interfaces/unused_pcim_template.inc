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

 // PCIe Master (pcim) Interface from CL to SH
  assign cl_sh_pcim_awid             =  16'b0;
  assign cl_sh_pcim_awaddr           =  64'b0;
  assign cl_sh_pcim_awlen            =   8'b0;
  assign cl_sh_pcim_awsize           =   3'h0;
  assign cl_sh_pcim_awuser           =  19'b0;
  assign cl_sh_pcim_awvalid          =   1'b0;

  assign cl_sh_pcim_wdata            = 512'b0;
  assign cl_sh_pcim_wstrb            =  64'b0;
  assign cl_sh_pcim_wlast            =   1'b0;
  assign cl_sh_pcim_wvalid           =   1'b0;

  assign cl_sh_pcim_bready           =   1'b0;

  assign cl_sh_pcim_arid             =  16'b0;
  assign cl_sh_pcim_araddr           =  64'b0;
  assign cl_sh_pcim_arlen            =   8'b0;
  assign cl_sh_pcim_arsize           =   3'h0;
  assign cl_sh_pcim_aruser           =  19'b0;
  assign cl_sh_pcim_arvalid          =   1'b0;

  assign cl_sh_pcim_rready           =   1'b0;

