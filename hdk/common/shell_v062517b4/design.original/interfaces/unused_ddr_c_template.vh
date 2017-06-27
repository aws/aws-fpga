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

  assign cl_sh_ddr_awid     =  16'b0;
  assign cl_sh_ddr_awaddr   =  64'b0;
  assign cl_sh_ddr_awlen    =   8'b0;
  assign cl_sh_ddr_awsize   =   3'b0;
  assign cl_sh_ddr_awvalid  =   1'b0;

  assign cl_sh_ddr_wid      =  16'b0;
  assign cl_sh_ddr_wdata    = 512'b0;
  assign cl_sh_ddr_wstrb    =  64'b0;
  assign cl_sh_ddr_wlast    =   1'b0;
  assign cl_sh_ddr_wvalid   =   1'b0;

  assign cl_sh_ddr_bready   =   1'b0;

  assign cl_sh_ddr_arid     =  16'b0;
  assign cl_sh_ddr_araddr   =  64'b0;
  assign cl_sh_ddr_arlen    =   8'b0;
  assign cl_sh_ddr_arsize   =   3'b0;
  assign cl_sh_ddr_arvalid  =   1'b0;

  assign cl_sh_ddr_rready   =   1'b0;

