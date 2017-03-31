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

  // PCIe Slave (sda) Interface from SH to CL
  assign cl_sda_awready              =   1'b0;

  assign cl_sda_wready               =   1'b0;

  assign cl_sda_bvalid               =   1'b0;
  assign cl_sda_bresp[1:0]           =   2'b0;

  assign cl_sda_arready              =   1'b0;

  assign cl_sda_rvalid               =   1'b0;
  assign cl_sda_rdata[31:0]          =  32'b0;
  assign cl_sda_rresp[1:0]           =   2'b0;
