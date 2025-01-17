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


  // PCIe Slave (ocl) Interface from SH to CL
  assign cl_ocl_awready             =   1'b0;

  assign cl_ocl_wready              =   1'b0;

  assign cl_ocl_bvalid              =   1'b0;
  assign cl_ocl_bresp[1:0]          =   2'b0;

  assign cl_ocl_arready             =   1'b0;

  assign cl_ocl_rvalid              =   1'b0;
  assign cl_ocl_rdata[31:0]         =  32'b0;
  assign cl_ocl_rresp[1:0]          =   2'b0;
