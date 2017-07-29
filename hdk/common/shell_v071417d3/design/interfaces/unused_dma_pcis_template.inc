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


  // PCIe Slave (pcis) Interface from SH to CL
  assign cl_sh_dma_pcis_awready      =   1'b0;

  assign cl_sh_dma_pcis_wready       =   1'b0;

  assign cl_sh_dma_pcis_bid[5:0]     =   6'b0;
  assign cl_sh_dma_pcis_bresp[1:0]   =   2'b0;
  assign cl_sh_dma_pcis_bvalid       =   1'b0;

  assign cl_sh_dma_pcis_arready      =   1'b0;

  assign cl_sh_dma_pcis_rid[5:0]     =   6'b0;
  assign cl_sh_dma_pcis_rdata[511:0] = 512'b0;
  assign cl_sh_dma_pcis_rresp[1:0]   =   2'b0;
  assign cl_sh_dma_pcis_rlast        =   1'b0;
  assign cl_sh_dma_pcis_rvalid       =   1'b0;
