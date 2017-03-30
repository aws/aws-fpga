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

//------------------------------------
// Tie-Off HMC Interfaces
//------------------------------------
  assign hmc_iic_scl_o           =  1'b0;
  assign hmc_iic_scl_t           =  1'b0;
  assign hmc_iic_sda_o           =  1'b0;
  assign hmc_iic_sda_t           =  1'b0;

  assign hmc_sh_stat_ack         =  1'b0;
  assign hmc_sh_stat_rdata[31:0] = 32'b0;

  assign hmc_sh_stat_int[7:0]    =  8'b0;

