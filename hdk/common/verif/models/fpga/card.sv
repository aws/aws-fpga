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

module card();

`include "fpga_ddr.svh"
   
fpga fpga  (
            .CLK_300M_DIMM0_DP(CLK_300M_DIMM0_DP),
            .CLK_300M_DIMM0_DN(CLK_300M_DIMM0_DN),
            .M_A_ACT_N(M_A_ACT_N),
            .M_A_MA(M_A_MA),
            .M_A_BA(M_A_BA),
            .M_A_BG(M_A_BG),
            .M_A_CKE(M_A_CKE),
            .M_A_ODT(M_A_ODT),
            .M_A_CS_N(M_A_CS_N),
            .M_A_CLK_DN(M_A_CLK_DN),
            .M_A_CLK_DP(M_A_CLK_DP),
            .RST_DIMM_A_N(RST_DIMM_A_N),
            .M_A_PAR(M_A_PAR),
            .M_A_DQ(M_A_DQ),
            .M_A_ECC(M_A_ECC),
            .M_A_DQS_DP(M_A_DQS_DP),
            .M_A_DQS_DN(M_A_DQS_DN),
            
            .CLK_300M_DIMM1_DP(CLK_300M_DIMM1_DP),
            .CLK_300M_DIMM1_DN(CLK_300M_DIMM1_DN),
            .M_B_ACT_N(M_B_ACT_N),
            .M_B_MA(M_B_MA),
            .M_B_BA(M_B_BA),
            .M_B_BG(M_B_BG),
            .M_B_CKE(M_B_CKE),
            .M_B_ODT(M_B_ODT),
            .M_B_CS_N(M_B_CS_N),
            .M_B_CLK_DN(M_B_CLK_DN),
            .M_B_CLK_DP(M_B_CLK_DP),
            .RST_DIMM_B_N(RST_DIMM_B_N),
            .M_B_PAR(M_B_PAR),
            .M_B_DQ(M_B_DQ),
            .M_B_ECC(M_B_ECC),
            .M_B_DQS_DP(M_B_DQS_DP),
            .M_B_DQS_DN(M_B_DQS_DN),
            
            // ------------------- DDR4 x72 RDIMM 2100 Interface C ----------------------------------
            .CLK_300M_DIMM2_DP(CLK_300M_DIMM2_DP),
            .CLK_300M_DIMM2_DN(CLK_300M_DIMM2_DN),
            .M_C_ACT_N(M_C_ACT_N),
            .M_C_MA(M_C_MA),
            .M_C_BA(M_C_BA),
            .M_C_BG(M_C_BG),
            .M_C_CKE(M_C_CKE),
            .M_C_ODT(M_C_ODT),
            .M_C_CS_N(M_C_CS_N),
            .M_C_CLK_DN(M_C_CLK_DN),
            .M_C_CLK_DP(M_C_CLK_DP),
            .RST_DIMM_C_N(RST_DIMM_C_N),
            .M_C_PAR(M_C_PAR),
            .M_C_DQ(M_C_DQ),
            .M_C_ECC(M_C_ECC),
            .M_C_DQS_DP(M_C_DQS_DP),
            .M_C_DQS_DN(M_C_DQS_DN),
            
            .CLK_300M_DIMM3_DP(CLK_300M_DIMM3_DP),
            .CLK_300M_DIMM3_DN(CLK_300M_DIMM3_DN),
            .M_D_ACT_N(M_D_ACT_N),
            .M_D_MA(M_D_MA),
            .M_D_BA(M_D_BA),
            .M_D_BG(M_D_BG),
            .M_D_CKE(M_D_CKE),
            .M_D_ODT(M_D_ODT),
            .M_D_CS_N(M_D_CS_N),
            .M_D_CLK_DN(M_D_CLK_DN),
            .M_D_CLK_DP(M_D_CLK_DP),
            .RST_DIMM_D_N(RST_DIMM_D_N),
            .M_D_PAR(M_D_PAR),
            .M_D_DQ(M_D_DQ),
            .M_D_ECC(M_D_ECC),
            .M_D_DQS_DP(M_D_DQS_DP),
            .M_D_DQS_DN(M_D_DQS_DN)
            
            );

endmodule // card
