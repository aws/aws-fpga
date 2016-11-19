// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

   //------------------------------------------------------
   // DIMM Interface from CL
   //------------------------------------------------------
   
   wire                CLK_300M_DIMM0_DP;
   wire                CLK_300M_DIMM0_DN;
   wire                M_A_ACT_N;
   wire [16:0]         M_A_MA;
   wire [1:0]          M_A_BA;
   wire [1:0]          M_A_BG;
   wire [0:0]          M_A_CKE;
   wire [0:0]          M_A_ODT;
   wire [0:0]          M_A_CS_N;
   wire [0:0]          M_A_CLK_DN;
   wire [0:0]          M_A_CLK_DP;
   wire                RST_DIMM_A_N;
   wire                M_A_PAR;
   wire [63:0]         M_A_DQ;
   wire [7:0]          M_A_ECC;
   wire [17:0]         M_A_DQS_DP;
   wire [17:0]         M_A_DQS_DN;
   
   //------------------------------------------------------
   // DIMM 1 Interface from CL
   //------------------------------------------------------
   
   wire                CLK_300M_DIMM1_DP;
   wire                CLK_300M_DIMM1_DN;
   wire                M_B_ACT_N;
   wire [16:0]         M_B_MA;
   wire [1:0]          M_B_BA;
   wire [1:0]          M_B_BG;
   wire [0:0]          M_B_CKE;
   wire [0:0]          M_B_ODT;
   wire [0:0]          M_B_CS_N;
   wire [0:0]          M_B_CLK_DN;
   wire [0:0]          M_B_CLK_DP;
   wire                RST_DIMM_B_N;
   wire                M_B_PAR;
   wire [63:0]         M_B_DQ;
   wire [7:0]          M_B_ECC;
   wire [17:0]         M_B_DQS_DP;
   wire [17:0]         M_B_DQS_DN;
   
   //------------------------------------------------------
   // DIMM 3 Interface from CL
   //------------------------------------------------------
   
   wire                CLK_300M_DIMM3_DP;
   wire                CLK_300M_DIMM3_DN;
   wire                M_D_ACT_N;
   wire [16:0]         M_D_MA;
   wire [1:0]          M_D_BA;
   wire [1:0]          M_D_BG;
   wire [0:0]          M_D_CKE;
   wire [0:0]          M_D_ODT;
   wire [0:0]          M_D_CS_N;
   wire [0:0]          M_D_CLK_DN;
   wire [0:0]          M_D_CLK_DP;
   wire                RST_DIMM_D_N;
   wire                M_D_PAR;
   wire [63:0]         M_D_DQ;
   wire [7:0]          M_D_ECC;
   wire [17:0]         M_D_DQS_DP;
   wire [17:0]         M_D_DQS_DN;
   
