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

// Only the DDR pins are connected. The AXI and stats interfaces are tied-off.

//-------------------------------------------------
// Array Signals to Tie-off AXI interfaces to sh_ddr module
//-------------------------------------------------
  logic         tie_zero[2:0];
  logic [ 15:0] tie_zero_id[2:0];
  logic [ 63:0] tie_zero_addr[2:0];
  logic [  7:0] tie_zero_len[2:0];
  logic [511:0] tie_zero_data[2:0];
  logic [ 63:0] tie_zero_strb[2:0];

sh_ddr #(.DDR_A_PRESENT(0),
         .DDR_B_PRESENT(0),
         .DDR_D_PRESENT(0)) SH_DDR
   (
   .clk(clk_main_a0),
   .rst_n(rst_main_n_sync),
   .stat_clk(clk_main_a0),
   .stat_rst_n(clk_main_a0),

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
   .M_A_PAR(M_A_PAR),
   .M_A_DQ(M_A_DQ),
   .M_A_ECC(M_A_ECC),
   .M_A_DQS_DP(M_A_DQS_DP),
   .M_A_DQS_DN(M_A_DQS_DN),
   .cl_RST_DIMM_A_N(),
   
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
   .M_B_PAR(M_B_PAR),
   .M_B_DQ(M_B_DQ),
   .M_B_ECC(M_B_ECC),
   .M_B_DQS_DP(M_B_DQS_DP),
   .M_B_DQS_DN(M_B_DQS_DN),
   .cl_RST_DIMM_B_N(),

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
   .M_D_PAR(M_D_PAR),
   .M_D_DQ(M_D_DQ),
   .M_D_ECC(M_D_ECC),
   .M_D_DQS_DP(M_D_DQS_DP),
   .M_D_DQS_DN(M_D_DQS_DN),
   .cl_RST_DIMM_D_N(),

   //------------------------------------------------------
   // DDR-4 Interface from CL (AXI-4)
   //------------------------------------------------------
   .cl_sh_ddr_awid     (tie_zero_id),
   .cl_sh_ddr_awaddr   (tie_zero_addr),
   .cl_sh_ddr_awlen    (tie_zero_len),
   .cl_sh_ddr_awvalid  (tie_zero),
   .sh_cl_ddr_awready  (),

   .cl_sh_ddr_wid      (tie_zero_id),
   .cl_sh_ddr_wdata    (tie_zero_data),
   .cl_sh_ddr_wstrb    (tie_zero_strb),
   .cl_sh_ddr_wlast    (3'b0),
   .cl_sh_ddr_wvalid   (3'b0),
   .sh_cl_ddr_wready   (),

   .sh_cl_ddr_bid      (),
   .sh_cl_ddr_bresp    (),
   .sh_cl_ddr_bvalid   (),
   .cl_sh_ddr_bready   (3'b0),

   .cl_sh_ddr_arid     (tie_zero_id),
   .cl_sh_ddr_araddr   (tie_zero_addr),
   .cl_sh_ddr_arlen    (tie_zero_len),
   .cl_sh_ddr_arvalid  (3'b0),
   .sh_cl_ddr_arready  (),

   .sh_cl_ddr_rid      (),
   .sh_cl_ddr_rdata    (),
   .sh_cl_ddr_rresp    (),
   .sh_cl_ddr_rlast    (),
   .sh_cl_ddr_rvalid   (),
   .cl_sh_ddr_rready   (3'b0),

   .sh_cl_ddr_is_ready (),

   .sh_ddr_stat_addr0   (8'h00),
   .sh_ddr_stat_wr0     (1'b0), 
   .sh_ddr_stat_rd0     (1'b0), 
   .sh_ddr_stat_wdata0  (32'b0),
   .ddr_sh_stat_ack0   (),
   .ddr_sh_stat_rdata0 (),
   .ddr_sh_stat_int0   (),
   .sh_ddr_stat_addr1   (8'h00),
   .sh_ddr_stat_wr1     (1'b0), 
   .sh_ddr_stat_rd1     (1'b0), 
   .sh_ddr_stat_wdata1  (32'b0),
   .ddr_sh_stat_ack1   (),
   .ddr_sh_stat_rdata1 (),
   .ddr_sh_stat_int1   (),
   .sh_ddr_stat_addr2   (8'h00),
   .sh_ddr_stat_wr2     (1'b0), 
   .sh_ddr_stat_rd2     (1'b0), 
   .sh_ddr_stat_wdata2  (32'b0),
   .ddr_sh_stat_ack2   (),
   .ddr_sh_stat_rdata2 (),
   .ddr_sh_stat_int2   ()
   );

// Tie-off AXI interfaces to sh_ddr module
  assign tie_zero[2]        =   1'b0;
  assign tie_zero[1]        =   1'b0;
  assign tie_zero[0]        =   1'b0;

  assign tie_zero_id[2]     =  16'b0;
  assign tie_zero_id[1]     =  16'b0;
  assign tie_zero_id[0]     =  16'b0;

  assign tie_zero_addr[2]   =  64'b0;
  assign tie_zero_addr[1]   =  64'b0;
  assign tie_zero_addr[0]   =  64'b0;

  assign tie_zero_len[2]    =   8'b0;
  assign tie_zero_len[1]    =   8'b0;
  assign tie_zero_len[0]    =   8'b0;

  assign tie_zero_data[2]   = 512'b0;
  assign tie_zero_data[1]   = 512'b0;
  assign tie_zero_data[0]   = 512'b0;

  assign tie_zero_strb[2]   =  64'b0;
  assign tie_zero_strb[1]   =  64'b0;
  assign tie_zero_strb[0]   =  64'b0;

  assign ddr_sh_stat_ack0   =   1'b1; // Needed in order not to hang the interface
  assign ddr_sh_stat_rdata0 =  32'b0;
  assign ddr_sh_stat_int0   =   8'b0;

  assign ddr_sh_stat_ack1   =   1'b1; // Needed in order not to hang the interface
  assign ddr_sh_stat_rdata1 =  32'b0;
  assign ddr_sh_stat_int1   =   8'b0;

  assign ddr_sh_stat_ack2   =   1'b1; // Needed in order not to hang the interface
  assign ddr_sh_stat_rdata2 =  32'b0;
  assign ddr_sh_stat_int2   =   8'b0;
