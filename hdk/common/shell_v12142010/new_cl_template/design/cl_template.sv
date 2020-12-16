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

module cl_template #(parameter NUM_PCIE=1, parameter NUM_DDR=4, parameter NUM_HMC=4, parameter NUM_GTY = 4) 

(
   `include "cl_ports.vh" // Fixed port definition

);
  
   localparam NUM_CFG_STGS_INT_TST = 4;
   localparam NUM_CFG_STGS_HMC_ATG = 4;
   localparam NUM_CFG_STGS_CL_DDR_ATG = 4;
   localparam NUM_CFG_STGS_SH_DDR_ATG = 4;
   localparam NUM_CFG_STGS_PCIE_ATG = 4;
   localparam NUM_CFG_STGS_AURORA_ATG = 4;
   localparam NUM_CFG_STGS_XDCFG = 4;
   localparam NUM_CFG_STGS_XDMA = 4;
   
`ifdef SIM
   localparam DDR_SCRB_MAX_ADDR = 64'h1FFF;
   localparam HMC_SCRB_MAX_ADDR = 64'h7FF;
`else   
   localparam DDR_SCRB_MAX_ADDR = 64'h3FFFFFFFF; //16GB 
   localparam HMC_SCRB_MAX_ADDR = 64'h7FFFFFFF;  // 2GB
`endif
   localparam DDR_SCRB_BURST_LEN_MINUS1 = 15;
   localparam HMC_SCRB_BURST_LEN_MINUS1 = 3;

//-------------------------------------------------
// Reset Synchronization
//-------------------------------------------------
logic pre_sync_rst_n;
logic sync_rst_n;
   
always_ff @(negedge rst_main_n or posedge clk)
   if (!rst_main_n)
   begin
      pre_sync_rst_n <= 0;
      sync_rst_n <= 0;
   end
   else
   begin
      pre_sync_rst_n <= 1;
      sync_rst_n <= pre_sync_rst_n;
   end

//----------------------------------------- 
// DDR controller instantiation   
//----------------------------------------- 
// All designs should instantiate the sh_ddr module even if not utilizing the
// DDR controllers. It must be instantiated in order to prevent build errors
// related to DDR pin constraints.

// Only the DDR pins are connected. The AXI and stats interfaces are tied-off.

sh_ddr #(.DDR_A_PRESENT(0),
         .DDR_B_PRESENT(0),
         .DDR_D_PRESENT(0)) SH_DDR
   (
   .clk(clk),
   .rst_n(sync_rst_n),

   .stat_clk(clk),
   .stat_rst_n(sync_rst_n),


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
   .cl_RST_DIMM_A_N(RST_DIMM_A_N),

   
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
   .cl_RST_DIMM_B_N(RST_DIMM_B_N),

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
   .cl_RST_DIMM_D_N(RST_DIMM_D_N),

   //------------------------------------------------------
   // DDR-4 Interface from CL (AXI-4)
   //------------------------------------------------------
   .cl_sh_ddr_awid     (tie_zero_id),
   .cl_sh_ddr_awaddr   (tie_zero_addr),
   .cl_sh_ddr_awlen    (tie_zero_len),
   .cl_sh_ddr_awsize   (tie_zero),
   .cl_sh_ddr_awvalid  (tie_zero),
   .cl_sh_ddr_awburst  (tie_zero),
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
   .cl_sh_ddr_arsize   (tie_zero),
   .cl_sh_ddr_arvalid  (3'b0),
   .cl_sh_ddr_arburst  (tie_zero),
   .sh_cl_ddr_arready  (),

   .sh_cl_ddr_rid      (),
   .sh_cl_ddr_rdata    (),
   .sh_cl_ddr_rresp    (),
   .sh_cl_ddr_rlast    (),
   .sh_cl_ddr_rvalid   (),
   .cl_sh_ddr_rready   (3'b0),

   .sh_cl_ddr_is_ready (),

   .sh_ddr_stat_addr0   (tie_zero_stat_addr),
   .sh_ddr_stat_wr0     (3'b0), 
   .sh_ddr_stat_rd0     (3'b0), 
   .sh_ddr_stat_wdata0  (tie_zero_stat_data),
   .ddr_sh_stat_ack0    (),
   .ddr_sh_stat_rdata0  (),
   .ddr_sh_stat_int0    ()

   .sh_ddr_stat_addr1  (tie_zero_stat_addr) ,
   .sh_ddr_stat_wr1    (3'b0) , 
   .sh_ddr_stat_rd1    (3'b0) , 
   .sh_ddr_stat_wdata1 (tie_zero_stat_data) , 
   .ddr_sh_stat_ack1   () ,
   .ddr_sh_stat_rdata1 (),
   .ddr_sh_stat_int1   (),

   .sh_ddr_stat_addr2  (tie_zero_stat_addr) ,
   .sh_ddr_stat_wr2    (3'b0) , 
   .sh_ddr_stat_rd2    (3'b0) , 
   .sh_ddr_stat_wdata2 (tie_zero_stat_data) , 
   .ddr_sh_stat_ack2   () ,
   .ddr_sh_stat_rdata2 (),
   .ddr_sh_stat_int2   () 
   );

//-------------------------------------------
// Tie-Off Global Signals
//-------------------------------------------
`ifndef CL_VERSION
   `define CL_VERSION 32'hee_ee_ee_00
`endif  

   assign cl_sh_flr_done        = 1'b0;
   assign cl_sh_id0[31:0]       = 32'h0000_0000;
   assign cl_sh_id1[31:0]       = 32'h0000_0000;
   assign cl_sh_status0[31:0]   = 32'h0000_0000;
   assign cl_sh_status1[31:0]   = `CL_VERSION;

//------------------------------------
// Tie-Off Unused AXI Interfaces
//------------------------------------

   // PCIe Interface from SH to CL
   assign cl_sh_pcis_awready[0] =   1'b0;
                                    
   assign cl_sh_pcis_wready[0]  =   1'b0;
                                    
   assign cl_sh_pcis_bresp[0]   =   2'b0;
   assign cl_sh_pcis_bid[0]     =   5'b0;
   assign cl_sh_pcis_bvalid[0]  =   1'b0;
                                    
   assign cl_sh_pcis_arready[0] =   1'b0;

   assign cl_sh_pcis_rdata[0]   = 512'b0;
   assign cl_sh_pcis_rresp[0]   =   2'b0;
   assign cl_sh_pcis_rid[0]     =   5'b0;
   assign cl_sh_pcis_rlast[0]   =   1'b0;
   assign cl_sh_pcis_rvalid[0]  =   1'b0;

   // PCIe Interface from CL to SH
   assign cl_sh_pcim_awid[0]    =   5'b0;
   assign cl_sh_pcim_awaddr[0]  =  64'b0;
   assign cl_sh_pcim_awlen[0]   =   8'b0;
   assign cl_sh_pcim_awuser[0]  =  19'b0;
   assign cl_sh_pcim_awvalid[0] =   1'b0;
                                   
   assign cl_sh_pcim_wdata[0]   = 512'b0;
   assign cl_sh_pcim_wstrb[0]   =  64'b0;
   assign cl_sh_pcim_wlast[0]   =   1'b0;
   assign cl_sh_pcim_wvalid[0]  =   1'b0;
                                    
   assign cl_sh_pcim_bready[0]  =   1'b0;
                                    
   assign cl_sh_pcim_arid[0]    =   5'b0;
   assign cl_sh_pcim_araddr[0]  =  64'b0;
   assign cl_sh_pcim_arlen[0]   =   8'b0;
   assign cl_sh_pcim_aruser[0]  =  19'b0;
   assign cl_sh_pcim_arvalid[0] =   1'b0;
                                    
   assign cl_sh_pcim_rready[0]  =   1'b0;

   // DDRC Interface from CL to SH
   assign ddr_sh_stat_ack[2:0]  =   3'b111; // Needed in order not to hang the interface
   assign ddr_sh_stat_rdata[2]  =  32'b0;
   assign ddr_sh_stat_rdata[1]  =  32'b0;
   assign ddr_sh_stat_rdata[0]  =  32'b0;
   assign ddr_sh_stat_int[2]    =   8'b0;
   assign ddr_sh_stat_int[1]    =   8'b0;
   assign ddr_sh_stat_int[0]    =   8'b0;
                                   
   assign cl_sh_ddr_awid        =   6'b0;
   assign cl_sh_ddr_awaddr      =  64'b0;
   assign cl_sh_ddr_awlen       =   8'b0;
   assign cl_sh_ddr_awvalid     =   1'b0;
                                
   assign cl_sh_ddr_wid         =   6'b0;
   assign cl_sh_ddr_wdata       = 512'b0;
   assign cl_sh_ddr_wstrb       =  64'b0;
   assign cl_sh_ddr_wlast       =   1'b0;
   assign cl_sh_ddr_wvalid      =   1'b0;
                                
   assign cl_sh_ddr_bready      =   1'b0;
                                
   assign cl_sh_ddr_arid        =   6'b0;
   assign cl_sh_ddr_araddr      =  64'b0;
   assign cl_sh_ddr_arlen       =   8'b0;
   assign cl_sh_ddr_arvalid     =   1'b0;
                                
   assign cl_sh_ddr_rready      =   1'b0;

  // Tie-off AXI interfaces to sh_ddr module
  assign tie_zero[2]      = 1'b0;
  assign tie_zero[1]      = 1'b0;
  assign tie_zero[0]      = 1'b0;
                          
  assign tie_zero_id[2]   = 6'b0;
  assign tie_zero_id[1]   = 6'b0;
  assign tie_zero_id[0]   = 6'b0;

  assign tie_zero_addr[2] = 64'b0;
  assign tie_zero_addr[1] = 64'b0;
  assign tie_zero_addr[0] = 64'b0;

  assign tie_zero_len[2]  = 8'b0;
  assign tie_zero_len[1]  = 8'b0;
  assign tie_zero_len[0]  = 8'b0;

  assign tie_zero_data[2] = 512'b0;
  assign tie_zero_data[1] = 512'b0;
  assign tie_zero_data[0] = 512'b0;

  assign tie_zero_strb[2] = 64'b0;
  assign tie_zero_strb[1] = 64'b0;
  assign tie_zero_strb[0] = 64'b0;

//------------------------------------
// Tie-Off HMC Interfaces
//------------------------------------

   assign hmc_iic_scl_o            =  1'b0;
   assign hmc_iic_scl_t            =  1'b0;
   assign hmc_iic_sda_o            =  1'b0;
   assign hmc_iic_sda_t            =  1'b0;

   assign hmc_sh_stat_ack          =  1'b0;
   assign hmc_sh_stat_rdata[31:0]  = 32'b0;

   assign hmc_sh_stat_int[7:0]     =  8'b0;

//------------------------------------
// Tie-Off Aurora Interfaces
//------------------------------------
   assign aurora_sh_stat_ack   =  1'b0;
   assign aurora_sh_stat_rdata = 32'b0;
   assign aurora_sh_stat_int   =  8'b0;

endmodule





