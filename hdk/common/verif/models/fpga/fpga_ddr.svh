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

  import "DPI-C" function string getenv(input string env_name);

  localparam ADDR_WIDTH                    = 17;
  localparam DQ_WIDTH                      = 72;
  localparam DQS_WIDTH                     = 18;
  localparam DM_WIDTH                      = 9;
  localparam DRAM_WIDTH                    = 4;
  localparam tCK                           = 952 ; //DDR4 interface clock period in ps
  localparam real SYSCLK_PERIOD            = tCK;
  localparam NUM_PHYSICAL_PARTS = (DQ_WIDTH/DRAM_WIDTH) ;
  parameter RANK_WIDTH                       = 1;
  parameter CS_WIDTH                       = 1;
  parameter ODT_WIDTH                      = 1;
  parameter CA_MIRROR                      = "OFF";

  localparam MRS                           = 3'b000;
  localparam REF                           = 3'b001;
  localparam PRE                           = 3'b010;
  localparam ACT                           = 3'b011;
  localparam WR                            = 3'b100;
  localparam RD                            = 3'b101;
  localparam ZQC                           = 3'b110;
  localparam NOP                           = 3'b111;
  //Added to support RDIMM wrapper
  localparam ODT_WIDTH_RDIMM   = 1;
  localparam CKE_WIDTH_RDIMM   = 1;
  localparam CS_WIDTH_RDIMM   = 1;
  localparam RANK_WIDTH_RDIMM   = 1;
  localparam RDIMM_SLOTS   = 4;
  localparam BANK_WIDTH_RDIMM = 2;
  localparam BANK_GROUP_WIDTH_RDIMM     = 2;

  localparam DM_DBI                        = "NONE";
  localparam DM_WIDTH_RDIMM                  = 18;
  localparam MEM_PART_WIDTH       = "x4";
  localparam REG_CTRL             = "ON";

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
   // DIMM 2 Interface from SH
   //------------------------------------------------------
   
   wire                CLK_300M_DIMM2_DP;
   wire                CLK_300M_DIMM2_DN;
   wire                M_C_ACT_N;
   wire [16:0]         M_C_MA;
   wire [1:0]          M_C_BA;
   wire [1:0]          M_C_BG;
   wire [0:0]          M_C_CKE;
   wire [0:0]          M_C_ODT;
   wire [0:0]          M_C_CS_N;
   wire [0:0]          M_C_CLK_DN;
   wire [0:0]          M_C_CLK_DP;
   wire                RST_DIMM_C_N;
   wire                M_C_PAR;
   wire [63:0]         M_C_DQ;
   wire [7:0]          M_C_ECC;
   wire [17:0]         M_C_DQS_DP;
   wire [17:0]         M_C_DQS_DN;
   
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

   int                 fp[17:0];
   string              ddr_name[17:0];
          
   int                 r;
   reg [1000:0]        hdk_name;
   
   //------------------------------------------------------
   // DDR Clocks
   //------------------------------------------------------
   logic ddr_clk;

   initial begin
      ddr_clk = 0;
      forever #1.666ns ddr_clk = ~ddr_clk;               
   end

   assign CLK_300M_DIMM0_DP =  ddr_clk;
   assign CLK_300M_DIMM0_DN = ~ddr_clk;
   assign CLK_300M_DIMM1_DP =  ddr_clk;
   assign CLK_300M_DIMM1_DN = ~ddr_clk;
   assign CLK_300M_DIMM2_DP =  ddr_clk;
   assign CLK_300M_DIMM2_DN = ~ddr_clk;
   assign CLK_300M_DIMM3_DP =  ddr_clk;
   assign CLK_300M_DIMM3_DN = ~ddr_clk;

`define EOF -1

`ifndef AXI_MEMORY_MODEL
   initial begin
      r = $value$plusargs("HDKDIR=%s", hdk_name);
      $display("Value is %0s", hdk_name);
   end
   
`ifndef QUESTA_SIM
 `ifndef IES_SIM
   //------------------------------------------------------
   // Turn off warnings from DDR models
   //------------------------------------------------------
   initial begin
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[0].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[1].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[2].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[3].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[4].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[5].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[6].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[7].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[8].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[9].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[10].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[11].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[12].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[13].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[14].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[15].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[16].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[17].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);

      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[0].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[1].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[2].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[3].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[4].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[5].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[6].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[7].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[8].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[9].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[10].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[11].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[12].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[13].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[14].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[15].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[16].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[17].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);

      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[0].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[1].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[2].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[3].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[4].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[5].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[6].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[7].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[8].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[9].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[10].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[11].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[12].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[13].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[14].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[15].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[16].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[17].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);

      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[0].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[1].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[2].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[3].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[4].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[5].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[6].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[7].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[8].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[9].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[10].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[11].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[12].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[13].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[14].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[15].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[16].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
      u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[17].micron_mem_model.u_ddr4_model.set_memory_warnings(0, 0);
   end // initial begin
  `endif //  `ifndef IES_SIM
 `endif //  `ifndef QUESTA_SIM

  function write_cfg_info_to_file(int ddr_fp);
     $display("File poiter is %d", ddr_fp);
     $fdisplay(ddr_fp, "config 4 8");
  endfunction

  function write_bdr_ld_data_to_file(logic [63:0] axi_addr, logic [511:0] data);
     logic [16:0] row_a, row_b;
     logic [1:0]  bank_a, bank_b;
     logic [9:0]  col_a, col_b;
     logic [1:0] bank_group_a, bank_group_b;
     logic [63:0] data_fp[17:0];
     logic [511:0] data_t;
             
     row_a = axi_addr[33:17];
     col_a = {axi_addr[16:11], axi_addr[8], axi_addr[5:3]};
     bank_a = {axi_addr[10:9]};
     bank_group_a = {axi_addr[7:6]};

     row_b = {row_a[16:14], ~row_a[13], row_a[12], ~row_a[11], row_a[10], ~row_a[9:3], row_a[2:0]};
     col_b = {~col_a[9:3], col_a[2:0]};
     bank_b = ~bank_a;
     bank_group_b = ~bank_group_a;

     for (int i=0 ; i<8; i=i+2) begin
        data_t = data;
        //Each device is 32-bits wide. 64-bit data is loaded as below.
        for (int j=0; j<8; j++) begin
           data_fp[i][(j*4+3) -: 4] = data_t[3:0]; //3-0
           
           data_t = data >> 4;
           data_fp[i+1][(j*4+3) -: 4] = data_t[3:0];//7-4

           data_t = data >> 8;
           data = data_t;
        end // for (int j=0; j<8; j++)
        
        $fdisplay(fp[i], "%0h %0h %0h %0h %h", bank_group_a, bank_a, row_a, col_a, data_fp[i][31:0]);
        $fdisplay(fp[i+1], "%0h %0h %0h %0h %h", bank_group_a, bank_a, row_a, col_a, data_fp[i+1][31:0]);

        $fdisplay(fp[i], "%0h %0h %0h %0h %h", bank_group_b, bank_b, row_b, col_b, data_fp[i][31:0]);
        $fdisplay(fp[i+1], "%0h %0h %0h %0h %h", bank_group_b, bank_b, row_b, col_b, data_fp[i+1][31:0]);
     end

     //ECC 
     $fdisplay(fp[14], "%0h %0h %0h %0h %h", bank_group_a, bank_a, row_a, col_a, 'h0);
     $fdisplay(fp[15], "%0h %0h %0h %0h %h", bank_group_a, bank_a, row_a, col_a, 'h0);

     //ECC
     $fdisplay(fp[14], "%0h %0h %0h %0h %h", bank_group_b, bank_b, row_b, col_b, 'h0);
     $fdisplay(fp[15], "%0h %0h %0h %0h %h", bank_group_b, bank_b, row_b, col_b, 'h0);
     
     for (int i=16 ; i<18; i=i+2) begin
        data_t = data;
        //Each device is 32-bits wide. 64-bit data is loaded as below.
        for (int j=0; j<8; j++) begin
           data_fp[i][(j*4+3) -: 4] = data_t[3:0];

           data_t = data >> 4;
           data_fp[i+1][(j*4+3) -: 4] = data_t[3:0];

           data_t = data >> 8;
           data = data_t;
        end // for (int j=0; j<8; j++)
        $fdisplay(fp[i], "%0h %0h %0h %0h %h", bank_group_a, bank_a, row_a, col_a, data_fp[i][31:0]);
        $fdisplay(fp[i+1], "%0h %0h %0h %0h %h", bank_group_a, bank_a, row_a, col_a, data_fp[i+1][31:0]);

        $fdisplay(fp[i], "%0h %0h %0h %0h %h", bank_group_b, bank_b, row_b, col_b, data_fp[i][31:0]);
        $fdisplay(fp[i+1], "%0h %0h %0h %0h %h", bank_group_b, bank_b, row_b, col_b, data_fp[i+1][31:0]);
     end // for (int i=16 ; i<18; i=i+2)
     
     for (int i=8 ; i<13; i=i+2) begin
        data_t = data;
        //Each device is 32-bits wide. 64-bit data is loaded as below.
        for (int j=0; j<8; j++) begin
           data_fp[i][(j*4+3) -: 4] = data_t[3:0];
           
           data_t = data >> 4;
           data_fp[i+1][(j*4+3) -: 4] = data_t[3:0];

           data_t = data >> 8;
           data = data_t;
        end // for (int j=0; j<8; j++)
        $fdisplay(fp[i], "%0h %0h %0h %0h %h", bank_group_a, bank_a, row_a, col_a, data_fp[i][31:0]);
        $fdisplay(fp[i+1], "%0h %0h %0h %0h %h", bank_group_a, bank_a, row_a, col_a, data_fp[i+1][31:0]);

        $fdisplay(fp[i], "%0h %0h %0h %0h %h", bank_group_b, bank_b, row_b, col_b, data_fp[i][31:0]);
        $fdisplay(fp[i+1], "%0h %0h %0h %0h %h", bank_group_b, bank_b, row_b, col_b, data_fp[i+1][31:0]);
     end // for (int i=8 ; i<13; i=i+2)
     
  endfunction // write_bdr_ld_data_to_file

  function write_bdr_ld_raw_data_to_file(int ddr_file, logic [16:0] row_a, logic [1:0]  bank_a, logic [9:0]  col_a, logic [1:0] bank_group_a, logic [31:0] data);
     $fdisplay(ddr_file, "%0d %0d %0d %0d %h", bank_group_a, bank_a, row_a, col_a, data);
  endfunction // write_bdr_ld_raw_data_to_file
  
  function ddr_bdr_ld(string file_name);
     logic [63:0]  addr;
     logic [511:0] data;
     int           axi_fp;
     int           eof_s;
     int           status;
     // Line buffer
     reg [12*100:1] line;
     int           c;
     
     axi_fp = $fopen(file_name, "r");
     
     for (int i=0; i<18; i++) begin
        ddr_name[i] = $sformatf("%0s/cl/examples/cl_dram_dma/verif/scripts/ddr4_ddr_%0d.mem", hdk_name, i);
        $display("ddr_name is %0s \n", ddr_name[i]);
        fp[i] = $fopen(ddr_name[i], "w");
        if (!fp[i]) begin
           $display("Could not open file %s", ddr_name[i]);
        end
     end
     //Config information for memory. 
     for (int i=0 ; i<18; i++) begin
        write_cfg_info_to_file(fp[i]);
     end
     // Check the first character
     c = $fgetc(axi_fp);
     while (c != `EOF) begin
        status = $ungetc(c, axi_fp);
        //status = $fscanf(axi_fp,"%0h %0h", addr, data);
        status = $fgets(line, axi_fp);
        status = $sscanf(line, "%x %x", addr, data);
        $display("eof_s is %d status is %d \n", eof_s, status);
        $display("addr is %h data is %h \n", addr, data);
        write_bdr_ld_data_to_file(.axi_addr(addr), .data(data));
        c = $fgetc(axi_fp);
     end
     for (int i=0; i<18; i++) begin
        $fclose(fp[i]);
     end
     device_bdr_ld();
  endfunction // ddr_bdr_ld
   
  function device_bdr_ld();
     for (int i=0; i<18; i++) begin
        ddr_name[i] = $sformatf("%0s/cl/examples/cl_dram_dma/verif/scripts/ddr4_ddr_%0d.mem", hdk_name, i);
        $display("ddr_name is %s \n", ddr_name[i]);
     end
 `ifndef DDR_A_ABSENT
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[0].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[0]);
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[1].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[1]);
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[2].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[2]);
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[3].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[3]);
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[4].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[4]);
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[5].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[5]);
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[6].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[6]);
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[7].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[7]);
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[8].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[8]);
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[9].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[9]);
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[10].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[10]);
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[11].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[11]);
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[12].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[12]);
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[13].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[13]);
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[14].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[14]);
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[15].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[15]);
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[16].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[16]);
     u_ddr4_rdimm_A.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[17].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[17]);
`endif //  `ifndef DDR_A_ABSENT

`ifndef DDR_B_ABSENT     
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[0].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[0]);
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[1].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[1]);
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[2].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[2]);
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[3].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[3]);
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[4].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[4]);
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[5].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[5]);
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[6].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[6]);
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[7].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[7]);
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[8].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[8]);
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[9].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[9]);
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[10].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[10]);
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[11].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[11]);
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[12].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[12]);
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[13].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[13]);
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[14].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[14]);
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[15].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[15]);
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[16].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[16]);
     u_ddr4_rdimm_B.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[17].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[17]);
`endif //  `ifndef DDR_B_ABSENT

`ifndef DDR_C_ABSENT     
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[0].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[0]);
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[1].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[1]);
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[2].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[2]);
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[3].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[3]);
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[4].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[4]);
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[5].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[5]);
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[6].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[6]);
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[7].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[7]);
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[8].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[8]);
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[9].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[9]);
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[10].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[10]);
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[11].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[11]);
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[12].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[12]);
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[13].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[13]);
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[14].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[14]);
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[15].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[15]);
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[16].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[16]);
     u_ddr4_rdimm_C.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[17].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[17]);
`endif //  `ifndef DDR_C_ABSENT

`ifndef DDR_D_ABSENT     
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[0].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[0]);
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[1].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[1]);
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[2].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[2]);
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[3].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[3]);
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[4].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[4]);
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[5].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[5]);
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[6].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[6]);
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[7].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[7]);
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[8].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[8]);
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[9].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[9]);
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[10].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[10]);
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[11].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[11]);
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[12].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[12]);
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[13].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[13]);
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[14].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[14]);
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[15].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[15]);
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[16].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[16]);
     u_ddr4_rdimm_D.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[17].micron_mem_model.u_ddr4_model.initialize_memory_with_file(ddr_name[17]);
`endif //  `ifndef DDR_D_ABSENT

  endfunction // device_bdr_ld

  //===========================================================================
  //                         Memory Model instantiation
  //===========================================================================

  ddr4_rdimm_wrapper #(
             .MC_DQ_WIDTH(DQ_WIDTH),
             .MC_DQS_BITS(DQS_WIDTH),
             .MC_DM_WIDTH(DM_WIDTH_RDIMM),
             .MC_CKE_NUM(CKE_WIDTH_RDIMM),
             .MC_ODT_WIDTH(ODT_WIDTH_RDIMM),
             .MC_ABITS(ADDR_WIDTH),
             .MC_BANK_WIDTH(BANK_WIDTH_RDIMM),
             .MC_BANK_GROUP(BANK_GROUP_WIDTH_RDIMM),
             .MC_CS_NUM(CS_WIDTH_RDIMM),
             .MC_RANKS_NUM(RANK_WIDTH_RDIMM),
             .NUM_PHYSICAL_PARTS(NUM_PHYSICAL_PARTS),
             .CALIB_EN("NO"),
             .tCK(tCK),
             .tPDM(),
             .MIN_TOTAL_R2R_DELAY(),
             .MAX_TOTAL_R2R_DELAY(),
             .TOTAL_FBT_DELAY(),
             .MEM_PART_WIDTH(MEM_PART_WIDTH),
             .MC_CA_MIRROR(CA_MIRROR),
            // .SDRAM("DDR4"),
   `ifdef SAMSUNG
             .DDR_SIM_MODEL("SAMSUNG"),

   `else
             .DDR_SIM_MODEL("MICRON"),
   `endif
             .DM_DBI(DM_DBI),
             .MC_REG_CTRL(REG_CTRL),
             .DIMM_MODEL ("RDIMM"),
             .RDIMM_SLOTS (RDIMM_SLOTS)

                               )
           u_ddr4_rdimm_A  (
                                  .ddr4_act_n(M_A_ACT_N),
                                  .ddr4_addr(M_A_MA),
                                  .ddr4_ba(M_A_BA),
                                  .ddr4_bg(M_A_BG),
                                  .ddr4_par(M_A_PAR),
                                  .ddr4_cke(M_A_CKE),
                                  .ddr4_odt(M_A_ODT),
                                  .ddr4_cs_n(M_A_CS_N),
                                  .ddr4_ck_t(M_A_CLK_DP),
                                  .ddr4_ck_c(M_A_CLK_DN),
                                  .ddr4_reset_n(RST_DIMM_C_N),
                                  .ddr4_dm_dbi_n(),
                                  .ddr4_dq({M_A_ECC, M_A_DQ}),
                                  .ddr4_dqs_t(M_A_DQS_DP),
                                  .ddr4_dqs_c(M_A_DQS_DN),
                                  .ddr4_alert_n(),
                                  .initDone(),
                                  .scl(),
                                  .sa0(),
                                  .sa1(),
                                  .sa2(),
                                  .sda(),
                                  .bfunc(),
                                  .vddspd());

  ddr4_rdimm_wrapper #(
             .MC_DQ_WIDTH(DQ_WIDTH),
             .MC_DQS_BITS(DQS_WIDTH),
             .MC_DM_WIDTH(DM_WIDTH_RDIMM),
             .MC_CKE_NUM(CKE_WIDTH_RDIMM),
             .MC_ODT_WIDTH(ODT_WIDTH_RDIMM),
             .MC_ABITS(ADDR_WIDTH),
             .MC_BANK_WIDTH(BANK_WIDTH_RDIMM),
             .MC_BANK_GROUP(BANK_GROUP_WIDTH_RDIMM),
             .MC_CS_NUM(CS_WIDTH_RDIMM),
             .MC_RANKS_NUM(RANK_WIDTH_RDIMM),
             .NUM_PHYSICAL_PARTS(NUM_PHYSICAL_PARTS),
             .CALIB_EN("NO"),
             .tCK(tCK),
             .tPDM(),
             .MIN_TOTAL_R2R_DELAY(),
             .MAX_TOTAL_R2R_DELAY(),
             .TOTAL_FBT_DELAY(),
             .MEM_PART_WIDTH(MEM_PART_WIDTH),
             .MC_CA_MIRROR(CA_MIRROR),
            // .SDRAM("DDR4"),
   `ifdef SAMSUNG
             .DDR_SIM_MODEL("SAMSUNG"),

   `else
             .DDR_SIM_MODEL("MICRON"),
   `endif
             .DM_DBI(DM_DBI),
             .MC_REG_CTRL(REG_CTRL),
             .DIMM_MODEL ("RDIMM"),
             .RDIMM_SLOTS (RDIMM_SLOTS)

                               )
           u_ddr4_rdimm_B  (
                                  .ddr4_act_n(M_B_ACT_N),
                                  .ddr4_addr(M_B_MA),
                                  .ddr4_ba(M_B_BA),
                                  .ddr4_bg(M_B_BG),
                                  .ddr4_par(M_B_PAR),
                                  .ddr4_cke(M_B_CKE),
                                  .ddr4_odt(M_B_ODT),
                                  .ddr4_cs_n(M_B_CS_N),
                                  .ddr4_ck_t(M_B_CLK_DP),
                                  .ddr4_ck_c(M_B_CLK_DN),
                                  .ddr4_reset_n(RST_DIMM_C_N),
                                  .ddr4_dm_dbi_n(),
                                  .ddr4_dq({M_B_ECC, M_B_DQ}),
                                  .ddr4_dqs_t(M_B_DQS_DP),
                                  .ddr4_dqs_c(M_B_DQS_DN),
                                  .ddr4_alert_n(),
                                  .initDone(),
                                  .scl(),
                                  .sa0(),
                                  .sa1(),
                                  .sa2(),
                                  .sda(),
                                  .bfunc(),
                                  .vddspd());


  ddr4_rdimm_wrapper #(
             .MC_DQ_WIDTH(DQ_WIDTH),
             .MC_DQS_BITS(DQS_WIDTH),
             .MC_DM_WIDTH(DM_WIDTH_RDIMM),
             .MC_CKE_NUM(CKE_WIDTH_RDIMM),
             .MC_ODT_WIDTH(ODT_WIDTH_RDIMM),
             .MC_ABITS(ADDR_WIDTH),
             .MC_BANK_WIDTH(BANK_WIDTH_RDIMM),
             .MC_BANK_GROUP(BANK_GROUP_WIDTH_RDIMM),
             .MC_CS_NUM(CS_WIDTH_RDIMM),
             .MC_RANKS_NUM(RANK_WIDTH_RDIMM),
             .NUM_PHYSICAL_PARTS(NUM_PHYSICAL_PARTS),
             .CALIB_EN("NO"),
             .tCK(tCK),
             .tPDM(),
             .MIN_TOTAL_R2R_DELAY(),
             .MAX_TOTAL_R2R_DELAY(),
             .TOTAL_FBT_DELAY(),
             .MEM_PART_WIDTH(MEM_PART_WIDTH),
             .MC_CA_MIRROR(CA_MIRROR),
            // .SDRAM("DDR4"),
   `ifdef SAMSUNG
             .DDR_SIM_MODEL("SAMSUNG"),

   `else
             .DDR_SIM_MODEL("MICRON"),
   `endif
             .DM_DBI(DM_DBI),
             .MC_REG_CTRL(REG_CTRL),
             .DIMM_MODEL ("RDIMM"),
             .RDIMM_SLOTS (RDIMM_SLOTS)

                               )
           u_ddr4_rdimm_C  (
                                  .ddr4_act_n(M_C_ACT_N),
                                  .ddr4_addr(M_C_MA),
                                  .ddr4_ba(M_C_BA),
                                  .ddr4_bg(M_C_BG),
                                  .ddr4_par(M_C_PAR),
                                  .ddr4_cke(M_C_CKE),
                                  .ddr4_odt(M_C_ODT),
                                  .ddr4_cs_n(M_C_CS_N),
                                  .ddr4_ck_t(M_C_CLK_DP),
                                  .ddr4_ck_c(M_C_CLK_DN),
                                  .ddr4_reset_n(RST_DIMM_C_N),
                                  .ddr4_dm_dbi_n(),
                                  .ddr4_dq({M_C_ECC, M_C_DQ}),
                                  .ddr4_dqs_t(M_C_DQS_DP),
                                  .ddr4_dqs_c(M_C_DQS_DN),
                                  .ddr4_alert_n(),
                                  .initDone(),
                                  .scl(),
                                  .sa0(),
                                  .sa1(),
                                  .sa2(),
                                  .sda(),
                                  .bfunc(),
                                  .vddspd());

  ddr4_rdimm_wrapper #(
             .MC_DQ_WIDTH(DQ_WIDTH),
             .MC_DQS_BITS(DQS_WIDTH),
             .MC_DM_WIDTH(DM_WIDTH_RDIMM),
             .MC_CKE_NUM(CKE_WIDTH_RDIMM),
             .MC_ODT_WIDTH(ODT_WIDTH_RDIMM),
             .MC_ABITS(ADDR_WIDTH),
             .MC_BANK_WIDTH(BANK_WIDTH_RDIMM),
             .MC_BANK_GROUP(BANK_GROUP_WIDTH_RDIMM),
             .MC_CS_NUM(CS_WIDTH_RDIMM),
             .MC_RANKS_NUM(RANK_WIDTH_RDIMM),
             .NUM_PHYSICAL_PARTS(NUM_PHYSICAL_PARTS),
             .CALIB_EN("NO"),
             .tCK(tCK),
             .tPDM(),
             .MIN_TOTAL_R2R_DELAY(),
             .MAX_TOTAL_R2R_DELAY(),
             .TOTAL_FBT_DELAY(),
             .MEM_PART_WIDTH(MEM_PART_WIDTH),
             .MC_CA_MIRROR(CA_MIRROR),
            // .SDRAM("DDR4"),
   `ifdef SAMSUNG
             .DDR_SIM_MODEL("SAMSUNG"),

   `else
             .DDR_SIM_MODEL("MICRON"),
   `endif
             .DM_DBI(DM_DBI),
             .MC_REG_CTRL(REG_CTRL),
             .DIMM_MODEL ("RDIMM"),
             .RDIMM_SLOTS (RDIMM_SLOTS)

                               )
           u_ddr4_rdimm_D  (
                                  .ddr4_act_n(M_D_ACT_N),
                                  .ddr4_addr(M_D_MA),
                                  .ddr4_ba(M_D_BA),
                                  .ddr4_bg(M_D_BG),
                                  .ddr4_par(M_D_PAR),
                                  .ddr4_cke(M_D_CKE),
                                  .ddr4_odt(M_D_ODT),
                                  .ddr4_cs_n(M_D_CS_N),
                                  .ddr4_ck_t(M_D_CLK_DP),
                                  .ddr4_ck_c(M_D_CLK_DN),
                                  .ddr4_reset_n(RST_DIMM_C_N),
                                  .ddr4_dm_dbi_n(),
                                  .ddr4_dq({M_D_ECC, M_D_DQ}),
                                  .ddr4_dqs_t(M_D_DQS_DP),
                                  .ddr4_dqs_c(M_D_DQS_DN),
                                  .ddr4_alert_n(),
                                  .initDone(),
                                  .scl(),
                                  .sa0(),
                                  .sa1(),
                                  .sa2(),
                                  .sda(),
                                  .bfunc(),
                                  .vddspd());

`endif
