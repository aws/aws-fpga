// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

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
   assign CLK_300M_DIMM3_DP =  ddr_clk;
   assign CLK_300M_DIMM3_DN = ~ddr_clk;

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
                                  .ddr4_ck_t(CLK_300M_DIMM0_DP),
                                  .ddr4_ck_c(CLK_300M_DIMM0_DN),
                                  .ddr4_reset_n(RST_DIMM_A_N),
                                  .ddr4_dm_dbi_n(),
                                  .ddr4_dq(M_A_DQ),
                                  .ddr4_dqs_t(M_A_DQS_DP),
                                  .ddr4_dqs_c(M_A_DQS_DP),
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
                                  .ddr4_ck_t(CLK_300M_DIMM1_DP),
                                  .ddr4_ck_c(CLK_300M_DIMM1_DN),
                                  .ddr4_reset_n(),
                                  .ddr4_dm_dbi_n(),
                                  .ddr4_dq(M_B_DQ),
                                  .ddr4_dqs_t(M_B_DQS_DP),
                                  .ddr4_dqs_c(M_B_DQS_DP),
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
                                  .ddr4_ck_t(CLK_300M_DIMM3_DP),
                                  .ddr4_ck_c(CLK_300M_DIMM3_DN),
                                  .ddr4_reset_n(),
                                  .ddr4_dm_dbi_n(),
                                  .ddr4_dq(M_D_DQ),
                                  .ddr4_dqs_t(M_D_DQS_DP),
                                  .ddr4_dqs_c(M_D_DQS_DP),
                                  .ddr4_alert_n(),
                                  .initDone(),
                                  .scl(),
                                  .sa0(),
                                  .sa1(),
                                  .sa2(),
                                  .sda(),
                                  .bfunc(),
                                  .vddspd());

