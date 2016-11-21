// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

//--------------------------------------------------------------------------------
// Stats interface registers
//Register MAP
// 0x00 - GPIO 0 - read/write scratchpad
// 0x04 - GPIO 1 - read/write scratchpad
// 0x08 - DDR is ready status (bit 0)
// 0x0c - DDR reset (bit 0).  Set to drive reset to the DDR core.
// 0x10 - AXI Address - AXI Address for accessing DDR core (refer to Xilinx DDR specification - pg150)
// 0x14 - AXI Data - AXI Data access for accessing DDR core.  Read or write this register
//                   to read or write the Xilinx DDR controller registers.
// 0x20 - Write Words Low - Stats, number of words written (512-bit words).  Write to clear.  note is 64-bit counter
// 0x24 - Write Words High - Note can write either register to clear entire 64-bits
// 0x28 - Read Words Low - Stats, number of read words writen (512-bit words).  Write to clear
// 0x2c - Read Words High
//
// Interrupt Status0 - bit0: AXI-Lite interrupt from DDR core (refer to Xilinx DDR specification - pg150)


//--------------------------------------------------------------------------------

module sh_ddr #( parameter NUM_DDR = 3)
   (

   //---------------------------
   // Main clock/reset
   //---------------------------
   input clk,
   input rst_n,

   //--------------------------
   // DDR Physical Interface
   //--------------------------

// ------------------- DDR4 x72 RDIMM 2100 Interface A ----------------------------------
    input                CLK_300M_DIMM0_DP,
    input                CLK_300M_DIMM0_DN,
    output logic         M_A_ACT_N,
    output logic[16:0]   M_A_MA,
    output logic[1:0]    M_A_BA,
    output logic[1:0]    M_A_BG,
    output logic[0:0]    M_A_CKE,
    output logic[0:0]    M_A_ODT,
    output logic[0:0]    M_A_CS_N,
    output logic[0:0]    M_A_CLK_DN,
    output logic[0:0]    M_A_CLK_DP,
    output logic         RST_DIMM_A_N,
    output logic         M_A_PAR,
    inout  [63:0]        M_A_DQ,
    inout  [7:0]         M_A_ECC,
    inout  [17:0]        M_A_DQS_DP,
    inout  [17:0]        M_A_DQS_DN,

// ------------------- DDR4 x72 RDIMM 2100 Interface B ----------------------------------
    input                CLK_300M_DIMM1_DP,
    input                CLK_300M_DIMM1_DN,
    output logic         M_B_ACT_N,
    output logic[16:0]   M_B_MA,
    output logic[1:0]    M_B_BA,
    output logic[1:0]    M_B_BG,
    output logic[0:0]    M_B_CKE,
    output logic[0:0]    M_B_ODT,
    output logic[0:0]    M_B_CS_N,
    output logic[0:0]    M_B_CLK_DN,
    output logic[0:0]    M_B_CLK_DP,
    output logic         RST_DIMM_B_N,
    output logic         M_B_PAR,
    inout  [63:0]        M_B_DQ,
    inout  [7:0]         M_B_ECC,
    inout  [17:0]        M_B_DQS_DP,
    inout  [17:0]        M_B_DQS_DN,

// ------------------- DDR4 x72 RDIMM 2100 Interface C ----------------------------------
    input                CLK_300M_DIMM2_DP,
    input                CLK_300M_DIMM2_DN,
    output logic         M_C_ACT_N,
    output logic[16:0]   M_C_MA,
    output logic[1:0]    M_C_BA,
    output logic[1:0]    M_C_BG,
    output logic[0:0]    M_C_CKE,
    output logic[0:0]    M_C_ODT,
    output logic[0:0]    M_C_CS_N,
    output logic[0:0]    M_C_CLK_DN,
    output logic[0:0]    M_C_CLK_DP,
    output logic         RST_DIMM_C_N,
    output logic         M_C_PAR,
    inout  [63:0]        M_C_DQ,
    inout  [7:0]         M_C_ECC,
    inout  [17:0]        M_C_DQS_DP,
    inout  [17:0]        M_C_DQS_DN,

// ------------------- DDR4 x72 RDIMM 2100 Interface D ----------------------------------
    input                CLK_300M_DIMM3_DP,
    input                CLK_300M_DIMM3_DN,
    output logic         M_D_ACT_N,
    output logic[16:0]   M_D_MA,
    output logic[1:0]    M_D_BA,
    output logic[1:0]    M_D_BG,
    output logic[0:0]    M_D_CKE,
    output logic[0:0]    M_D_ODT,
    output logic[0:0]    M_D_CS_N,
    output logic[0:0]    M_D_CLK_DN,
    output logic[0:0]    M_D_CLK_DP,
    output logic         RST_DIMM_D_N,
    output logic         M_D_PAR,
    inout  [63:0]        M_D_DQ,
    inout  [7:0]         M_D_ECC,
    inout  [17:0]        M_D_DQS_DP,
    inout  [17:0]        M_D_DQS_DN,


   //------------------------------------------------------
   // DDR-4 Interface from CL (AXI-4)
   //------------------------------------------------------
   input[5:0] cl_sh_ddr_awid[NUM_DDR-1:0],
   input[63:0] cl_sh_ddr_awaddr[NUM_DDR-1:0],
   input[7:0] cl_sh_ddr_awlen[NUM_DDR-1:0],
   //input[10:0] cl_sh_ddr_awuser[NUM_DDR-1:0],
   input cl_sh_ddr_awvalid[NUM_DDR-1:0],
   output logic[NUM_DDR-1:0] sh_cl_ddr_awready,

   input[5:0] cl_sh_ddr_wid[NUM_DDR-1:0],
   input[511:0] cl_sh_ddr_wdata[NUM_DDR-1:0],
   input[63:0] cl_sh_ddr_wstrb[NUM_DDR-1:0],
   input[NUM_DDR-1:0] cl_sh_ddr_wlast,
   input[NUM_DDR-1:0] cl_sh_ddr_wvalid,
   output logic[NUM_DDR-1:0] sh_cl_ddr_wready,

   output logic[5:0] sh_cl_ddr_bid[NUM_DDR-1:0],
   output logic[1:0] sh_cl_ddr_bresp[NUM_DDR-1:0],
   output logic[NUM_DDR-1:0] sh_cl_ddr_bvalid,
   input[NUM_DDR-1:0] cl_sh_ddr_bready,

   input[5:0] cl_sh_ddr_arid[NUM_DDR-1:0],
   input[63:0] cl_sh_ddr_araddr[NUM_DDR-1:0],
   input[7:0] cl_sh_ddr_arlen[NUM_DDR-1:0],
   //input[10:0] cl_sh_ddr_aruser[NUM_DDR-1:0],
   input[NUM_DDR-1:0] cl_sh_ddr_arvalid,
   output logic[NUM_DDR-1:0] sh_cl_ddr_arready,

   output logic[5:0] sh_cl_ddr_rid[NUM_DDR-1:0],
   output logic[511:0] sh_cl_ddr_rdata[NUM_DDR-1:0],
   output logic[1:0] sh_cl_ddr_rresp[NUM_DDR-1:0],
   output logic[NUM_DDR-1:0] sh_cl_ddr_rlast,
   output logic[NUM_DDR-1:0] sh_cl_ddr_rvalid,
   input[NUM_DDR-1:0] cl_sh_ddr_rready,

   output logic[NUM_DDR-1:0] sh_cl_ddr_is_ready,

   input[7:0] sh_ddr_stat_addr[2:0],
   input[2:0] sh_ddr_stat_wr,
   input[2:0] sh_ddr_stat_rd,
   input[31:0] sh_ddr_stat_wdata[2:0],

   output logic[2:0] ddr_sh_stat_ack,
   output logic[31:0] ddr_sh_stat_rdata[2:0],
   output logic[7:0] ddr_sh_stat_int[2:0]
   );

//-------------------------------------------
// Internal signals
//-------------------------------------------

//--------------------------------------------------------
// DDR4 AXI interafaces to core (sync to DDR clock)
//--------------------------------------------------------
logic[5:0] sync_cl_sh_ddr_awid[NUM_DDR-1:0];
logic[63:0] sync_cl_sh_ddr_awaddr[NUM_DDR-1:0];
logic[7:0] sync_cl_sh_ddr_awlen[NUM_DDR-1:0];
logic sync_cl_sh_ddr_awvalid[NUM_DDR-1:0];
logic[NUM_DDR-1:0] sync_sh_cl_ddr_awready;

logic[5:0] sync_cl_sh_ddr_wid[NUM_DDR-1:0];
logic[511:0] sync_cl_sh_ddr_wdata[NUM_DDR-1:0];
logic[63:0] sync_cl_sh_ddr_wstrb[NUM_DDR-1:0];
logic[NUM_DDR-1:0] sync_cl_sh_ddr_wlast;
logic[NUM_DDR-1:0] sync_cl_sh_ddr_wvalid;
logic[NUM_DDR-1:0] sync_sh_cl_ddr_wready;

logic[5:0] sync_sh_cl_ddr_bid[NUM_DDR-1:0];
logic[1:0] sync_sh_cl_ddr_bresp[NUM_DDR-1:0];
logic[NUM_DDR-1:0] sync_sh_cl_ddr_bvalid;
logic[NUM_DDR-1:0] sync_cl_sh_ddr_bready;

logic[5:0] sync_cl_sh_ddr_arid[NUM_DDR-1:0];
logic[63:0] sync_cl_sh_ddr_araddr[NUM_DDR-1:0];
logic[7:0] sync_cl_sh_ddr_arlen[NUM_DDR-1:0];
logic[NUM_DDR-1:0] sync_cl_sh_ddr_arvalid;
logic[NUM_DDR-1:0] sync_sh_cl_ddr_arready;

logic[5:0] sync_sh_cl_ddr_rid[NUM_DDR-1:0];
logic[511:0] sync_sh_cl_ddr_rdata[NUM_DDR-1:0];
logic[1:0] sync_sh_cl_ddr_rresp[NUM_DDR-1:0];
logic[NUM_DDR-1:0] sync_sh_cl_ddr_rlast;
logic[NUM_DDR-1:0] sync_sh_cl_ddr_rvalid;
logic[NUM_DDR-1:0] sync_cl_sh_ddr_rready;

logic[NUM_DDR-1:0] ddr_user_rst_n;
logic[NUM_DDR-1:0] ddr_user_clk;
logic[NUM_DDR-1:0] ddr_user_rst;

logic[NUM_DDR-1:0] axl_awvalid;
logic[NUM_DDR-1:0] axl_awready;
logic[31:0] axl_awaddr[NUM_DDR-1:0];
logic[NUM_DDR-1:0] axl_wvalid;
logic[NUM_DDR-1:0] axl_wready;
logic[31:0] axl_wdata[NUM_DDR-1:0];
logic[NUM_DDR-1:0] axl_bvalid;
logic[NUM_DDR-1:0] axl_bready;
logic[1:0] axl_bresp[NUM_DDR-1:0];
logic[NUM_DDR-1:0] axl_arvalid;
logic[NUM_DDR-1:0] axl_arready;
logic[31:0] axl_araddr[NUM_DDR-1:0];
logic[NUM_DDR-1:0] axl_rvalid;
logic[NUM_DDR-1:0] axl_rready;
logic[31:0] axl_rdata[NUM_DDR-1:0];
logic[1:0] axl_rresp[NUM_DDR-1:0];
logic[NUM_DDR-1:0] axl_interrupt;

logic[NUM_DDR-1:0] clk_axl_awvalid;
logic[NUM_DDR-1:0] clk_axl_awready;
logic[31:0] clk_axl_awaddr[NUM_DDR-1:0];
logic[NUM_DDR-1:0] clk_axl_wvalid;
logic[NUM_DDR-1:0] clk_axl_wready;
logic[31:0] clk_axl_wdata[NUM_DDR-1:0];
logic[NUM_DDR-1:0] clk_axl_bvalid;
logic[NUM_DDR-1:0] clk_axl_bready;
logic[1:0] clk_axl_bresp[NUM_DDR-1:0];
logic[NUM_DDR-1:0] clk_axl_arvalid;
logic[NUM_DDR-1:0] clk_axl_arready;
logic[31:0] clk_axl_araddr[NUM_DDR-1:0];
logic[NUM_DDR-1:0] clk_axl_rvalid;
logic[NUM_DDR-1:0] clk_axl_rready;
logic[31:0] clk_axl_rdata[NUM_DDR-1:0];
logic[1:0] clk_axl_rresp[NUM_DDR-1:0];
logic[NUM_DDR-1:0] clk_axl_interrupt;

   
// End internal signals
//----------------------------

assign ddr_user_rst_n = ~ddr_user_rst;

logic[NUM_DDR-1:0] ddr_rst_n;
logic[NUM_DDR-1:0] ddr_sw_rst = 0;

assign ddr_rst_n = ~({NUM_DDR{~rst_n}} | ddr_sw_rst);

`ifndef NO_DDR
//----------------------------------------------------------
// DDR Controllers
//----------------------------------------------------------
generate
begin
   for (genvar gi=0; gi<NUM_DDR; gi++)
   begin:ddr_inst

         axi4_ccf #(.ADDR_WIDTH(64), .DATA_WIDTH(512), .ID_WIDTH(6), .A_USER_WIDTH(1), .FIFO_ADDR_WIDTH(3)) AXI_CCF (
            .s_axi_aclk(clk),
            .s_axi_aresetn(ddr_rst_n[gi]),

            .s_axi_awid(cl_sh_ddr_awid[gi]),
            .s_axi_awaddr(cl_sh_ddr_awaddr[gi]),
            .s_axi_awlen(cl_sh_ddr_awlen[gi]),
            .s_axi_awuser(1'b0),
            .s_axi_awvalid(cl_sh_ddr_awvalid[gi]),
            .s_axi_awready(sh_cl_ddr_awready[gi]),

            .s_axi_wdata(cl_sh_ddr_wdata[gi]),
            .s_axi_wstrb(cl_sh_ddr_wstrb[gi]),
            .s_axi_wlast(cl_sh_ddr_wlast[gi]),
            .s_axi_wvalid(cl_sh_ddr_wvalid[gi]),
            .s_axi_wuser(),
            .s_axi_wready(sh_cl_ddr_wready[gi]),
   
            .s_axi_bid(sh_cl_ddr_bid[gi]),
            .s_axi_bresp(sh_cl_ddr_bresp[gi]),
            .s_axi_buser(),
            .s_axi_bvalid(sh_cl_ddr_bvalid[gi]),
            .s_axi_bready(cl_sh_ddr_bready[gi]),

            .s_axi_arid(cl_sh_ddr_arid[gi]),
            .s_axi_araddr(cl_sh_ddr_araddr[gi]),
            .s_axi_arlen(cl_sh_ddr_arlen[gi]),
            .s_axi_aruser(1'b0),
            .s_axi_arvalid(cl_sh_ddr_arvalid[gi]),
            .s_axi_arready(sh_cl_ddr_arready[gi]),

            .s_axi_rid(sh_cl_ddr_rid[gi]),
            .s_axi_rdata(sh_cl_ddr_rdata[gi]),
            .s_axi_rresp(sh_cl_ddr_rresp[gi]),
            .s_axi_rlast(sh_cl_ddr_rlast[gi]),
            .s_axi_ruser(),
            .s_axi_rvalid(sh_cl_ddr_rvalid[gi]),
            .s_axi_rready(cl_sh_ddr_rready[gi]),

            .m_axi_aclk(ddr_user_clk[gi]),
            .m_axi_aresetn(ddr_user_rst_n[gi]),

            .m_axi_awid(sync_cl_sh_ddr_awid[gi]),
            .m_axi_awaddr(sync_cl_sh_ddr_awaddr[gi]),
            .m_axi_awlen(sync_cl_sh_ddr_awlen[gi]),
            .m_axi_awuser(),
            .m_axi_awvalid(sync_cl_sh_ddr_awvalid[gi]),
            .m_axi_awready(sync_sh_cl_ddr_awready[gi]),

            .m_axi_wdata(sync_cl_sh_ddr_wdata[gi]),
            .m_axi_wstrb(sync_cl_sh_ddr_wstrb[gi]),
            .m_axi_wlast(sync_cl_sh_ddr_wlast[gi]),
            .m_axi_wuser(),
            .m_axi_wvalid(sync_cl_sh_ddr_wvalid[gi]),
            .m_axi_wready(sync_sh_cl_ddr_wready[gi]),
   
            .m_axi_bid(sync_sh_cl_ddr_bid[gi]),
            .m_axi_bresp(sync_sh_cl_ddr_bresp[gi]),
            .m_axi_buser(),
            .m_axi_bvalid(sync_sh_cl_ddr_bvalid[gi]),
            .m_axi_bready(sync_cl_sh_ddr_bready[gi]),

            .m_axi_arid(sync_cl_sh_ddr_arid[gi]),
            .m_axi_araddr(sync_cl_sh_ddr_araddr[gi]),
            .m_axi_arlen(sync_cl_sh_ddr_arlen[gi]),
            .m_axi_aruser(),
            .m_axi_arvalid(sync_cl_sh_ddr_arvalid[gi]),
            .m_axi_arready(sync_sh_cl_ddr_arready[gi]),

            .m_axi_rid(sync_sh_cl_ddr_rid[gi]),
            .m_axi_rdata(sync_sh_cl_ddr_rdata[gi]),
            .m_axi_rresp(sync_sh_cl_ddr_rresp[gi]),
            .m_axi_rlast(sync_sh_cl_ddr_rlast[gi]),
            .m_axi_ruser(),
            .m_axi_rvalid(sync_sh_cl_ddr_rvalid[gi]),
            .m_axi_rready(sync_cl_sh_ddr_rready[gi])
         );


   end
end
endgenerate


generate
begin:ddr_cores
   if (NUM_DDR>=1)
   begin
      //--------------------
      // DDR 0
      //--------------------
      ddr4_core DDR4_0 (
         .sys_rst(~ddr_rst_n[0]),
         .c0_sys_clk_p(CLK_300M_DIMM0_DP),
         .c0_sys_clk_n(CLK_300M_DIMM0_DN),
         .c0_ddr4_act_n(M_A_ACT_N),
         .c0_ddr4_adr(M_A_MA),
         .c0_ddr4_ba(M_A_BA),
         .c0_ddr4_bg(M_A_BG),
         .c0_ddr4_cke(M_A_CKE),
         .c0_ddr4_odt(M_A_ODT),
         .c0_ddr4_cs_n(M_A_CS_N),
         .c0_ddr4_ck_t(M_A_CLK_DP),
         .c0_ddr4_ck_c(M_A_CLK_DN),
         .c0_ddr4_reset_n(RST_DIMM_A_N),
         .c0_ddr4_parity(M_A_PAR),
      
         //.c0_ddr4_dq({M_A_ECC, M_A_DQ}),
         //.c0_ddr4_dqs_c(M_A_DQS_DN),
         //.c0_ddr4_dqs_t(M_A_DQS_DP),
         .c0_ddr4_dq({M_A_DQ[63:32], M_A_ECC, M_A_DQ[31:0]}),
         .c0_ddr4_dqs_t({M_A_DQS_DP[16],M_A_DQS_DP[7], M_A_DQS_DP[15],M_A_DQS_DP[6], M_A_DQS_DP[14], M_A_DQS_DP[5], M_A_DQS_DP[13], M_A_DQS_DP[4], M_A_DQS_DP[17], M_A_DQS_DP[8], M_A_DQS_DP[12], M_A_DQS_DP[3], M_A_DQS_DP[11], M_A_DQS_DP[2], M_A_DQS_DP[10], M_A_DQS_DP[1], M_A_DQS_DP[9], M_A_DQS_DP[0]}),
         .c0_ddr4_dqs_c({M_A_DQS_DN[16],M_A_DQS_DN[7], M_A_DQS_DN[15],M_A_DQS_DN[6], M_A_DQS_DN[14], M_A_DQS_DN[5], M_A_DQS_DN[13], M_A_DQS_DN[4], M_A_DQS_DN[17], M_A_DQS_DN[8], M_A_DQS_DN[12], M_A_DQS_DN[3], M_A_DQS_DN[11], M_A_DQS_DN[2], M_A_DQS_DN[10], M_A_DQS_DN[1], M_A_DQS_DN[9], M_A_DQS_DN[0]}),
         .c0_init_calib_complete(sh_cl_ddr_is_ready[0]),
         .c0_ddr4_ui_clk(ddr_user_clk[0]),
         .c0_ddr4_ui_clk_sync_rst(ddr_user_rst[0]),
         .dbg_clk(),                               //No connect
         
         .c0_ddr4_s_axi_ctrl_awvalid(axl_awvalid[0]),
         .c0_ddr4_s_axi_ctrl_awready(axl_awready[0]),
         .c0_ddr4_s_axi_ctrl_awaddr(axl_awaddr[0]),
         .c0_ddr4_s_axi_ctrl_wvalid(axl_wvalid[0]),
         .c0_ddr4_s_axi_ctrl_wready(axl_wready[0]),
         .c0_ddr4_s_axi_ctrl_wdata(axl_wdata[0]),
         .c0_ddr4_s_axi_ctrl_bvalid(axl_bvalid[0]),
         .c0_ddr4_s_axi_ctrl_bready(axl_bready[0]),
         .c0_ddr4_s_axi_ctrl_bresp(axl_bresp[0]),
         .c0_ddr4_s_axi_ctrl_arvalid(axl_arvalid[0]),
         .c0_ddr4_s_axi_ctrl_arready(axl_arready[0]),
         .c0_ddr4_s_axi_ctrl_araddr(axl_araddr[0]),
         .c0_ddr4_s_axi_ctrl_rvalid(axl_rvalid[0]),
         .c0_ddr4_s_axi_ctrl_rready(axl_rready[0]),
         .c0_ddr4_s_axi_ctrl_rdata(axl_rdata[0]),
         .c0_ddr4_s_axi_ctrl_rresp(axl_rresp[0]),
         .c0_ddr4_interrupt(axl_interrupt[0]),
         
         .c0_ddr4_aresetn(ddr_user_rst_n[0]),
         
         .c0_ddr4_s_axi_awid(sync_cl_sh_ddr_awid[0]),
         .c0_ddr4_s_axi_awaddr(sync_cl_sh_ddr_awaddr[0][33:0]),
         .c0_ddr4_s_axi_awlen(sync_cl_sh_ddr_awlen[0]),
         .c0_ddr4_s_axi_awsize(3'h6),
         .c0_ddr4_s_axi_awburst(2'b00),
         .c0_ddr4_s_axi_awlock(1'b0),
         .c0_ddr4_s_axi_awcache(4'h0),    
         .c0_ddr4_s_axi_awprot(3'h0),
         .c0_ddr4_s_axi_awqos(4'h0),
         .c0_ddr4_s_axi_awvalid(sync_cl_sh_ddr_awvalid[0]),
         .c0_ddr4_s_axi_awready(sync_sh_cl_ddr_awready[0]),
         
         .c0_ddr4_s_axi_wdata(sync_cl_sh_ddr_wdata[0]),
         .c0_ddr4_s_axi_wstrb(sync_cl_sh_ddr_wstrb[0]),
         .c0_ddr4_s_axi_wlast(sync_cl_sh_ddr_wlast[0]),
         .c0_ddr4_s_axi_wvalid(sync_cl_sh_ddr_wvalid[0]),
         .c0_ddr4_s_axi_wready(sync_sh_cl_ddr_wready[0]),
         
         .c0_ddr4_s_axi_bready(sync_cl_sh_ddr_bready[0]),
         .c0_ddr4_s_axi_bid(sync_sh_cl_ddr_bid[0]),
         .c0_ddr4_s_axi_bresp(sync_sh_cl_ddr_bresp[0]),
         .c0_ddr4_s_axi_bvalid(sync_sh_cl_ddr_bvalid[0]),
         
         .c0_ddr4_s_axi_arid(sync_cl_sh_ddr_arid[0]),
         .c0_ddr4_s_axi_araddr(sync_cl_sh_ddr_araddr[0][33:0]),
         .c0_ddr4_s_axi_arlen(sync_cl_sh_ddr_arlen[0]),
         .c0_ddr4_s_axi_arsize(3'h6),
         .c0_ddr4_s_axi_arburst(2'b0),
         .c0_ddr4_s_axi_arlock(1'b0),
         .c0_ddr4_s_axi_arcache(4'h0),
         .c0_ddr4_s_axi_arprot(3'h0),
         .c0_ddr4_s_axi_arqos(4'h0),
         .c0_ddr4_s_axi_arvalid(sync_cl_sh_ddr_arvalid[0]),
         .c0_ddr4_s_axi_arready(sync_sh_cl_ddr_arready[0]),
         
         .c0_ddr4_s_axi_rready(sync_cl_sh_ddr_rready[0]),
         .c0_ddr4_s_axi_rid(sync_sh_cl_ddr_rid[0]),
         .c0_ddr4_s_axi_rdata(sync_sh_cl_ddr_rdata[0]),
         .c0_ddr4_s_axi_rresp(sync_sh_cl_ddr_rresp[0]),
         .c0_ddr4_s_axi_rlast(sync_sh_cl_ddr_rlast[0]),
         .c0_ddr4_s_axi_rvalid(sync_sh_cl_ddr_rvalid[0]),
         .dbg_bus()        //No Connect
         );
   end
   else
   begin
      assign sh_cl_ddr_is_ready[0] = 0;
   end

   if (NUM_DDR>=2)
   begin
      //--------------------
      // DDR 1
      //--------------------
      ddr4_core DDR4_1 (
         .sys_rst(~ddr_rst_n[1]),
         .c0_sys_clk_p(CLK_300M_DIMM1_DP),
         .c0_sys_clk_n(CLK_300M_DIMM1_DN),
         .c0_ddr4_act_n(M_B_ACT_N),
         .c0_ddr4_adr(M_B_MA),
         .c0_ddr4_ba(M_B_BA),
         .c0_ddr4_bg(M_B_BG),
         .c0_ddr4_cke(M_B_CKE),
         .c0_ddr4_odt(M_B_ODT),
         .c0_ddr4_cs_n(M_B_CS_N),
         .c0_ddr4_ck_t(M_B_CLK_DP),
         .c0_ddr4_ck_c(M_B_CLK_DN),
         .c0_ddr4_reset_n(RST_DIMM_B_N),
         .c0_ddr4_parity(M_B_PAR),
      
         //.c0_ddr4_dq({M_B_ECC, M_B_DQ}),
         //.c0_ddr4_dqs_c(M_B_DQS_DN),
         //.c0_ddr4_dqs_t(M_B_DQS_DP),
         .c0_ddr4_dq({M_B_DQ[63:32], M_B_ECC, M_B_DQ[31:0]}),
         .c0_ddr4_dqs_t({M_B_DQS_DP[16],M_B_DQS_DP[7], M_B_DQS_DP[15],M_B_DQS_DP[6], M_B_DQS_DP[14], M_B_DQS_DP[5], M_B_DQS_DP[13], M_B_DQS_DP[4], M_B_DQS_DP[17], M_B_DQS_DP[8], M_B_DQS_DP[12], M_B_DQS_DP[3], M_B_DQS_DP[11], M_B_DQS_DP[2], M_B_DQS_DP[10], M_B_DQS_DP[1], M_B_DQS_DP[9], M_B_DQS_DP[0]}),
         .c0_ddr4_dqs_c({M_B_DQS_DN[16],M_B_DQS_DN[7], M_B_DQS_DN[15],M_B_DQS_DN[6], M_B_DQS_DN[14], M_B_DQS_DN[5], M_B_DQS_DN[13], M_B_DQS_DN[4], M_B_DQS_DN[17], M_B_DQS_DN[8], M_B_DQS_DN[12], M_B_DQS_DN[3], M_B_DQS_DN[11], M_B_DQS_DN[2], M_B_DQS_DN[10], M_B_DQS_DN[1], M_B_DQS_DN[9], M_B_DQS_DN[0]}),
      
         .c0_init_calib_complete(sh_cl_ddr_is_ready[1]),
         .c0_ddr4_ui_clk(ddr_user_clk[1]),
         .c0_ddr4_ui_clk_sync_rst(ddr_user_rst[1]),
         .dbg_clk(),                               //No connect

         .c0_ddr4_s_axi_ctrl_awvalid(axl_awvalid[1]),
         .c0_ddr4_s_axi_ctrl_awready(axl_awready[1]),
         .c0_ddr4_s_axi_ctrl_awaddr(axl_awaddr[1]),
         .c0_ddr4_s_axi_ctrl_wvalid(axl_wvalid[1]),
         .c0_ddr4_s_axi_ctrl_wready(axl_wready[1]),
         .c0_ddr4_s_axi_ctrl_wdata(axl_wdata[1]),
         .c0_ddr4_s_axi_ctrl_bvalid(axl_bvalid[1]),
         .c0_ddr4_s_axi_ctrl_bready(axl_bready[1]),
         .c0_ddr4_s_axi_ctrl_bresp(axl_bresp[1]),
         .c0_ddr4_s_axi_ctrl_arvalid(axl_arvalid[1]),
         .c0_ddr4_s_axi_ctrl_arready(axl_arready[1]),
         .c0_ddr4_s_axi_ctrl_araddr(axl_araddr[1]),
         .c0_ddr4_s_axi_ctrl_rvalid(axl_rvalid[1]),
         .c0_ddr4_s_axi_ctrl_rready(axl_rready[1]),
         .c0_ddr4_s_axi_ctrl_rdata(axl_rdata[1]),
         .c0_ddr4_s_axi_ctrl_rresp(axl_rresp[1]),
         .c0_ddr4_interrupt(axl_interrupt[1]),
         
         .c0_ddr4_aresetn(ddr_user_rst_n[1]),
         
         .c0_ddr4_s_axi_awid(sync_cl_sh_ddr_awid[1]),
         .c0_ddr4_s_axi_awaddr(sync_cl_sh_ddr_awaddr[1][33:0]),
         .c0_ddr4_s_axi_awlen(sync_cl_sh_ddr_awlen[1]),
         .c0_ddr4_s_axi_awsize(3'h6),
         .c0_ddr4_s_axi_awburst(2'b00),
         .c0_ddr4_s_axi_awlock(1'b0),
         .c0_ddr4_s_axi_awcache(4'h0),    
         .c0_ddr4_s_axi_awprot(3'h0),
         .c0_ddr4_s_axi_awqos(4'h0),
         .c0_ddr4_s_axi_awvalid(sync_cl_sh_ddr_awvalid[1]),
         .c0_ddr4_s_axi_awready(sync_sh_cl_ddr_awready[1]),
         
         .c0_ddr4_s_axi_wdata(sync_cl_sh_ddr_wdata[1]),
         .c0_ddr4_s_axi_wstrb(sync_cl_sh_ddr_wstrb[1]),
         .c0_ddr4_s_axi_wlast(sync_cl_sh_ddr_wlast[1]),
         .c0_ddr4_s_axi_wvalid(sync_cl_sh_ddr_wvalid[1]),
         .c0_ddr4_s_axi_wready(sync_sh_cl_ddr_wready[1]),
         
         .c0_ddr4_s_axi_bready(sync_cl_sh_ddr_bready[1]),
         .c0_ddr4_s_axi_bid(sync_sh_cl_ddr_bid[1]),
         .c0_ddr4_s_axi_bresp(sync_sh_cl_ddr_bresp[1]),
         .c0_ddr4_s_axi_bvalid(sync_sh_cl_ddr_bvalid[1]),
         
         .c0_ddr4_s_axi_arid(sync_cl_sh_ddr_arid[1]),
         .c0_ddr4_s_axi_araddr(sync_cl_sh_ddr_araddr[1][33:0]),
         .c0_ddr4_s_axi_arlen(sync_cl_sh_ddr_arlen[1]),
         .c0_ddr4_s_axi_arsize(3'h6),
         .c0_ddr4_s_axi_arburst(2'b0),
         .c0_ddr4_s_axi_arlock(1'b0),
         .c0_ddr4_s_axi_arcache(4'h0),
         .c0_ddr4_s_axi_arprot(3'h0),
         .c0_ddr4_s_axi_arqos(4'h0),
         .c0_ddr4_s_axi_arvalid(sync_cl_sh_ddr_arvalid[1]),
         .c0_ddr4_s_axi_arready(sync_sh_cl_ddr_arready[1]),
         
         .c0_ddr4_s_axi_rready(sync_cl_sh_ddr_rready[1]),
         .c0_ddr4_s_axi_rid(sync_sh_cl_ddr_rid[1]),
         .c0_ddr4_s_axi_rdata(sync_sh_cl_ddr_rdata[1]),
         .c0_ddr4_s_axi_rresp(sync_sh_cl_ddr_rresp[1]),
         .c0_ddr4_s_axi_rlast(sync_sh_cl_ddr_rlast[1]),
         .c0_ddr4_s_axi_rvalid(sync_sh_cl_ddr_rvalid[1]),
         .dbg_bus()        //No Connect
         );
   end
   else
   begin
      assign sh_cl_ddr_is_ready[1] = 0;
   end
   
   if (NUM_DDR>=3)
   begin
      //--------------------
      // DDR 2
      //--------------------
      ddr4_core DDR4_2 (
         .sys_rst(~ddr_rst_n[2]),
         .c0_sys_clk_p(CLK_300M_DIMM3_DP),
         .c0_sys_clk_n(CLK_300M_DIMM3_DN),
         .c0_ddr4_act_n(M_D_ACT_N),
         .c0_ddr4_adr(M_D_MA),
         .c0_ddr4_ba(M_D_BA),
         .c0_ddr4_bg(M_D_BG),
         .c0_ddr4_cke(M_D_CKE),
         .c0_ddr4_odt(M_D_ODT),
         .c0_ddr4_cs_n(M_D_CS_N),
         .c0_ddr4_ck_t(M_D_CLK_DP),
         .c0_ddr4_ck_c(M_D_CLK_DN),
         .c0_ddr4_reset_n(RST_DIMM_D_N),
         .c0_ddr4_parity(M_D_PAR),
      
         //.c0_ddr4_dq({M_D_ECC, M_D_DQ}),
         //.c0_ddr4_dqs_c(M_D_DQS_DN),
         //.c0_ddr4_dqs_t(M_D_DQS_DP),
         .c0_ddr4_dq({M_D_DQ[63:32], M_D_ECC, M_D_DQ[31:0]}),
         .c0_ddr4_dqs_t({M_D_DQS_DP[16],M_D_DQS_DP[7], M_D_DQS_DP[15],M_D_DQS_DP[6], M_D_DQS_DP[14], M_D_DQS_DP[5], M_D_DQS_DP[13], M_D_DQS_DP[4], M_D_DQS_DP[17], M_D_DQS_DP[8], M_D_DQS_DP[12], M_D_DQS_DP[3], M_D_DQS_DP[11], M_D_DQS_DP[2], M_D_DQS_DP[10], M_D_DQS_DP[1], M_D_DQS_DP[9], M_D_DQS_DP[0]}),
         .c0_ddr4_dqs_c({M_D_DQS_DN[16],M_D_DQS_DN[7], M_D_DQS_DN[15],M_D_DQS_DN[6], M_D_DQS_DN[14], M_D_DQS_DN[5], M_D_DQS_DN[13], M_D_DQS_DN[4], M_D_DQS_DN[17], M_D_DQS_DN[8], M_D_DQS_DN[12], M_D_DQS_DN[3], M_D_DQS_DN[11], M_D_DQS_DN[2], M_D_DQS_DN[10], M_D_DQS_DN[1], M_D_DQS_DN[9], M_D_DQS_DN[0]}),
      
      
         .c0_init_calib_complete(sh_cl_ddr_is_ready[2]),
         .c0_ddr4_ui_clk(ddr_user_clk[2]),
         .c0_ddr4_ui_clk_sync_rst(ddr_user_rst[2]),
         .dbg_clk(),                               //No connect
         
         .c0_ddr4_s_axi_ctrl_awvalid(axl_awvalid[2]),
         .c0_ddr4_s_axi_ctrl_awready(axl_awready[2]),
         .c0_ddr4_s_axi_ctrl_awaddr(axl_awaddr[2]),
         .c0_ddr4_s_axi_ctrl_wvalid(axl_wvalid[2]),
         .c0_ddr4_s_axi_ctrl_wready(axl_wready[2]),
         .c0_ddr4_s_axi_ctrl_wdata(axl_wdata[2]),
         .c0_ddr4_s_axi_ctrl_bvalid(axl_bvalid[2]),
         .c0_ddr4_s_axi_ctrl_bready(axl_bready[2]),
         .c0_ddr4_s_axi_ctrl_bresp(axl_bresp[2]),
         .c0_ddr4_s_axi_ctrl_arvalid(axl_arvalid[2]),
         .c0_ddr4_s_axi_ctrl_arready(axl_arready[2]),
         .c0_ddr4_s_axi_ctrl_araddr(axl_araddr[2]),
         .c0_ddr4_s_axi_ctrl_rvalid(axl_rvalid[2]),
         .c0_ddr4_s_axi_ctrl_rready(axl_rready[2]),
         .c0_ddr4_s_axi_ctrl_rdata(axl_rdata[2]),
         .c0_ddr4_s_axi_ctrl_rresp(axl_rresp[2]),
         .c0_ddr4_interrupt(axl_interrupt[2]),
         
         .c0_ddr4_aresetn(ddr_user_rst_n[2]),
         
         .c0_ddr4_s_axi_awid(sync_cl_sh_ddr_awid[2]),
         .c0_ddr4_s_axi_awaddr(sync_cl_sh_ddr_awaddr[2][33:0]),
         .c0_ddr4_s_axi_awlen(sync_cl_sh_ddr_awlen[2]),
         .c0_ddr4_s_axi_awsize(3'h6),
         .c0_ddr4_s_axi_awburst(2'b00),
         .c0_ddr4_s_axi_awlock(1'b0),
         .c0_ddr4_s_axi_awcache(4'h0),    
         .c0_ddr4_s_axi_awprot(3'h0),
         .c0_ddr4_s_axi_awqos(4'h0),
         .c0_ddr4_s_axi_awvalid(sync_cl_sh_ddr_awvalid[2]),
         .c0_ddr4_s_axi_awready(sync_sh_cl_ddr_awready[2]),
         
         .c0_ddr4_s_axi_wdata(sync_cl_sh_ddr_wdata[2]),
         .c0_ddr4_s_axi_wstrb(sync_cl_sh_ddr_wstrb[2]),
         .c0_ddr4_s_axi_wlast(sync_cl_sh_ddr_wlast[2]),
         .c0_ddr4_s_axi_wvalid(sync_cl_sh_ddr_wvalid[2]),
         .c0_ddr4_s_axi_wready(sync_sh_cl_ddr_wready[2]),
         
         .c0_ddr4_s_axi_bready(sync_cl_sh_ddr_bready[2]),
         .c0_ddr4_s_axi_bid(sync_sh_cl_ddr_bid[2]),
         .c0_ddr4_s_axi_bresp(sync_sh_cl_ddr_bresp[2]),
         .c0_ddr4_s_axi_bvalid(sync_sh_cl_ddr_bvalid[2]),
         
         .c0_ddr4_s_axi_arid(sync_cl_sh_ddr_arid[2]),
         .c0_ddr4_s_axi_araddr(sync_cl_sh_ddr_araddr[2][33:0]),
         .c0_ddr4_s_axi_arlen(sync_cl_sh_ddr_arlen[2]),
         .c0_ddr4_s_axi_arsize(3'h6),
         .c0_ddr4_s_axi_arburst(2'b0),
         .c0_ddr4_s_axi_arlock(1'b0),
         .c0_ddr4_s_axi_arcache(4'h0),
         .c0_ddr4_s_axi_arprot(3'h0),
         .c0_ddr4_s_axi_arqos(4'h0),
         .c0_ddr4_s_axi_arvalid(sync_cl_sh_ddr_arvalid[2]),
         .c0_ddr4_s_axi_arready(sync_sh_cl_ddr_arready[2]),
         
         .c0_ddr4_s_axi_rready(sync_cl_sh_ddr_rready[2]),
         .c0_ddr4_s_axi_rid(sync_sh_cl_ddr_rid[2]),
         .c0_ddr4_s_axi_rdata(sync_sh_cl_ddr_rdata[2]),
         .c0_ddr4_s_axi_rresp(sync_sh_cl_ddr_rresp[2]),
         .c0_ddr4_s_axi_rlast(sync_sh_cl_ddr_rlast[2]),
         .c0_ddr4_s_axi_rvalid(sync_sh_cl_ddr_rvalid[2]),
         .dbg_bus()        //No Connect
         );
   end
   else
   begin
      assign sh_cl_ddr_is_ready[2] = 0;
   end

//    if (NUM_DDR>=4)
//    begin
//       //--------------------
//       // DDR 3
//       //--------------------
//       ddr4_core DDR4_3 (
//          .sys_rst(~rst_n),
//          .c0_sys_clk_p(CLK_300M_DIMM2_DP),
//          .c0_sys_clk_n(CLK_300M_DIMM2_DN),
//          .c0_ddr4_act_n(M_C_ACT_N),
//          .c0_ddr4_adr(M_C_MA),
//          .c0_ddr4_ba(M_C_BA),
//          .c0_ddr4_bg(M_C_BG),
//          .c0_ddr4_cke(M_C_CKE),
//          .c0_ddr4_odt(M_C_ODT),
//          .c0_ddr4_cs_n(M_C_CS_N),
//          .c0_ddr4_ck_t(M_C_CLK_DP),
//          .c0_ddr4_ck_c(M_C_CLK_DN),
//          .c0_ddr4_reset_n(RST_DIMM_C_N),
//          .c0_ddr4_parity(M_C_PAR),
//       
//          //.c0_ddr4_dq({M_C_ECC, M_C_DQ}),
//          //.c0_ddr4_dqs_c(M_C_DQS_DN),
//          //.c0_ddr4_dqs_t(M_C_DQS_DP),
//          .c0_ddr4_dq({M_C_DQ[63:32], M_C_ECC, M_C_DQ[31:0]}),
//          .c0_ddr4_dqs_t({M_C_DQS_DP[16],M_C_DQS_DP[7], M_C_DQS_DP[15],M_C_DQS_DP[6], M_C_DQS_DP[14], M_C_DQS_DP[5], M_C_DQS_DP[13], M_C_DQS_DP[4], M_C_DQS_DP[17], M_C_DQS_DP[8], M_C_DQS_DP[12], M_C_DQS_DP[3], M_C_DQS_DP[11], M_C_DQS_DP[2], M_C_DQS_DP[10], M_C_DQS_DP[1], M_C_DQS_DP[9], M_C_DQS_DP[0]}),
//          .c0_ddr4_dqs_c({M_C_DQS_DN[16],M_C_DQS_DN[7], M_C_DQS_DN[15],M_C_DQS_DN[6], M_C_DQS_DN[14], M_C_DQS_DN[5], M_C_DQS_DN[13], M_C_DQS_DN[4], M_C_DQS_DN[17], M_C_DQS_DN[8], M_C_DQS_DN[12], M_C_DQS_DN[3], M_C_DQS_DN[11], M_C_DQS_DN[2], M_C_DQS_DN[10], M_C_DQS_DN[1], M_C_DQS_DN[9], M_C_DQS_DN[0]}),
//       
//          .c0_init_calib_complete(sh_cl_ddr_is_ready[3]),
//          .c0_ddr4_ui_clk(ddr_user_clk[3]),
//          .c0_ddr4_ui_clk_sync_rst(ddr_user_rst[3]),
//          .dbg_clk(),                               //No connect
//          
//          .c0_ddr4_s_axi_ctrl_awvalid(1'b0),          //Fixme need to hook up control to MGT
//          .c0_ddr4_s_axi_ctrl_awready(),
//          .c0_ddr4_s_axi_ctrl_awaddr(),
//          .c0_ddr4_s_axi_ctrl_wvalid(1'b0),
//          .c0_ddr4_s_axi_ctrl_wready(),
//          .c0_ddr4_s_axi_ctrl_wdata(),
//          .c0_ddr4_s_axi_ctrl_bvalid(),
//          .c0_ddr4_s_axi_ctrl_bready(1'b1),
//          .c0_ddr4_s_axi_ctrl_bresp(),
//          .c0_ddr4_s_axi_ctrl_arvalid(1'b0),
//          .c0_ddr4_s_axi_ctrl_arready(),
//          .c0_ddr4_s_axi_ctrl_araddr(),
//          .c0_ddr4_s_axi_ctrl_rvalid(),
//          .c0_ddr4_s_axi_ctrl_rready(1'b1),
//          .c0_ddr4_s_axi_ctrl_rdata(),
//          .c0_ddr4_s_axi_ctrl_rresp(),
//          .c0_ddr4_interrupt(),
//          
//          .c0_ddr4_aresetn(ddr_user_rst_n[3]),
//          
//          .c0_ddr4_s_axi_awid(sync_cl_sh_ddr_awid[3]),
//          .c0_ddr4_s_axi_awaddr(sync_cl_sh_ddr_awaddr[3][33:0]),
//          .c0_ddr4_s_axi_awlen(sync_cl_sh_ddr_awlen[3]),
//          .c0_ddr4_s_axi_awsize(3'h6),
//          .c0_ddr4_s_axi_awburst(2'b00),
//          .c0_ddr4_s_axi_awlock(1'b0),
//          .c0_ddr4_s_axi_awcache(4'h0),    
//          .c0_ddr4_s_axi_awprot(3'h0),
//          .c0_ddr4_s_axi_awqos(4'h0),
//          .c0_ddr4_s_axi_awvalid(sync_cl_sh_ddr_awvalid[3]),
//          .c0_ddr4_s_axi_awready(sync_sh_cl_ddr_awready[3]),
//          
//          .c0_ddr4_s_axi_wdata(sync_cl_sh_ddr_wdata[3]),
//          .c0_ddr4_s_axi_wstrb(sync_cl_sh_ddr_wstrb[3]),
//          .c0_ddr4_s_axi_wlast(sync_cl_sh_ddr_wlast[3]),
//          .c0_ddr4_s_axi_wvalid(sync_cl_sh_ddr_wvalid[3]),
//          .c0_ddr4_s_axi_wready(sync_sh_cl_ddr_wready[3]),
//          
//          .c0_ddr4_s_axi_bready(sync_cl_sh_ddr_bready[3]),
//          .c0_ddr4_s_axi_bid(sync_sh_cl_ddr_bid[3]),
//          .c0_ddr4_s_axi_bresp(sync_sh_cl_ddr_bresp[3]),
//          .c0_ddr4_s_axi_bvalid(sync_sh_cl_ddr_bvalid[3]),
//          
//          .c0_ddr4_s_axi_arid(sync_cl_sh_ddr_arid[3]),
//          .c0_ddr4_s_axi_araddr(sync_cl_sh_ddr_araddr[3][33:0]),
//          .c0_ddr4_s_axi_arlen(sync_cl_sh_ddr_arlen[3]),
//          .c0_ddr4_s_axi_arsize(3'h6),
//          .c0_ddr4_s_axi_arburst(2'b0),
//          .c0_ddr4_s_axi_arlock(1'b0),
//          .c0_ddr4_s_axi_arcache(4'h0),
//          .c0_ddr4_s_axi_arprot(3'h0),
//          .c0_ddr4_s_axi_arqos(4'h0),
//          .c0_ddr4_s_axi_arvalid(sync_cl_sh_ddr_arvalid[3]),
//          .c0_ddr4_s_axi_arready(sync_sh_cl_ddr_arready[3]),
//          
//          .c0_ddr4_s_axi_rready(sync_cl_sh_ddr_rready[3]),
//          .c0_ddr4_s_axi_rid(sync_sh_cl_ddr_rid[3]),
//          .c0_ddr4_s_axi_rdata(sync_sh_cl_ddr_rdata[3]),
//          .c0_ddr4_s_axi_rresp(sync_sh_cl_ddr_rresp[3]),
//          .c0_ddr4_s_axi_rlast(sync_sh_cl_ddr_rlast[3]),
//          .c0_ddr4_s_axi_rvalid(sync_sh_cl_ddr_rvalid[3]),
//          .dbg_bus()        //No Connect
//          );
//    end
//    else
//    begin
//       assign sh_cl_ddr_is_ready[3] = 0;
//    end
end
endgenerate

`else // !`ifndef NO_DDR
   
always_comb
begin
    M_A_ACT_N = 0;
    M_A_MA = 0;
    M_A_BA = 0;
    M_A_BG = 0;
    M_A_CKE = 0;
    M_A_ODT = 0;
    M_A_CS_N = 0;
    M_A_CLK_DN = 0;
    M_A_CLK_DP = 0;
    RST_DIMM_A_N = 0;
    M_A_PAR = 0;
    M_B_ACT_N = 0;
    M_B_MA = 0;
    M_B_BA = 0;
    M_B_BG = 0;
    M_B_CKE = 0;
    M_B_ODT = 0;
    M_B_CS_N = 0;
    M_B_CLK_DN = 0;
    M_B_CLK_DP = 0;
    RST_DIMM_B_N = 0;
    M_B_PAR = 0;
    M_C_ACT_N = 0;
    M_C_MA = 0;
    M_C_BA = 0;
    M_C_BG = 0;
    M_C_CKE = 0;
    M_C_ODT = 0;
    M_C_CS_N = 0;
    M_C_CLK_DN = 0;
    M_C_CLK_DP = 0;
    RST_DIMM_C_N = 0;
    M_C_PAR = 0;
    M_D_ACT_N = 0;
    M_D_MA = 0;
    M_D_BA = 0;
    M_D_BG = 0;
    M_D_CKE = 0;
    M_D_ODT = 0;
    M_D_CS_N = 0;
    M_D_CLK_DN = 0;
    M_D_CLK_DP = 0;
    RST_DIMM_D_N = 0;
    M_D_PAR = 0;

 sh_cl_ddr_awready = '{default:'1};
 sh_cl_ddr_wready = '{default:'1};
 sh_cl_ddr_bid = '{default:'0};
 sh_cl_ddr_bresp = '{default:'0};
 sh_cl_ddr_bvalid = '{default:'0};
 sh_cl_ddr_arready = '{default:'1};
 sh_cl_ddr_rid = '{default:'0};
 sh_cl_ddr_rdata = '{default:'0};
 sh_cl_ddr_rresp = '{default:'0};
 sh_cl_ddr_rlast = '{default:'0};
 sh_cl_ddr_rvalid = '{default:'0};
 sh_cl_ddr_is_ready = '{default:'1};
end

`endif // !`ifndef NO_DDR
  

//Temp placeholder for the stat stuff, eventually will add more stuff, and probably use this for 
// restoring DDR calibration data. 




//Flop the interface
logic[7:0] sh_ddr_stat_addr_q[NUM_DDR-1:0];
logic[NUM_DDR-1:0] sh_ddr_stat_wr_q;
logic[NUM_DDR-1:0] sh_ddr_stat_rd_q;
logic[31:0] sh_ddr_stat_wdata_q[NUM_DDR-1:0];

logic[31:0] gpio_reg0[NUM_DDR-1:0] = '{default:'0};
logic[31:0] gpio_reg1[NUM_DDR-1:0] = '{default:'0};

logic[63:0] stat_wr_words[NUM_DDR-1:0] = '{default:'0};
logic[63:0] stat_rd_words[NUM_DDR-1:0] = '{default:'0};
logic[31:0] axl_addr[NUM_DDR-1:0] = '{default:'0};

//ACC_AXL block outputs
logic[NUM_DDR-1:0] acc_ack;
logic[31:0] acc_rdata[NUM_DDR-1:0];

logic[NUM_DDR-1:0] axl_inp;
logic[NUM_DDR-1:0] axl_wr;
logic[NUM_DDR-1:0] axl_rd;

generate
   for (genvar gi=0; gi<NUM_DDR; gi=gi+1)
   begin: ddr_stat
      always_ff @(negedge rst_n or posedge clk)
         if (!rst_n)
         begin
            sh_ddr_stat_addr_q[gi] <= 0;
            sh_ddr_stat_wr_q[gi] <= 0;
            sh_ddr_stat_rd_q[gi] <= 0;
            sh_ddr_stat_wdata_q[gi] <= 0;
         end   
         else
           begin
              if (sh_ddr_stat_wr[gi] || sh_ddr_stat_rd[gi]) 
                sh_ddr_stat_addr_q[gi] <= sh_ddr_stat_addr[gi];
              sh_ddr_stat_wr_q[gi] <= sh_ddr_stat_wr[gi];
              sh_ddr_stat_rd_q[gi] <= sh_ddr_stat_rd[gi];
              if (sh_ddr_stat_wr[gi])
                sh_ddr_stat_wdata_q[gi] <= sh_ddr_stat_wdata[gi];
         end
      
      
      always @(posedge clk)
         if (sh_ddr_stat_wr_q[gi])
         begin
            case (sh_ddr_stat_addr_q[gi])
               8'h00:   gpio_reg0[gi] <= sh_ddr_stat_wdata_q[gi];
               8'h04:   gpio_reg1[gi] <= sh_ddr_stat_wdata_q[gi];
               8'h0c:   ddr_sw_rst[gi] <= sh_ddr_stat_wdata_q[gi][0];
               8'h10:   axl_addr[gi] <= sh_ddr_stat_wdata_q[gi];
            endcase
         end

      //AXI Cycle 
      always_ff @(negedge rst_n or posedge clk)
         if (!rst_n)
            axl_inp[gi] <= 0;
         else if ((sh_ddr_stat_wr_q[gi] || sh_ddr_stat_rd_q[gi]) && (sh_ddr_stat_addr_q[gi]==8'h14))
            axl_inp[gi] <= 1;
         else if (acc_ack[gi])
            axl_inp[gi] <= 0;

      assign axl_wr[gi] = sh_ddr_stat_wr_q[gi] && (sh_ddr_stat_addr_q[gi]==8'h14);
      assign axl_rd[gi] = sh_ddr_stat_rd_q[gi] && (sh_ddr_stat_addr_q[gi]==8'h14);
      
      always_ff @(negedge rst_n or posedge clk) 
         if (!rst_n)
         begin
            ddr_sh_stat_ack[gi] <= 0;
            ddr_sh_stat_rdata[gi] <= 0;
         end   
         else  
         begin
            ddr_sh_stat_ack[gi] <= (axl_inp[gi])?  acc_ack[gi]:
                                                   ((sh_ddr_stat_addr_q[gi]!=8'h14) && (sh_ddr_stat_wr_q[gi] || sh_ddr_stat_rd_q[gi]));

            ddr_sh_stat_rdata[gi] <=   (axl_inp[gi])?                      acc_rdata[gi]:
                                       (sh_ddr_stat_addr_q[gi]==8'h00)?    gpio_reg0[gi]:
                                       (sh_ddr_stat_addr_q[gi]==8'h04)?    gpio_reg1[gi]:
                                       (sh_ddr_stat_addr_q[gi]==8'h08)?    sh_cl_ddr_is_ready[gi]:
                                       (sh_ddr_stat_addr_q[gi]==8'h0c)?    ddr_sw_rst[gi]:
                                       (sh_ddr_stat_addr_q[gi]==8'h10)?    axl_addr[gi]:
                                       (sh_ddr_stat_addr_q[gi]==8'h20)?    stat_wr_words[gi][31:0]:
                                       (sh_ddr_stat_addr_q[gi]==8'h24)?    stat_wr_words[gi][63:32]:
                                       (sh_ddr_stat_addr_q[gi]==8'h28)?    stat_rd_words[gi][31:0]:
                                       (sh_ddr_stat_addr_q[gi]==8'h2c)?    stat_rd_words[gi][63:32]:
                                                                           32'hdddd_ffff;
         end

         always_ff @(posedge clk)
            ddr_sh_stat_int[gi] <= {7'h0, axl_interrupt[gi]};

         //Write stats
         always @(posedge clk)
            if (sh_ddr_stat_wr_q[gi] && ((sh_ddr_stat_addr_q[gi]==8'h20) || (sh_ddr_stat_addr_q[gi]==8'h24)))
               stat_wr_words[gi] <= 0;
            else if (cl_sh_ddr_awvalid[gi] && sh_cl_ddr_awready[gi])
               stat_wr_words[gi] <= stat_wr_words[gi] + cl_sh_ddr_awlen[gi];

         //Read stats
         always @(posedge clk)
            if (sh_ddr_stat_wr_q[gi] && ((sh_ddr_stat_addr_q[gi]==8'h28) || (sh_ddr_stat_addr_q[gi]==8'h2c)))
               stat_rd_words[gi] <= 0;
            else if (cl_sh_ddr_arvalid[gi] && sh_cl_ddr_arready[gi])
               stat_rd_words[gi] <= stat_rd_words[gi] + cl_sh_ddr_arlen[gi];

         //AXI-L interface to DDR controller
         mgt_acc_axl #(.ADDR_WIDTH(32), .SINGLE_PHASE_WR(0)) STAT_AXL (
            .clk(clk),
            .rst_n(rst_n),
      
            .acc_addr(axl_addr[gi]),
            .acc_wr(axl_wr[gi]),
            .acc_rd(axl_rd[gi]),
            .acc_be(4'hf),
            .acc_wdata(sh_ddr_stat_wdata_q[gi]),
         
            .acc_ack(acc_ack[gi]),
            .acc_rdata(acc_rdata[gi]),
         
            .cfg_to_en(1'b0),
            .cfg_to_time(32'h0),
            .cfg_to_rdata(32'h0),

            .axl_cfg_to(),
            .axl_cfg_to_addr(),

            .awvalid(clk_axl_awvalid[gi]),
            .awaddr(clk_axl_awaddr[gi]),
            .awready(clk_axl_awready[gi]),
            
            .wvalid(clk_axl_wvalid[gi]),
            .wdata(clk_axl_wdata[gi]),
            .wstrb(),
            .wready(clk_axl_wready[gi]),

            .bvalid(clk_axl_bvalid[gi]),
            .bresp(clk_axl_bresp[gi]),
            .bready(clk_axl_bready[gi]),

            .arvalid(clk_axl_arvalid[gi]),
            .araddr(clk_axl_araddr[gi]),
            .arready(clk_axl_arready[gi]),

            .rvalid(clk_axl_rvalid[gi]),
            .rdata(clk_axl_rdata[gi]),
            .rresp(clk_axl_rresp[gi]),
            .rready(clk_axl_rready[gi])
         );
            

         //Clock crossing FIFO (clk to ddr clock)
         axi4_ccf #(.ADDR_WIDTH(32), .DATA_WIDTH(32), .ID_WIDTH(1), .A_USER_WIDTH(1), .FIFO_ADDR_WIDTH(1)) AXI_CCF (
            .s_axi_aclk(clk),
            .s_axi_aresetn(rst_n),

            .s_axi_awid(),
            .s_axi_awaddr(clk_axl_awaddr[gi]),
            .s_axi_awlen(),
            .s_axi_awuser(1'b0),
            .s_axi_awvalid(clk_axl_awvalid[gi]),
            .s_axi_awready(clk_axl_awready[gi]),

            .s_axi_wdata(clk_axl_wdata[gi]),
            .s_axi_wstrb(),
            .s_axi_wlast(),
            .s_axi_wvalid(clk_axl_wvalid[gi]),
            .s_axi_wuser(),
            .s_axi_wready(clk_axl_wready[gi]),
   
            .s_axi_bid(),
            .s_axi_bresp(clk_axl_bresp[gi]),
            .s_axi_buser(),
            .s_axi_bvalid(clk_axl_bvalid[gi]),
            .s_axi_bready(clk_axl_bready[gi]),

            .s_axi_arid(),
            .s_axi_araddr(clk_axl_araddr[gi]),
            .s_axi_arlen(),
            .s_axi_aruser(1'b0),
            .s_axi_arvalid(clk_axl_arvalid[gi]),
            .s_axi_arready(clk_axl_arready[gi]),

            .s_axi_rid(),
            .s_axi_rdata(clk_axl_rdata[gi]),
            .s_axi_rresp(clk_axl_rresp[gi]),
            .s_axi_rlast(),
            .s_axi_ruser(),
            .s_axi_rvalid(clk_axl_rvalid[gi]),
            .s_axi_rready(clk_axl_rready[gi]),

            .m_axi_aclk(ddr_user_clk[gi]),
            .m_axi_aresetn(ddr_user_rst_n[gi]),

            .m_axi_awid(),
            .m_axi_awaddr(axl_awaddr[gi]),
            .m_axi_awlen(),
            .m_axi_awuser(),
            .m_axi_awvalid(axl_awvalid[gi]),
            .m_axi_awready(axl_awready[gi]),

            .m_axi_wdata(axl_wdata[gi]),
            .m_axi_wstrb(),
            .m_axi_wlast(),
            .m_axi_wuser(),
            .m_axi_wvalid(axl_wvalid[gi]),
            .m_axi_wready(axl_wready[gi]),
   
            .m_axi_bid(),
            .m_axi_bresp(axl_bresp[gi]),
            .m_axi_buser(),
            .m_axi_bvalid(axl_bvalid[gi]),
            .m_axi_bready(axl_bready[gi]),

            .m_axi_arid(),
            .m_axi_araddr(axl_araddr[gi]),
            .m_axi_arlen(),
            .m_axi_aruser(),
            .m_axi_arvalid(axl_arvalid[gi]),
            .m_axi_arready(axl_arready[gi]),

            .m_axi_rid(),
            .m_axi_rdata(axl_rdata[gi]),
            .m_axi_rresp(axl_rresp[gi]),
            .m_axi_rlast(),
            .m_axi_ruser(),
            .m_axi_rvalid(axl_rvalid[gi]),
            .m_axi_rready(axl_rready[gi])
         );
            
   end
endgenerate

endmodule
