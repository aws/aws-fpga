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
// 0x30 - Self Refresh Request - Request self refresh to the core
// 0x34 - Self Refresh Ack (read only) - Self refresh ack from the core
// 0x38 - Restore/Skip - Drive these signals to the core
//          0 - Restore
//          1 - Skip Mem Init
//          2 - Restore Complete
// 0x3c - DBG Out - Save/restore debug out (??not sure what is on this)
// 0x4c - XSDB Select - Drive select to the core for save/restore operation
// 0x50 - XSDB Addr - Drive  address to core for save/restore operation
// 0x54 - XSDB Data  - Drive data to core for save/restore operation.  Read/write to this register triggers
//                   a save/restore access to the core (with XSDB Addr setup at offset 0x50).
//
// Interrupt Status0 - bit0: AXI-Lite interrupt from DDR core (refer to Xilinx DDR specification - pg150)


//--------------------------------------------------------------------------------

module sh_ddr #( parameter DDR_A_PRESENT = 1,
                 parameter DDR_B_PRESENT = 1,
                 parameter DDR_D_PRESENT = 1,
                 parameter DDR_A_IO = 1,           //When not Present to include IO buffers
                 parameter DDR_D_IO = 1)           //When not Present to include IO buffers
   (

   //---------------------------
   // Main clock/reset
   //---------------------------
   input clk,
   input rst_n,

   input stat_clk,                           //Stats interface clock
   input stat_rst_n,

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
    output logic cl_RST_DIMM_A_N,

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
    output logic cl_RST_DIMM_B_N,

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
    output logic cl_RST_DIMM_D_N,


   //------------------------------------------------------
   // DDR-4 Interface from CL (AXI-4)
   //------------------------------------------------------
   input[15:0] cl_sh_ddr_awid[2:0],
   input[63:0] cl_sh_ddr_awaddr[2:0],
   input[7:0] cl_sh_ddr_awlen[2:0],
   //input[10:0] cl_sh_ddr_awuser[2:0],
   input cl_sh_ddr_awvalid[2:0],
   output logic[2:0] sh_cl_ddr_awready,

   input[15:0] cl_sh_ddr_wid[2:0],
   input[511:0] cl_sh_ddr_wdata[2:0],
   input[63:0] cl_sh_ddr_wstrb[2:0],
   input[2:0] cl_sh_ddr_wlast,
   input[2:0] cl_sh_ddr_wvalid,
   output logic[2:0] sh_cl_ddr_wready,

   output logic[15:0] sh_cl_ddr_bid[2:0],
   output logic[1:0] sh_cl_ddr_bresp[2:0],
   output logic[2:0] sh_cl_ddr_bvalid,
   input[2:0] cl_sh_ddr_bready,

   input[15:0] cl_sh_ddr_arid[2:0],
   input[63:0] cl_sh_ddr_araddr[2:0],
   input[7:0] cl_sh_ddr_arlen[2:0],
   //input[10:0] cl_sh_ddr_aruser[2:0],
   input[2:0] cl_sh_ddr_arvalid,
   output logic[2:0] sh_cl_ddr_arready,

   output logic[15:0] sh_cl_ddr_rid[2:0],
   output logic[511:0] sh_cl_ddr_rdata[2:0],
   output logic[1:0] sh_cl_ddr_rresp[2:0],
   output logic[2:0] sh_cl_ddr_rlast,
   output logic[2:0] sh_cl_ddr_rvalid,
   input[2:0] cl_sh_ddr_rready,

   output logic[2:0] sh_cl_ddr_is_ready,

   input[7:0] sh_ddr_stat_addr0,
   input sh_ddr_stat_wr0,
   input sh_ddr_stat_rd0,
   input[31:0] sh_ddr_stat_wdata0,

   output logic ddr_sh_stat_ack0,
   output logic[31:0] ddr_sh_stat_rdata0,
   output logic[7:0] ddr_sh_stat_int0,

   input[7:0] sh_ddr_stat_addr1,
   input sh_ddr_stat_wr1,
   input sh_ddr_stat_rd1,
   input[31:0] sh_ddr_stat_wdata1,

   output logic ddr_sh_stat_ack1,
   output logic[31:0] ddr_sh_stat_rdata1,
   output logic[7:0] ddr_sh_stat_int1,

   input[7:0] sh_ddr_stat_addr2,
   input sh_ddr_stat_wr2,
   input sh_ddr_stat_rd2,
   input[31:0] sh_ddr_stat_wdata2,

   output logic ddr_sh_stat_ack2,
   output logic[31:0] ddr_sh_stat_rdata2,
   output logic[7:0] ddr_sh_stat_int2



   );

//-------------------------------------------
// Internal signals
//-------------------------------------------

//--------------------------------------------------------
// DDR4 AXI interafaces to core (sync to DDR clock)
//--------------------------------------------------------
logic[15:0] sync_cl_sh_ddr_awid[2:0];
logic[63:0] sync_cl_sh_ddr_awaddr[2:0];
logic[7:0] sync_cl_sh_ddr_awlen[2:0];
logic sync_cl_sh_ddr_awvalid[2:0];
logic[2:0] sync_sh_cl_ddr_awready;

logic[15:0] sync_cl_sh_ddr_wid[2:0];
logic[511:0] sync_cl_sh_ddr_wdata[2:0];
logic[63:0] sync_cl_sh_ddr_wstrb[2:0];
logic[2:0] sync_cl_sh_ddr_wlast;
logic[2:0] sync_cl_sh_ddr_wvalid;
logic[2:0] sync_sh_cl_ddr_wready;

logic[15:0] sync_sh_cl_ddr_bid[2:0];
logic[1:0] sync_sh_cl_ddr_bresp[2:0];
logic[2:0] sync_sh_cl_ddr_bvalid;
logic[2:0] sync_cl_sh_ddr_bready;

logic[15:0] sync_cl_sh_ddr_arid[2:0];
logic[63:0] sync_cl_sh_ddr_araddr[2:0];
logic[7:0] sync_cl_sh_ddr_arlen[2:0];
logic[2:0] sync_cl_sh_ddr_arvalid;
logic[2:0] sync_sh_cl_ddr_arready;

logic[15:0] sync_sh_cl_ddr_rid[2:0];
logic[511:0] sync_sh_cl_ddr_rdata[2:0];
logic[1:0] sync_sh_cl_ddr_rresp[2:0];
logic[2:0] sync_sh_cl_ddr_rlast;
logic[2:0] sync_sh_cl_ddr_rvalid;
logic[2:0] sync_cl_sh_ddr_rready;

logic[2:0] ddr_user_rst_n;
logic[2:0] ddr_user_clk;
logic[2:0] ddr_user_rst;

logic[2:0] axl_awvalid;
logic[2:0] axl_awready;
logic[31:0] axl_awaddr[2:0];
logic[2:0] axl_wvalid;
logic[2:0] axl_wready;
logic[31:0] axl_wdata[2:0];
logic[2:0] axl_bvalid;
logic[2:0] axl_bready;
logic[1:0] axl_bresp[2:0];
logic[2:0] axl_arvalid;
logic[2:0] axl_arready;
logic[31:0] axl_araddr[2:0];
logic[2:0] axl_rvalid;
logic[2:0] axl_rready;
logic[31:0] axl_rdata[2:0];
logic[1:0] axl_rresp[2:0];
logic[2:0] axl_interrupt;

logic[2:0] clk_axl_awvalid;
logic[2:0] clk_axl_awready;
logic[31:0] clk_axl_awaddr[2:0];
logic[2:0] clk_axl_wvalid;
logic[2:0] clk_axl_wready;
logic[31:0] clk_axl_wdata[2:0];
logic[2:0] clk_axl_bvalid;
logic[2:0] clk_axl_bready;
logic[1:0] clk_axl_bresp[2:0];
logic[2:0] clk_axl_arvalid;
logic[2:0] clk_axl_arready;
logic[31:0] clk_axl_araddr[2:0];
logic[2:0] clk_axl_rvalid;
logic[2:0] clk_axl_rready;
logic[31:0] clk_axl_rdata[2:0];
logic[1:0] clk_axl_rresp[2:0];
logic[2:0] clk_axl_interrupt;

logic[2:0] app_sref_req;
logic[2:0] app_sref_ack;
logic[2:0] app_mem_init_skip;

logic[2:0] app_restore_en;
logic[2:0] app_restore_complete;

logic[2:0] app_xsdb_select;
logic[2:0] app_xsdb_rd_en;
logic[2:0] app_xsdb_wr_en;
logic[15:0] app_xsdb_addr[2:0] = '{default:'0};
logic[8:0] app_xsdb_wr_data[2:0];
logic[8:0] app_xsdb_rd_data[2:0];
logic[2:0] app_xsdb_rdy;
logic[31:0] app_dbg_out[2:0];

logic[2:0] xsdb_inp;

//All the sync signals, regardless of input/output are on the DDR contorller side
logic[2:0] app_sref_req_sync;
logic[2:0] app_sref_ack_sync;
logic[2:0] app_mem_init_skip_sync;

logic[2:0] app_restore_en_sync;
logic[2:0] app_restore_complete_sync;

logic[2:0] app_xsdb_select_sync;
logic[2:0] app_xsdb_rd_en_sync;
logic[2:0] app_xsdb_wr_en_sync;
logic[15:0] app_xsdb_addr_sync[2:0];
logic[8:0] app_xsdb_wr_data_sync[2:0];
logic[8:0] app_xsdb_rd_data_sync[2:0];
logic[2:0] app_xsdb_rdy_sync;
logic[31:0] app_dbg_out_sync[2:0];

logic[2:0] app_xsdb_rd_en_unqual;
logic[2:0] app_xsdb_wr_en_unqual;

logic[2:0] app_xsdb_vld;

logic[2:0] pre_ddr_sh_stat_ack;
logic[31:0] pre_ddr_sh_stat_rdata[2:0];
logic[7:0] pre_ddr_sh_stat_int[2:0];

//Flop the interface
logic[7:0] sh_ddr_stat_addr_q[2:0];
logic[2:0] sh_ddr_stat_wr_q;
logic[2:0] sh_ddr_stat_rd_q;
logic[31:0] sh_ddr_stat_wdata_q[2:0];
   
// End internal signals
//----------------------------

assign ddr_user_rst_n = ~ddr_user_rst;

logic[2:0] ddr_rst_n;
logic[2:0] ddr_sw_rst;

assign ddr_rst_n = ~({3{~rst_n}} | ddr_sw_rst);

//------------------------------------------------------------------------
// Synchronize the Stats interface to the input clock (from the user)
//------------------------------------------------------------------------
logic [7:0] sh_ddr_stat_addr_sync[2:0];
logic[2:0] sh_ddr_stat_wr_sync;
logic[2:0] sh_ddr_stat_rd_sync;
logic[31:0] sh_ddr_stat_wdata_sync[2:0];

logic[2:0] sh_ddr_stat_wr_sync_unqual;
logic[2:0] sh_ddr_stat_rd_sync_unqual;

logic[2:0] sh_ddr_stat_sync_vld;

logic[2:0] ddr_sh_stat_ack_sync;
logic[31:0] ddr_sh_stat_rdata_sync[2:0];
logic[7:0] ddr_sh_stat_int_sync[2:0];

logic[7:0] int_sh_ddr_stat_addr[2:0];
logic[2:0] int_sh_ddr_stat_wr;
logic[2:0] int_sh_ddr_stat_rd;
logic[31:0] int_sh_ddr_stat_wdata[2:0];

logic[2:0] int_ddr_sh_stat_ack;
logic[31:0] int_ddr_sh_stat_rdata[2:0];


//Make 2-d to 1-d assignment
assign int_sh_ddr_stat_addr = {sh_ddr_stat_addr2, sh_ddr_stat_addr1, sh_ddr_stat_addr0};
assign int_sh_ddr_stat_wr = {sh_ddr_stat_wr2, sh_ddr_stat_wr1, sh_ddr_stat_wr0};
assign int_sh_ddr_stat_rd = {sh_ddr_stat_rd2, sh_ddr_stat_rd1, sh_ddr_stat_rd0};
assign int_sh_ddr_stat_wdata = {sh_ddr_stat_wdata2, sh_ddr_stat_wdata1, sh_ddr_stat_wdata0};

assign {ddr_sh_stat_ack2, ddr_sh_stat_ack1, ddr_sh_stat_ack0} = int_ddr_sh_stat_ack;
assign {ddr_sh_stat_rdata2, ddr_sh_stat_rdata1, ddr_sh_stat_rdata0} = {int_ddr_sh_stat_rdata[2], int_ddr_sh_stat_rdata[1], int_ddr_sh_stat_rdata[0]};

generate
   for (genvar gi=0; gi<3; gi++)
   begin: gen_ddr_tst

      //Flop the interface
      always_ff @(negedge stat_rst_n or posedge stat_clk)
         if (!stat_rst_n)
         begin
            sh_ddr_stat_addr_q[gi] <= 0;
            sh_ddr_stat_wr_q[gi] <= 0;
            sh_ddr_stat_rd_q[gi] <= 0;
            sh_ddr_stat_wdata_q[gi] <= 0;
         end   
         else
           begin
              if (int_sh_ddr_stat_wr[gi] || int_sh_ddr_stat_rd[gi]) 
                sh_ddr_stat_addr_q[gi] <= int_sh_ddr_stat_addr[gi];
              sh_ddr_stat_wr_q[gi] <= int_sh_ddr_stat_wr[gi];
              sh_ddr_stat_rd_q[gi] <= int_sh_ddr_stat_rd[gi];
              if (int_sh_ddr_stat_wr[gi])
                sh_ddr_stat_wdata_q[gi] <= int_sh_ddr_stat_wdata[gi];
         end


      //Add flop_ccf going both directions.  Note the wr/rd commands need qualification
      flop_ccf #(.ADDR_WIDTH(1), .DATA_WIDTH(1+1+8+32)) CCF_DDR_STAT_REQ (
         .wr_clk(stat_clk),
         .wr_rst_n(stat_rst_n),

         .rd_clk(clk),
         .rd_rst_n(rst_n),

         .wr_di({sh_ddr_stat_wr_q[gi], sh_ddr_stat_rd_q[gi], sh_ddr_stat_addr_q[gi], sh_ddr_stat_wdata_q[gi]}),
         .wr_push(sh_ddr_stat_wr_q[gi] | sh_ddr_stat_rd_q[gi]),
         .wr_full(),
         .wr_full_n(),
         .rd_do({sh_ddr_stat_wr_sync_unqual[gi], sh_ddr_stat_rd_sync_unqual[gi], sh_ddr_stat_addr_sync[gi], sh_ddr_stat_wdata_sync[gi]}),
         .rd_vld(sh_ddr_stat_sync_vld[gi]),
         .rd_pop(sh_ddr_stat_sync_vld[gi])

      );

      assign sh_ddr_stat_wr_sync[gi] = sh_ddr_stat_wr_sync_unqual[gi] & sh_ddr_stat_sync_vld[gi];
      assign sh_ddr_stat_rd_sync[gi] = sh_ddr_stat_rd_sync_unqual[gi] & sh_ddr_stat_sync_vld[gi];

      flop_ccf #(.ADDR_WIDTH(1), .DATA_WIDTH(32)) CCF_DDR_STAT_ACK (
         .wr_clk(clk),     
         .wr_rst_n(rst_n),

         .rd_clk(stat_clk),
         .rd_rst_n(stat_rst_n),

         .wr_di(ddr_sh_stat_rdata_sync[gi]),
         .wr_push(ddr_sh_stat_ack_sync[gi]),
         .wr_full(),
         .wr_full_n(),
         .rd_do(int_ddr_sh_stat_rdata[gi]),
         .rd_vld(int_ddr_sh_stat_ack[gi]),
         .rd_pop(int_ddr_sh_stat_ack[gi])

      );


   end
endgenerate

//Synchronize INT
sync #(.WIDTH(8)) DDR_STAT_INC_SYNC0 (.clk(stat_clk), .rst_n(stat_rst_n), .in(ddr_sh_stat_int_sync[0]), .sync_out(ddr_sh_stat_int0));
sync #(.WIDTH(8)) DDR_STAT_INC_SYNC1 (.clk(stat_clk), .rst_n(stat_rst_n), .in(ddr_sh_stat_int_sync[1]), .sync_out(ddr_sh_stat_int1));
sync #(.WIDTH(8)) DDR_STAT_INC_SYNC2 (.clk(stat_clk), .rst_n(stat_rst_n), .in(ddr_sh_stat_int_sync[2]), .sync_out(ddr_sh_stat_int2));


`ifndef NO_DDR
//----------------------------------------------------------
// DDR Controllers
//----------------------------------------------------------
generate
   for (genvar gi=0; gi<3; gi++)
   begin:ddr_inst
       if ((gi == 0 && DDR_A_PRESENT == 1) ||
           (gi == 1 && DDR_B_PRESENT == 1) ||
           (gi == 2 && DDR_D_PRESENT == 1)) begin
         axi4_ccf #(.ADDR_WIDTH(64), .DATA_WIDTH(512), .ID_WIDTH(16), .A_USER_WIDTH(1), .FIFO_ADDR_WIDTH(3)) AXI_CCF (
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
       end // if ((gi == 0 && DDR_A_PRESENT == 1) ||...
      
   end // block: ddr_inst
endgenerate


generate
begin:ddr_cores
   if (DDR_A_PRESENT == 1)
   begin
      //--------------------
      // DDR 0
      //--------------------
      ddr4_core DDR4_0 (
         .sys_rst(~ddr_rst_n[0]),
         .c0_sys_clk_p(CLK_300M_DIMM0_DP),
         .c0_sys_clk_n(CLK_300M_DIMM0_DN),

         .ALT_ddr4_reset_n(cl_RST_DIMM_A_N),

         .c0_ddr4_app_sref_req(app_sref_req_sync[0]),
         .c0_ddr4_app_sref_ack(app_sref_ack_sync[0]),
         .c0_ddr4_app_mem_init_skip(app_mem_init_skip_sync[0]),

         .c0_ddr4_app_restore_en(app_restore_en_sync[0]),
         .c0_ddr4_app_restore_complete(app_restore_complete_sync[0]),
         .c0_ddr4_app_xsdb_select(app_xsdb_select_sync[0]),
         .c0_ddr4_app_xsdb_rd_en(app_xsdb_rd_en_sync[0]),
         .c0_ddr4_app_xsdb_wr_en(app_xsdb_wr_en_sync[0]),
         .c0_ddr4_app_xsdb_addr(app_xsdb_addr_sync[0]),
         .c0_ddr4_app_xsdb_wr_data(app_xsdb_wr_data_sync[0]),
         .c0_ddr4_app_xsdb_rd_data(app_xsdb_rd_data_sync[0]),
         .c0_ddr4_app_xsdb_rdy(app_xsdb_rdy_sync[0]),
         .c0_ddr4_app_dbg_out(app_dbg_out_sync[0]),

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
         .c0_ddr4_s_axi_awburst(2'b01),
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
         .c0_ddr4_s_axi_arburst(2'b1),
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
   end // if (NUM_DDR>=1)
   
   else if (DDR_A_IO == 1)
     
   begin
      assign sh_cl_ddr_is_ready[0] = 0;
     
`ifndef DDR_A_SH 
 (* dont_touch = "TRUE" *)     logic dummy_A_clk;
 (* dont_touch = "TRUE" *)        IBUFDS DDR_A_CLK (.I(CLK_300M_DIMM0_DP), .IB(CLK_300M_DIMM0_DN), .O(dummy_A_clk));
  (* dont_touch = "TRUE" *)     OBUF DDR_A_ACT_N (.I(1'b1), .O(M_A_ACT_N));
      for (genvar idx = 0; idx < 17; idx++) begin
 (* dont_touch = "TRUE" *)         OBUF DDR_A_MA (.I(1'b0), .O(M_A_MA[idx]));
      end
 (* dont_touch = "TRUE" *)      OBUF DDR_A_BA0 (.I(1'b0), .O(M_A_BA[0]));
 (* dont_touch = "TRUE" *)      OBUF DDR_A_BA1 (.I(1'b0), .O(M_A_BA[1]));
 (* dont_touch = "TRUE" *)      OBUF DDR_A_BG0 (.I(1'b0), .O(M_A_BG[0]));
 (* dont_touch = "TRUE" *)      OBUF DDR_A_BG1 (.I(1'b0), .O(M_A_BG[1]));
 (* dont_touch = "TRUE" *)      OBUF DDR_A_CKE (.I(1'b0), .O(M_A_CKE[0]));
 (* dont_touch = "TRUE" *)      OBUF DDR_A_ODT (.I(1'b0), .O(M_A_ODT[0]));
 (* dont_touch = "TRUE" *)      OBUF DDR_A_CS_N (.I(1'b0), .O(M_A_CS_N[0]));
 (* dont_touch = "TRUE" *)      OBUFDS DDR_A_CLK_DP (.I(1'b0), .O(M_A_CLK_DP[0]), .OB(M_A_CLK_DN[0]));
 (* dont_touch = "TRUE" *)      OBUF DDR_A_RST (.I(1'b1), .O(RST_DIMM_A_N));
 (* dont_touch = "TRUE" *)      OBUF DDR_A_PAR (.I(1'b0), .O(M_A_PAR));
      for (genvar idx = 0; idx < 64; idx++) begin
 (* dont_touch = "TRUE" *)         IOBUFE3 DDR_A_DQ (.I(1'b0), .T(1'b1), .IO(M_A_DQ[idx]));
      end
      for (genvar idx = 0; idx < 8; idx++) begin
 (* dont_touch = "TRUE" *)         IOBUFE3 DDR_A_ECC (.I(1'b0), .T(1'b1), .IO(M_A_ECC[idx]));
      end
      for (genvar idx = 0; idx < 18; idx++) begin
 (* dont_touch = "TRUE" *)         IOBUFDS DDR_A_DQS_DP (.I(1'b0), .T(1'b1), .IO(M_A_DQS_DP[idx]), .IOB(M_A_DQS_DN[idx]));
      end
`endif

      assign cl_RST_DIMM_A_N = 0;
      
   end // else: !if(NUM_DDR>=1)

   if (DDR_B_PRESENT == 1)
   begin
      //--------------------
      // DDR 1
      //--------------------
      ddr4_core DDR4_1 (
         .sys_rst(~ddr_rst_n[1]),
         .c0_sys_clk_p(CLK_300M_DIMM1_DP),
         .c0_sys_clk_n(CLK_300M_DIMM1_DN),

         .ALT_ddr4_reset_n(cl_RST_DIMM_B_N),

         .c0_ddr4_app_sref_req(app_sref_req_sync[1]),
         .c0_ddr4_app_sref_ack(app_sref_ack_sync[1]),
         .c0_ddr4_app_mem_init_skip(app_mem_init_skip_sync[1]),

         .c0_ddr4_app_restore_en(app_restore_en_sync[1]),
         .c0_ddr4_app_restore_complete(app_restore_complete_sync[1]),
         .c0_ddr4_app_xsdb_select(app_xsdb_select_sync[1]),
         .c0_ddr4_app_xsdb_rd_en(app_xsdb_rd_en_sync[1]),
         .c0_ddr4_app_xsdb_wr_en(app_xsdb_wr_en_sync[1]),
         .c0_ddr4_app_xsdb_addr(app_xsdb_addr_sync[1]),
         .c0_ddr4_app_xsdb_wr_data(app_xsdb_wr_data_sync[1]),
         .c0_ddr4_app_xsdb_rd_data(app_xsdb_rd_data_sync[1]),
         .c0_ddr4_app_xsdb_rdy(app_xsdb_rdy_sync[1]),
         .c0_ddr4_app_dbg_out(app_dbg_out_sync[1]),

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
         .c0_ddr4_s_axi_awburst(2'b01),
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
         .c0_ddr4_s_axi_arburst(2'b01),
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
   end // if (NUM_DDR>=2)
   
   else
     begin
        
      assign sh_cl_ddr_is_ready[1] = 0;

 (* dont_touch = "TRUE" *)     logic dummy_B_clk;
 (* dont_touch = "TRUE" *)        IBUFDS DDR_B_CLK (.I(CLK_300M_DIMM1_DP), .IB(CLK_300M_DIMM1_DN), .O(dummy_B_clk));
  (* dont_touch = "TRUE" *)     OBUF DDR_B_ACT_N (.I(1'b1), .O(M_B_ACT_N));
      for (genvar idx = 0; idx < 17; idx++) begin
 (* dont_touch = "TRUE" *)         OBUF DDR_B_MA (.I(1'b0), .O(M_B_MA[idx]));
      end
 (* dont_touch = "TRUE" *)      OBUF DDR_B_BA0 (.I(1'b0), .O(M_B_BA[0]));
 (* dont_touch = "TRUE" *)      OBUF DDR_B_BA1 (.I(1'b0), .O(M_B_BA[1]));
 (* dont_touch = "TRUE" *)      OBUF DDR_B_BG0 (.I(1'b0), .O(M_B_BG[0]));
 (* dont_touch = "TRUE" *)      OBUF DDR_B_BG1 (.I(1'b0), .O(M_B_BG[1]));
 (* dont_touch = "TRUE" *)      OBUF DDR_B_CKE (.I(1'b0), .O(M_B_CKE[0]));
 (* dont_touch = "TRUE" *)      OBUF DDR_B_ODT (.I(1'b0), .O(M_B_ODT[0]));
 (* dont_touch = "TRUE" *)      OBUF DDR_B_CS_N (.I(1'b0), .O(M_B_CS_N[0]));
 (* dont_touch = "TRUE" *)      OBUFDS DDR_B_CLK_DP (.I(1'b0), .O(M_B_CLK_DP[0]), .OB(M_B_CLK_DN[0]));
 (* dont_touch = "TRUE" *)      OBUF DDR_B_RST (.I(1'b1), .O(RST_DIMM_B_N));
 (* dont_touch = "TRUE" *)      OBUF DDR_B_PAR (.I(1'b0), .O(M_B_PAR));
      for (genvar idx = 0; idx < 64; idx++) begin
 (* dont_touch = "TRUE" *)         IOBUFE3 DDR_B_DQ (.I(1'b0), .T(1'b1), .IO(M_B_DQ[idx]));
      end
      for (genvar idx = 0; idx < 8; idx++) begin
 (* dont_touch = "TRUE" *)         IOBUFE3 DDR_B_ECC (.I(1'b0), .T(1'b1), .IO(M_B_ECC[idx]));
      end
      for (genvar idx = 0; idx < 18; idx++) begin
 (* dont_touch = "TRUE" *)         IOBUFDS DDR_B_DQS_DP (.I(1'b0), .T(1'b1), .IO(M_B_DQS_DP[idx]), .IOB(M_B_DQS_DN[idx]));
      end
      
      assign cl_RST_DIMM_B_N = 0;
         
    end // else: !if(NUM_DDR>=2)
   
   
   if (DDR_D_PRESENT == 1)
   begin
      //--------------------
      // DDR 2
      //--------------------
      ddr4_core DDR4_2 (
         .sys_rst(~ddr_rst_n[2]),
         .c0_sys_clk_p(CLK_300M_DIMM3_DP),
         .c0_sys_clk_n(CLK_300M_DIMM3_DN),

         .ALT_ddr4_reset_n(cl_RST_DIMM_D_N),

         .c0_ddr4_app_sref_req(app_sref_req_sync[2]),
         .c0_ddr4_app_sref_ack(app_sref_ack_sync[2]),
         .c0_ddr4_app_mem_init_skip(app_mem_init_skip_sync[2]),

         .c0_ddr4_app_restore_en(app_restore_en_sync[2]),
         .c0_ddr4_app_restore_complete(app_restore_complete_sync[2]),
         .c0_ddr4_app_xsdb_select(app_xsdb_select_sync[2]),
         .c0_ddr4_app_xsdb_rd_en(app_xsdb_rd_en_sync[2]),
         .c0_ddr4_app_xsdb_wr_en(app_xsdb_wr_en_sync[2]),
         .c0_ddr4_app_xsdb_addr(app_xsdb_addr_sync[2]),
         .c0_ddr4_app_xsdb_wr_data(app_xsdb_wr_data_sync[2]),
         .c0_ddr4_app_xsdb_rd_data(app_xsdb_rd_data_sync[2]),
         .c0_ddr4_app_xsdb_rdy(app_xsdb_rdy_sync[2]),
         .c0_ddr4_app_dbg_out(app_dbg_out_sync[2]),

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
         .c0_ddr4_s_axi_awburst(2'b01),
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
         .c0_ddr4_s_axi_arburst(2'b01),
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
   end // if (NUM_DDR>=3)
   
   else if (DDR_D_IO == 1)
   
     begin
      assign sh_cl_ddr_is_ready[2] = 0;

 (* dont_touch = "TRUE" *)     logic dummy_D_clk;
 (* dont_touch = "TRUE" *)        IBUFDS DDR_D_CLK (.I(CLK_300M_DIMM3_DP), .IB(CLK_300M_DIMM3_DN), .O(dummy_D_clk));
  (* dont_touch = "TRUE" *)     OBUF DDR_D_ACT_N (.I(1'b1), .O(M_D_ACT_N));
      for (genvar idx = 0; idx < 17; idx++) begin
 (* dont_touch = "TRUE" *)         OBUF DDR_D_MA (.I(1'b0), .O(M_D_MA[idx]));
      end
 (* dont_touch = "TRUE" *)      OBUF DDR_D_BA0 (.I(1'b0), .O(M_D_BA[0]));
 (* dont_touch = "TRUE" *)      OBUF DDR_D_BA1 (.I(1'b0), .O(M_D_BA[1]));
 (* dont_touch = "TRUE" *)      OBUF DDR_D_BG0 (.I(1'b0), .O(M_D_BG[0]));
 (* dont_touch = "TRUE" *)      OBUF DDR_D_BG1 (.I(1'b0), .O(M_D_BG[1]));
 (* dont_touch = "TRUE" *)      OBUF DDR_D_CKE (.I(1'b0), .O(M_D_CKE[0]));
 (* dont_touch = "TRUE" *)      OBUF DDR_D_ODT (.I(1'b0), .O(M_D_ODT[0]));
 (* dont_touch = "TRUE" *)      OBUF DDR_D_CS_N (.I(1'b0), .O(M_D_CS_N[0]));
 (* dont_touch = "TRUE" *)      OBUFDS DDR_D_CLK_DP (.I(1'b0), .O(M_D_CLK_DP[0]), .OB(M_D_CLK_DN[0]));
 (* dont_touch = "TRUE" *)      OBUF DDR_D_RST (.I(1'b1), .O(RST_DIMM_D_N));
 (* dont_touch = "TRUE" *)      OBUF DDR_D_PAR (.I(1'b0), .O(M_D_PAR));
      for (genvar idx = 0; idx < 64; idx++) begin
 (* dont_touch = "TRUE" *)         IOBUFE3 DDR_D_DQ (.I(1'b0), .T(1'b1), .IO(M_D_DQ[idx]));
      end
      for (genvar idx = 0; idx < 8; idx++) begin
 (* dont_touch = "TRUE" *)         IOBUFE3 DDR_D_ECC (.I(1'b0), .T(1'b1), .IO(M_D_ECC[idx]));
      end
      for (genvar idx = 0; idx < 18; idx++) begin
 (* dont_touch = "TRUE" *)         IOBUFDS DDR_D_DQS_DP (.I(1'b0), .T(1'b1), .IO(M_D_DQS_DP[idx]), .IOB(M_D_DQS_DN[idx]));
      end
      
      assign cl_RST_DIMM_D_N = 0;

   end // else: !if(NUM_DDR>=3)
   
end // block: ddr_cores
   
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
  

//--------------------------------------------------------------------------------------------------------------------------------------------------------
//Stat stuff.  The interface to SH is on "stat_clk" (250MHz clock).  We cross this to "clk" (developer supplied DDR interface clock), and all the stat
// logic is actually on "clk".  To interface to the DDR controller have to cross to ddr_user_clk.
//--------------------------------------------------------------------------------------------------------------------------------------------------------


logic[31:0] gpio_reg0[2:0];
logic[31:0] gpio_reg1[2:0];

logic[63:0] stat_wr_words[2:0] = '{default:'0};
logic[63:0] stat_rd_words[2:0] = '{default:'0};
logic[31:0] axl_addr[2:0] = '{default:'0};

//ACC_AXL block outputs
logic[2:0] acc_ack;
logic[31:0] acc_rdata[2:0];

logic[2:0] axl_inp;
logic[2:0] axl_wr;
logic[2:0] axl_rd;

generate
   for (genvar gi=0; gi<3; gi=gi+1)
     begin: ddr_stat
        if ((gi == 0 && DDR_A_PRESENT == 1) ||
            (gi == 1 && DDR_B_PRESENT == 1) ||
            (gi == 2 && DDR_D_PRESENT == 1)) begin
      
      
      always @(posedge clk)
         if (!rst_n)
         begin
            gpio_reg0[gi] <= 0;
            gpio_reg1[gi] <= 0;
            ddr_sw_rst[gi] <= 1;
            app_sref_req[gi] <= 0;
            app_restore_complete[gi] <= 0;
            app_mem_init_skip[gi] <= 0; 
            app_restore_en[gi] <= 0;
            app_xsdb_select[gi] <= 0;
         end 
         else if (sh_ddr_stat_wr_sync[gi])
         begin
            case (sh_ddr_stat_addr_sync[gi])
               8'h00:   gpio_reg0[gi] <= sh_ddr_stat_wdata_sync[gi];
               8'h04:   gpio_reg1[gi] <= sh_ddr_stat_wdata_sync[gi];
               8'h0c:   ddr_sw_rst[gi] <= sh_ddr_stat_wdata_sync[gi][0];
               //8'h10:   axl_addr[gi] <= sh_ddr_stat_wdata_sync[gi];
               8'h30:   app_sref_req[gi] <= sh_ddr_stat_wdata_sync[gi][0];
               8'h38:   {app_restore_complete[gi], app_mem_init_skip[gi], app_restore_en[gi]} <= sh_ddr_stat_wdata_sync[gi][2:0];
               8'h4c:   app_xsdb_select[gi] <= sh_ddr_stat_wdata_sync[gi][0];
            endcase
         end

      //AXL Address has auto-inc feature
      always @(posedge clk)
         if (sh_ddr_stat_wr_sync[gi] && (sh_ddr_stat_addr_sync[gi]==8'h10))
            axl_addr[gi] <= sh_ddr_stat_wdata_sync[gi];
         else if (axl_inp[gi] && acc_ack[gi])
            axl_addr[gi] <= axl_addr[gi] + 1;

      //XSDB Address has auto-inc feature
      always @(posedge clk)
         if (sh_ddr_stat_wr_sync[gi] && (sh_ddr_stat_addr_sync[gi]==8'h50))
            app_xsdb_addr[gi] <= sh_ddr_stat_wdata_sync[gi];
         else if (xsdb_inp[gi] && app_xsdb_rdy[gi])
            app_xsdb_addr[gi] <= app_xsdb_addr[gi] + 1; 

      //AXI Cycle 
      always_ff @(negedge rst_n or posedge clk)
         if (!rst_n)
            axl_inp[gi] <= 0;
         else if ((sh_ddr_stat_wr_sync[gi] || sh_ddr_stat_rd_sync[gi]) && (sh_ddr_stat_addr_sync[gi]==8'h14))
            axl_inp[gi] <= 1;
         else if (acc_ack[gi])
            axl_inp[gi] <= 0;

      //XSDB Cycle
      always_ff @(negedge rst_n or posedge clk)
         if (!rst_n)
            xsdb_inp[gi] <= 0;
         else if ((sh_ddr_stat_wr_sync[gi] || sh_ddr_stat_rd_sync[gi]) && (sh_ddr_stat_addr_sync[gi]==8'h54))
            xsdb_inp[gi] <= 0;
         else if (app_xsdb_rdy[gi])
            xsdb_inp[gi] <= 0;

      assign axl_wr[gi] = sh_ddr_stat_wr_sync[gi] && (sh_ddr_stat_addr_sync[gi]==8'h14);
      assign axl_rd[gi] = sh_ddr_stat_rd_sync[gi] && (sh_ddr_stat_addr_sync[gi]==8'h14);

      //Note these are pulses
      assign app_xsdb_wr_en[gi] = sh_ddr_stat_wr_sync[gi] && !xsdb_inp[gi] && (sh_ddr_stat_addr_sync[gi]==8'h54); 
      assign app_xsdb_rd_en[gi] = sh_ddr_stat_rd_sync[gi] && !xsdb_inp[gi] && (sh_ddr_stat_addr_sync[gi]==8'h54);

      assign app_xsdb_wr_data[gi] = sh_ddr_stat_wdata_sync[gi];
      
      always_ff @(negedge rst_n or posedge clk) 
         if (!rst_n)
         begin
            pre_ddr_sh_stat_ack[gi] <= 0;
            pre_ddr_sh_stat_rdata[gi] <= 0;
         end   
         else  
         begin
            pre_ddr_sh_stat_ack[gi] <= (axl_inp[gi])?    acc_ack[gi]:
                                       (xsdb_inp[gi])?   app_xsdb_rdy[gi]:    
                                                         ((sh_ddr_stat_addr_sync[gi]!=8'h14) && (sh_ddr_stat_wr_sync[gi] || sh_ddr_stat_rd_sync[gi]));

            pre_ddr_sh_stat_rdata[gi] <=   (axl_inp[gi])?                     acc_rdata[gi]:
                                       (xsdb_inp[gi])?                        app_xsdb_rd_data[gi]:
                                       (sh_ddr_stat_addr_sync[gi]==8'h00)?    gpio_reg0[gi]:
                                       (sh_ddr_stat_addr_sync[gi]==8'h04)?    gpio_reg1[gi]:
                                       (sh_ddr_stat_addr_sync[gi]==8'h08)?    sh_cl_ddr_is_ready[gi]:
                                       (sh_ddr_stat_addr_sync[gi]==8'h0c)?    ddr_sw_rst[gi]:
                                       (sh_ddr_stat_addr_sync[gi]==8'h10)?    axl_addr[gi]:
                                       (sh_ddr_stat_addr_sync[gi]==8'h20)?    stat_wr_words[gi][31:0]:
                                       (sh_ddr_stat_addr_sync[gi]==8'h24)?    stat_wr_words[gi][63:32]:
                                       (sh_ddr_stat_addr_sync[gi]==8'h28)?    stat_rd_words[gi][31:0]:
                                       (sh_ddr_stat_addr_sync[gi]==8'h2c)?    stat_rd_words[gi][63:32]:
                                       (sh_ddr_stat_addr_sync[gi]==8'h30)?    app_sref_req[gi]:
                                       (sh_ddr_stat_addr_sync[gi]==8'h34)?    app_sref_ack[gi]:
                                       (sh_ddr_stat_addr_sync[gi]==8'h38)?    {app_restore_complete[gi], app_mem_init_skip[gi], app_restore_en[gi]}:
                                       (sh_ddr_stat_addr_sync[gi]==8'h3c)?    app_dbg_out[gi]:
                                       (sh_ddr_stat_addr_sync[gi]==8'h4c)?    app_xsdb_select[gi]:
                                       (sh_ddr_stat_addr_sync[gi]==8'h50)?    app_xsdb_addr[gi]:
                                       (sh_ddr_stat_addr_sync[gi]==8'h54)?    app_xsdb_rd_data[gi]:
                                                                              32'hbaad_dd00;
         end

         always_ff @(posedge clk)
            pre_ddr_sh_stat_int[gi] <= {7'h0, axl_interrupt[gi]};

         //Have one state of pipelining here.
         always @(posedge clk)
         begin
            ddr_sh_stat_ack_sync[gi] <= pre_ddr_sh_stat_ack[gi];
            ddr_sh_stat_rdata_sync[gi] <= pre_ddr_sh_stat_rdata[gi];
            ddr_sh_stat_int_sync[gi] <= pre_ddr_sh_stat_int[gi];
         end
            

         //Write stats
         always @(posedge clk)
            if (sh_ddr_stat_wr_sync[gi] && ((sh_ddr_stat_addr_sync[gi]==8'h20) || (sh_ddr_stat_addr_sync[gi]==8'h24)))
               stat_wr_words[gi] <= 0;
            else if (cl_sh_ddr_awvalid[gi] && sh_cl_ddr_awready[gi])
               stat_wr_words[gi] <= stat_wr_words[gi] + cl_sh_ddr_awlen[gi];

         //Read stats
         always @(posedge clk)
            if (sh_ddr_stat_wr_sync[gi] && ((sh_ddr_stat_addr_sync[gi]==8'h28) || (sh_ddr_stat_addr_sync[gi]==8'h2c)))
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
            .acc_wdata(sh_ddr_stat_wdata_sync[gi]),
         
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
        end // if ((gi == 0 && DDR_A_PRESENT == 1) ||...

      //Syncrhonizer for save/restore signals
      sync #(.WIDTH(4)) SAVE_RST_TO_DDR_SYNC (.clk(ddr_user_clk[gi]), .rst_n(ddr_user_rst_n[gi]),  .in({app_sref_req[gi], app_mem_init_skip[gi], app_restore_en[gi], app_xsdb_select[gi]}), 
                                             .sync_out({app_sref_req_sync[gi], app_mem_init_skip_sync[gi], app_restore_en_sync[gi], app_xsdb_select_sync[gi]}));

      sync #(.WIDTH(33)) SAVE_RST_FROM_DDR_SYNC (.clk(clk), .rst_n(rst_n), .in({app_sref_ack_sync[gi], app_dbg_out_sync[gi]}), .sync_out({app_sref_ack[gi], app_dbg_out[gi]}));

  
      flop_ccf #(.ADDR_WIDTH(1), .DATA_WIDTH(1+1+9+16)) CCF_XSDB_REQ (
         .wr_clk(clk),
         .wr_rst_n(rst_n),

         .rd_clk(ddr_user_clk[gi]),
         .rd_rst_n(ddr_user_rst_n[gi]),

         .wr_di({app_xsdb_rd_en[gi], app_xsdb_wr_en[gi], app_xsdb_wr_data[gi], app_xsdb_addr[gi]}),
         .wr_push(app_xsdb_rd_en[gi] | app_xsdb_wr_en[gi]),
         .wr_full(),
         .wr_full_n(),
         .rd_do({app_xsdb_rd_en_unqual[gi], app_xsdb_wr_en_unqual[gi], app_xsdb_wr_data_sync[gi], app_xsdb_addr_sync[gi]}), 
         .rd_vld(app_xsdb_vld[gi]),
         .rd_pop(app_xsdb_vld[gi])
      );

      assign app_xsdb_rd_en_sync[gi] = app_xsdb_vld[gi] && app_xsdb_rd_en_unqual[gi];
      assign app_xsdb_wr_en_sync[gi] = app_xsdb_vld[gi] && app_xsdb_wr_en_unqual[gi];

      flop_ccf #(.ADDR_WIDTH(1), .DATA_WIDTH(9)) CCF_XSDB_ACK (
         .wr_clk(ddr_user_clk[gi]),
         .wr_rst_n(ddr_user_rst_n[gi]),

         .rd_clk(clk),
         .rd_rst_n(rst_n),

         .wr_di(app_xsdb_rd_data_sync[gi]),
         .wr_push(app_xsdb_rdy_sync[gi]),
         .wr_full(),
         .wr_full_n(),
         .rd_do(app_xsdb_rd_data[gi]),
         .rd_vld(app_xsdb_rdy[gi]),
         .rd_pop(app_xsdb_rdy[gi])
         );
   
   

        
   end   //for (generate for)
endgenerate

endmodule
