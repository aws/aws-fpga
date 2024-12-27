// ============================================================================
// Amazon FPGA Hardware Development Kit
//
// Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
// ============================================================================


//=============================================================================
// Top level module file for CL_DRAM_HBM_DMA
//=============================================================================

module cl_dram_hbm_dma
#(
  parameter EN_DDR = 1,
  parameter EN_HBM = 1
)
(
`include "cl_ports.vh"
);

`include "cl_id_defines.vh"       // Defines for ID0 and ID1 (PCI ID's)
`include "cl_dram_dma_defines.vh"

// To reduce RTL simulation time, only 8KiB of
// each external DRAM is scrubbed in simulations

`ifdef SIM
  localparam DDR_SCRB_MAX_ADDR = 64'h1FFF;
`else
  localparam DDR_SCRB_MAX_ADDR = 64'h3FFFFFFFF; //16GB
`endif
  localparam DDR_SCRB_BURST_LEN_MINUS1 = 15;

`ifdef NO_CL_TST_SCRUBBER
  localparam NO_SCRB_INST = 1;
`else
  localparam NO_SCRB_INST = 0;
`endif

  //----------------------------
  // Internal interfaces
  //----------------------------
  axi_bus_t  cl_axi_mstr_bus();
  axi_bus_t  cl_sh_pcim_bus();
  axi_bus_t  sh_cl_dma_pcis_bus();
  axi_bus_t  sh_cl_dma_pcis_q();
  axi_bus_t  lcl_cl_sh_ddra();
  axi_bus_t  lcl_cl_sh_ddrb();
  axi_bus_t  axi_bus_tied();
  axi_bus_t  sda_cl_bus();
  axi_bus_t  sh_ocl_bus();

  cfg_bus_t  pcim_tst_cfg_bus();
  cfg_bus_t  ddra_tst_cfg_bus();
  cfg_bus_t  ddrb_tst_cfg_bus();
  cfg_bus_t  hbm_stat_cfg_bus();
  cfg_bus_t  ddrd_tst_cfg_bus();
  cfg_bus_t  axi_mstr_cfg_bus();
  cfg_bus_t  int_tst_cfg_bus();

  scrb_bus_t ddra_scrb_bus();
  scrb_bus_t ddrb_scrb_bus();
  scrb_bus_t ddrc_scrb_bus();
  scrb_bus_t ddrd_scrb_bus();
  //----------------------------
  // End internal interfaces
  //----------------------------

///////////////////////////////////////////////////////////////////////
///////////////// Unused signals //////////////////////////////////////
///////////////////////////////////////////////////////////////////////

  // Tie off unused signals
  assign cl_sh_dma_rd_full  = 'b0;
  assign cl_sh_dma_wr_full  = 'b0;

  assign cl_sh_pcim_awuser  = 'b0;
  assign cl_sh_pcim_aruser  = 'b0;

  assign cl_sh_status0      = 'b0;
  assign cl_sh_status1      = 'b0;
  assign cl_sh_status2      = 'b0;


///////////////////////////////////////////////////////////////////////
///////////////// FLR resposne ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////

  logic sh_cl_flr_assert_q = 'b0;

  // Auto FLR response
  always_ff @(posedge clk_main_a0)
    if (!rst_main_n) begin
      sh_cl_flr_assert_q <= 0;
      cl_sh_flr_done     <= 0;
    end else begin
      sh_cl_flr_assert_q <= sh_cl_flr_assert;
      cl_sh_flr_done     <= sh_cl_flr_assert_q && !cl_sh_flr_done;
    end

///////////////////////////////////////////////////////////////////////
///////////////// Scrubber enable and status //////////////////////////
///////////////////////////////////////////////////////////////////////

  // Bit 31: Debug enable (for cl_sh_id0 and cl_sh_id1)
  // Bit 30:28: Debug Scrb memory select
  // Bit 3 : DDRC Scrub enable
  // Bit 2 : DDRD Scrub enable
  // Bit 1 : DDRB Scrub enable
  // Bit 0 : DDRA Scrub enable
  logic [31:0]  sh_cl_ctl0_q;

  logic         dbg_scrb_en;
  logic [2:0]   dbg_scrb_mem_sel;

  logic [3:0]   all_ddr_scrb_done;
  logic [3:0]   all_ddr_is_ready;
  logic         ddr_ready;
  logic         hbm_ready;

  always_ff @(posedge clk_main_a0)
    if (!rst_main_n)
      sh_cl_ctl0_q <= 32'd0;
    else
      sh_cl_ctl0_q <= sh_cl_ctl0;

  assign ddra_scrb_bus.enable = sh_cl_ctl0_q[0];
  assign ddrb_scrb_bus.enable = sh_cl_ctl0_q[1];
  assign ddrd_scrb_bus.enable = sh_cl_ctl0_q[2];
  assign ddrc_scrb_bus.enable = sh_cl_ctl0_q[3];

  assign dbg_scrb_en          = sh_cl_ctl0_q[31];
  assign dbg_scrb_mem_sel     = sh_cl_ctl0_q[30:28];

  always_ff @(posedge clk_main_a0)
      cl_sh_id0 <= dbg_scrb_en ? (dbg_scrb_mem_sel == 3'd3 ? ddrc_scrb_bus.addr[31:0] :
                                  dbg_scrb_mem_sel == 3'd2 ? ddrd_scrb_bus.addr[31:0] :
                                  dbg_scrb_mem_sel == 3'd1 ? ddrb_scrb_bus.addr[31:0] :
                                  ddra_scrb_bus.addr[31:0]) : `CL_SH_ID0;
  always_ff @(posedge clk_main_a0)
      cl_sh_id1 <= dbg_scrb_en ? (dbg_scrb_mem_sel == 3'd3 ? ddrc_scrb_bus.addr[63:32] :
                                  dbg_scrb_mem_sel == 3'd2 ? ddrd_scrb_bus.addr[63:32] :
                                  dbg_scrb_mem_sel == 3'd1 ? ddrb_scrb_bus.addr[63:32] :
                                  ddra_scrb_bus.addr[63:32]) : `CL_SH_ID1;

  assign all_ddr_scrb_done = {ddrc_scrb_bus.done, ddrd_scrb_bus.done, ddrb_scrb_bus.done, ddra_scrb_bus.done};

  assign all_ddr_is_ready  = {3'd0, ddr_ready};

  assign cl_sh_status_vled = 16'({ddr_ready, hbm_ready});

///////////////////////////////////////////////////////////////////////
///////////////// DMA PCIS SLAVE module ///////////////////////////////
///////////////////////////////////////////////////////////////////////

  assign sh_cl_dma_pcis_bus.awaddr  = sh_cl_dma_pcis_awaddr;
  assign sh_cl_dma_pcis_bus.awid    = sh_cl_dma_pcis_awid;
  assign sh_cl_dma_pcis_bus.awlen   = sh_cl_dma_pcis_awlen;
  assign sh_cl_dma_pcis_bus.awsize  = sh_cl_dma_pcis_awsize;
  assign sh_cl_dma_pcis_bus.awvalid = sh_cl_dma_pcis_awvalid;
  assign cl_sh_dma_pcis_awready     = sh_cl_dma_pcis_bus.awready;

  assign sh_cl_dma_pcis_bus.wid     = sh_cl_dma_pcis_wid;
  assign sh_cl_dma_pcis_bus.wdata   = sh_cl_dma_pcis_wdata;
  assign sh_cl_dma_pcis_bus.wstrb   = sh_cl_dma_pcis_wstrb;
  assign sh_cl_dma_pcis_bus.wlast   = sh_cl_dma_pcis_wlast;
  assign sh_cl_dma_pcis_bus.wvalid  = sh_cl_dma_pcis_wvalid;
  assign cl_sh_dma_pcis_wready      = sh_cl_dma_pcis_bus.wready;

  assign cl_sh_dma_pcis_bresp       = sh_cl_dma_pcis_bus.bresp;
  assign cl_sh_dma_pcis_bid         = sh_cl_dma_pcis_bus.bid;
  assign cl_sh_dma_pcis_bvalid      = sh_cl_dma_pcis_bus.bvalid;
  assign sh_cl_dma_pcis_bus.bready  = sh_cl_dma_pcis_bready;

  assign sh_cl_dma_pcis_bus.araddr  = sh_cl_dma_pcis_araddr;
  assign sh_cl_dma_pcis_bus.arid    = sh_cl_dma_pcis_arid;
  assign sh_cl_dma_pcis_bus.arlen   = sh_cl_dma_pcis_arlen;
  assign sh_cl_dma_pcis_bus.arsize  = sh_cl_dma_pcis_arsize;
  assign sh_cl_dma_pcis_bus.arvalid = sh_cl_dma_pcis_arvalid;
  assign cl_sh_dma_pcis_arready     = sh_cl_dma_pcis_bus.arready;

  assign cl_sh_dma_pcis_rid         = sh_cl_dma_pcis_bus.rid;
  assign cl_sh_dma_pcis_rlast       = sh_cl_dma_pcis_bus.rlast;
  assign cl_sh_dma_pcis_rresp       = sh_cl_dma_pcis_bus.rresp;
  assign cl_sh_dma_pcis_rdata       = sh_cl_dma_pcis_bus.rdata;
  assign cl_sh_dma_pcis_rvalid      = sh_cl_dma_pcis_bus.rvalid;
  assign sh_cl_dma_pcis_bus.rready  = sh_cl_dma_pcis_rready;

  cl_dma_pcis_slv
  #(
    .SCRB_BURST_LEN_MINUS1  (DDR_SCRB_BURST_LEN_MINUS1),
    .SCRB_MAX_ADDR          (DDR_SCRB_MAX_ADDR        ),
    .NO_SCRB_INST           (NO_SCRB_INST             )
  )
  CL_DMA_PCIS_SLV
  (
    .aclk                   (clk_main_a0              ),
    .aresetn                (rst_main_n               ),
    .ddra_tst_cfg_bus       (ddra_tst_cfg_bus         ),
    .ddrb_tst_cfg_bus       (ddrb_tst_cfg_bus         ),
    .ddra_scrb_bus          (ddra_scrb_bus            ),
    .ddrb_scrb_bus          (ddrb_scrb_bus            ),
    .sh_cl_dma_pcis_bus     (sh_cl_dma_pcis_bus       ),
    .cl_axi_mstr_bus        (cl_axi_mstr_bus          ),
    .scrb_axi_ddra          (lcl_cl_sh_ddra           ),
    .scrb_axi_ddrb          (lcl_cl_sh_ddrb           ),
    .sh_cl_dma_pcis_q       (sh_cl_dma_pcis_q         )
  );

///////////////////////////////////////////////////////////////////////
///////////////// Secondary AXI Master module /////////////////////////
///////////////////////////////////////////////////////////////////////

  logic mstr_sync_rst_n;

  xpm_cdc_async_rst CDC_ASYNC_RST_N_AXI_MSTR
  (
    .src_arst               (rst_main_n               ),
    .dest_clk               (clk_main_a0              ),
    .dest_arst              (mstr_sync_rst_n          )
  );

  cl_dram_dma_axi_mstr CL_DRAM_DMA_AXI_MSTR
  (
    .aclk                   (clk_main_a0              ),
    .aresetn                (mstr_sync_rst_n          ),
    .cl_axi_mstr_bus        (cl_axi_mstr_bus          ),
    .axi_mstr_cfg_bus       (axi_mstr_cfg_bus         )
  );

///////////////////////////////////////////////////////////////////////
///////////////// PCIM MSTR module ////////////////////////////////////
///////////////////////////////////////////////////////////////////////

  assign cl_sh_pcim_awid        = cl_sh_pcim_bus.awid;
  assign cl_sh_pcim_awaddr      = cl_sh_pcim_bus.awaddr;
  assign cl_sh_pcim_awsize      = cl_sh_pcim_bus.awsize;
  assign cl_sh_pcim_awlen       = cl_sh_pcim_bus.awlen;
  assign cl_sh_pcim_awvalid     = cl_sh_pcim_bus.awvalid;
  assign cl_sh_pcim_bus.awready = sh_cl_pcim_awready;

  assign cl_sh_pcim_wdata       = cl_sh_pcim_bus.wdata;
  assign cl_sh_pcim_wstrb       = cl_sh_pcim_bus.wstrb;
  assign cl_sh_pcim_wlast       = cl_sh_pcim_bus.wlast;
  assign cl_sh_pcim_wvalid      = cl_sh_pcim_bus.wvalid;
  assign cl_sh_pcim_bus.wready  = sh_cl_pcim_wready;

  assign cl_sh_pcim_bus.bid     = sh_cl_pcim_bid;
  assign cl_sh_pcim_bus.bresp   = sh_cl_pcim_bresp;
  assign cl_sh_pcim_bus.bvalid  = sh_cl_pcim_bvalid;
  assign cl_sh_pcim_bready      = cl_sh_pcim_bus.bready;

  assign cl_sh_pcim_arid        = cl_sh_pcim_bus.arid;
  assign cl_sh_pcim_araddr      = cl_sh_pcim_bus.araddr;
  assign cl_sh_pcim_arlen       = cl_sh_pcim_bus.arlen;
  assign cl_sh_pcim_arsize      = cl_sh_pcim_bus.arsize;
  assign cl_sh_pcim_arvalid     = cl_sh_pcim_bus.arvalid;
  assign cl_sh_pcim_bus.arready = sh_cl_pcim_arready;

  assign cl_sh_pcim_bus.rid     = sh_cl_pcim_rid;
  assign cl_sh_pcim_bus.rresp   = sh_cl_pcim_rresp;
  assign cl_sh_pcim_bus.rdata   = sh_cl_pcim_rdata;
  assign cl_sh_pcim_bus.rlast   = sh_cl_pcim_rlast;
  assign cl_sh_pcim_bus.rvalid  = sh_cl_pcim_rvalid;
  assign cl_sh_pcim_rready      = cl_sh_pcim_bus.rready;

// note: cl_sh_pcim_aruser/awuser are ignored by the shell
// and the axi4 size is set fixed for 64-bytes
//  cl_sh_pcim_arsize/awsize = 3'b6;

  logic pcim_sync_rst_n;

  xpm_cdc_async_rst CDC_ASYNC_RST_N_PCIM
  (
    .src_arst               (rst_main_n               ),
    .dest_clk               (clk_main_a0              ),
    .dest_arst              (pcim_sync_rst_n          )
  );

  cl_pcim_mstr CL_PCIM_MSTR
  (
    .aclk                   (clk_main_a0              ),
    .aresetn                (pcim_sync_rst_n          ),
    .cfg_bus                (pcim_tst_cfg_bus         ),
    .cl_sh_pcim_bus         (cl_sh_pcim_bus           )
  );

///////////////////////////////////////////////////////////////////////
///////////////// OCL SLAVE module ////////////////////////////////////
///////////////////////////////////////////////////////////////////////

  assign sh_ocl_bus.awvalid       = ocl_cl_awvalid;
  assign sh_ocl_bus.awaddr[31:0]  = ocl_cl_awaddr;
  assign cl_ocl_awready           = sh_ocl_bus.awready;

  assign sh_ocl_bus.wdata[31:0]   = ocl_cl_wdata;
  assign sh_ocl_bus.wstrb[3:0]    = ocl_cl_wstrb;
  assign sh_ocl_bus.wvalid        = ocl_cl_wvalid;
  assign cl_ocl_wready            = sh_ocl_bus.wready;

  assign cl_ocl_bresp             = sh_ocl_bus.bresp;
  assign cl_ocl_bvalid            = sh_ocl_bus.bvalid;
  assign sh_ocl_bus.bready        = ocl_cl_bready;

  assign sh_ocl_bus.araddr[31:0]  = ocl_cl_araddr;
  assign sh_ocl_bus.arvalid       = ocl_cl_arvalid;
  assign cl_ocl_arready           = sh_ocl_bus.arready;

  assign cl_ocl_rresp             = sh_ocl_bus.rresp;
  assign cl_ocl_rdata             = sh_ocl_bus.rdata[31:0];
  assign cl_ocl_rvalid            = sh_ocl_bus.rvalid;
  assign sh_ocl_bus.rready        = ocl_cl_rready;

  logic ocl_sync_rst_n;

  xpm_cdc_async_rst CDC_ASYNC_RST_N_OCL
  (
    .src_arst               (rst_main_n               ),
    .dest_clk               (clk_main_a0              ),
    .dest_arst              (ocl_sync_rst_n           )
  );

  cl_ocl_slv CL_OCL_SLV
  (
    .clk                    (clk_main_a0              ),
    .sync_rst_n             (ocl_sync_rst_n           ),
    .sh_cl_flr_assert_q     (sh_cl_flr_assert_q       ),
    .sh_ocl_bus             (sh_ocl_bus               ),
    .pcim_tst_cfg_bus       (pcim_tst_cfg_bus         ),
    .ddra_tst_cfg_bus       (ddra_tst_cfg_bus         ),
    .ddrb_tst_cfg_bus       (ddrb_tst_cfg_bus         ),
    .ddrc_tst_cfg_bus       (hbm_stat_cfg_bus         ),
    .ddrd_tst_cfg_bus       (ddrd_tst_cfg_bus         ),
    .axi_mstr_cfg_bus       (axi_mstr_cfg_bus         ),
    .int_tst_cfg_bus        (int_tst_cfg_bus          )
);


///////////////////////////////////////////////////////////////////////
//////////////////// DDR module ///////////////////////////////////////
///////////////////////////////////////////////////////////////////////

  //-----------------------------------------
  // DDR controller instantiation
  //-----------------------------------------
  localparam   NUM_CFG_STGS_CL_DDR_ATG = 8;

  logic  [7:0] sh_ddr_stat_addr_q;
  logic        sh_ddr_stat_wr_q;
  logic        sh_ddr_stat_rd_q;
  logic [31:0] sh_ddr_stat_wdata_q;
  logic        ddr_sh_stat_ack_q;
  logic [31:0] ddr_sh_stat_rdata_q;
  logic  [7:0] ddr_sh_stat_int_q;
  logic        ddr_sync_rst_n;

  xpm_cdc_async_rst CDC_ASYNC_RST_N_DDR
  (
    .src_arst               (rst_main_n               ),
    .dest_clk               (clk_main_a0              ),
    .dest_arst              (ddr_sync_rst_n           )
  );

  lib_pipe
  #(
    .WIDTH                  (1+1+8+32                 ),
    .STAGES                 (NUM_CFG_STGS_CL_DDR_ATG  )
  )
  PIPE_DDR_STAT0
  (
    .clk                    (clk_main_a0              ),
    .rst_n                  (ddr_sync_rst_n           ),
    .in_bus                 ({sh_cl_ddr_stat_wr,
                              sh_cl_ddr_stat_rd,
                              sh_cl_ddr_stat_addr,
                              sh_cl_ddr_stat_wdata}   ),
    .out_bus                ({sh_ddr_stat_wr_q,
                              sh_ddr_stat_rd_q,
                              sh_ddr_stat_addr_q,
                              sh_ddr_stat_wdata_q}    )
  );


  lib_pipe
  #(
    .WIDTH                  (1+8+32                   ),
    .STAGES                 (NUM_CFG_STGS_CL_DDR_ATG  )
  )
  PIPE_DDR_STAT_ACK0
  (
    .clk                    (clk_main_a0              ),
    .rst_n                  (ddr_sync_rst_n           ),
    .in_bus                 ({ddr_sh_stat_ack_q,
                              ddr_sh_stat_int_q,
                              ddr_sh_stat_rdata_q}    ),
    .out_bus                ({cl_sh_ddr_stat_ack,
                              cl_sh_ddr_stat_int,
                              cl_sh_ddr_stat_rdata}   )
  );

  sh_ddr
  #(
    .DDR_PRESENT            (EN_DDR                   )
  )
  SH_DDR
  (
    .clk                    (clk_main_a0              ),
    .rst_n                  (ddr_sync_rst_n           ),
    .stat_clk               (clk_main_a0              ),
    .stat_rst_n             (ddr_sync_rst_n           ),
    .CLK_DIMM_DP            (CLK_DIMM_DP              ),
    .CLK_DIMM_DN            (CLK_DIMM_DN              ),
    .M_ACT_N                (M_ACT_N                  ),
    .M_MA                   (M_MA                     ),
    .M_BA                   (M_BA                     ),
    .M_BG                   (M_BG                     ),
    .M_CKE                  (M_CKE                    ),
    .M_ODT                  (M_ODT                    ),
    .M_CS_N                 (M_CS_N                   ),
    .M_CLK_DN               (M_CLK_DN                 ),
    .M_CLK_DP               (M_CLK_DP                 ),
    .M_PAR                  (M_PAR                    ),
    .M_DQ                   (M_DQ                     ),
    .M_ECC                  (M_ECC                    ),
    .M_DQS_DP               (M_DQS_DP                 ),
    .M_DQS_DN               (M_DQS_DN                 ),
    .cl_RST_DIMM_N          (RST_DIMM_N               ),

    .cl_sh_ddr_axi_awid     (lcl_cl_sh_ddra.awid      ),
    .cl_sh_ddr_axi_awaddr   (lcl_cl_sh_ddra.awaddr    ),
    .cl_sh_ddr_axi_awlen    (lcl_cl_sh_ddra.awlen     ),
    .cl_sh_ddr_axi_awsize   (lcl_cl_sh_ddra.awsize    ),
    .cl_sh_ddr_axi_awvalid  (lcl_cl_sh_ddra.awvalid   ),
    .cl_sh_ddr_axi_awburst  (lcl_cl_sh_ddra.awburst   ),
    .cl_sh_ddr_axi_awuser   (1'd0                     ),
    .cl_sh_ddr_axi_awready  (lcl_cl_sh_ddra.awready   ),
    .cl_sh_ddr_axi_wdata    (lcl_cl_sh_ddra.wdata     ),
    .cl_sh_ddr_axi_wstrb    (lcl_cl_sh_ddra.wstrb     ),
    .cl_sh_ddr_axi_wlast    (lcl_cl_sh_ddra.wlast     ),
    .cl_sh_ddr_axi_wvalid   (lcl_cl_sh_ddra.wvalid    ),
    .cl_sh_ddr_axi_wready   (lcl_cl_sh_ddra.wready    ),
    .cl_sh_ddr_axi_bid      (lcl_cl_sh_ddra.bid       ),
    .cl_sh_ddr_axi_bresp    (lcl_cl_sh_ddra.bresp     ),
    .cl_sh_ddr_axi_bvalid   (lcl_cl_sh_ddra.bvalid    ),
    .cl_sh_ddr_axi_bready   (lcl_cl_sh_ddra.bready    ),
    .cl_sh_ddr_axi_arid     (lcl_cl_sh_ddra.arid      ),
    .cl_sh_ddr_axi_araddr   (lcl_cl_sh_ddra.araddr    ),
    .cl_sh_ddr_axi_arlen    (lcl_cl_sh_ddra.arlen     ),
    .cl_sh_ddr_axi_arsize   (lcl_cl_sh_ddra.arsize    ),
    .cl_sh_ddr_axi_arvalid  (lcl_cl_sh_ddra.arvalid   ),
    .cl_sh_ddr_axi_arburst  (lcl_cl_sh_ddra.arburst   ),
    .cl_sh_ddr_axi_aruser   (1'd0                     ),
    .cl_sh_ddr_axi_arready  (lcl_cl_sh_ddra.arready   ),
    .cl_sh_ddr_axi_rid      (lcl_cl_sh_ddra.rid       ),
    .cl_sh_ddr_axi_rdata    (lcl_cl_sh_ddra.rdata     ),
    .cl_sh_ddr_axi_rresp    (lcl_cl_sh_ddra.rresp     ),
    .cl_sh_ddr_axi_rlast    (lcl_cl_sh_ddra.rlast     ),
    .cl_sh_ddr_axi_rvalid   (lcl_cl_sh_ddra.rvalid    ),
    .cl_sh_ddr_axi_rready   (lcl_cl_sh_ddra.rready    ),

    .sh_ddr_stat_bus_addr   (sh_ddr_stat_addr_q       ),
    .sh_ddr_stat_bus_wdata  (sh_ddr_stat_wdata_q      ),
    .sh_ddr_stat_bus_wr     (sh_ddr_stat_wr_q         ),
    .sh_ddr_stat_bus_rd     (sh_ddr_stat_rd_q         ),
    .sh_ddr_stat_bus_ack    (ddr_sh_stat_ack_q        ),
    .sh_ddr_stat_bus_rdata  (ddr_sh_stat_rdata_q      ),

    .ddr_sh_stat_int        (ddr_sh_stat_int_q        ),
    .sh_cl_ddr_is_ready     (ddr_ready                )
  );


///////////////////////////////////////////////////////////////////////
//////////////////// HBM module ///////////////////////////////////////
///////////////////////////////////////////////////////////////////////

  logic hbm_sync_rst_n;

  xpm_cdc_async_rst CDC_ASYNC_RST_N_HBM
  (
    .src_arst               (rst_main_n               ),
    .dest_clk               (clk_main_a0              ),
    .dest_arst              (hbm_sync_rst_n           )
  );

  cl_hbm_axi4
  #(
    .HBM_PRESENT            (EN_HBM                   )
  )
  CL_HBM
  (
    .clk_hbm_ref            (clk_hbm_ref              ),
    .clk                    (clk_main_a0              ),
    .rst_n                  (hbm_sync_rst_n           ),
    .hbm_axi4_bus           (lcl_cl_sh_ddrb           ),
    .hbm_stat_bus           (hbm_stat_cfg_bus         ),
    .i_hbm_apb_preset_n_1   (hbm_apb_preset_n_1       ),
    .o_hbm_apb_paddr_1      (hbm_apb_paddr_1          ),
    .o_hbm_apb_pprot_1      (hbm_apb_pprot_1          ),
    .o_hbm_apb_psel_1       (hbm_apb_psel_1           ),
    .o_hbm_apb_penable_1    (hbm_apb_penable_1        ),
    .o_hbm_apb_pwrite_1     (hbm_apb_pwrite_1         ),
    .o_hbm_apb_pwdata_1     (hbm_apb_pwdata_1         ),
    .o_hbm_apb_pstrb_1      (hbm_apb_pstrb_1          ),
    .o_hbm_apb_pready_1     (hbm_apb_pready_1         ),
    .o_hbm_apb_prdata_1     (hbm_apb_prdata_1         ),
    .o_hbm_apb_pslverr_1    (hbm_apb_pslverr_1        ),
    .i_hbm_apb_preset_n_0   (hbm_apb_preset_n_0       ),
    .o_hbm_apb_paddr_0      (hbm_apb_paddr_0          ),
    .o_hbm_apb_pprot_0      (hbm_apb_pprot_0          ),
    .o_hbm_apb_psel_0       (hbm_apb_psel_0           ),
    .o_hbm_apb_penable_0    (hbm_apb_penable_0        ),
    .o_hbm_apb_pwrite_0     (hbm_apb_pwrite_0         ),
    .o_hbm_apb_pwdata_0     (hbm_apb_pwdata_0         ),
    .o_hbm_apb_pstrb_0      (hbm_apb_pstrb_0          ),
    .o_hbm_apb_pready_0     (hbm_apb_pready_0         ),
    .o_hbm_apb_prdata_0     (hbm_apb_prdata_0         ),
    .o_hbm_apb_pslverr_0    (hbm_apb_pslverr_0        ),
    .o_cl_sh_hbm_stat_int   (                         ),
    .o_hbm_ready            (hbm_ready                )
  );


///////////////////////////////////////////////////////////////////////
//////////////////// IRQ module ///////////////////////////////////////
///////////////////////////////////////////////////////////////////////

  logic irq_sync_rst_n;

  xpm_cdc_async_rst CDC_ASYNC_RST_N_IRQ
  (
    .src_arst               (rst_main_n               ),
    .dest_clk               (clk_main_a0              ),
    .dest_arst              (irq_sync_rst_n           )
  );

  cl_int_slv CL_INT_TST
  (
    .clk                    (clk_main_a0              ),
    .rst_n                  (irq_sync_rst_n           ),
    .cfg_bus                (int_tst_cfg_bus          ),
    .cl_sh_apppf_irq_req    (cl_sh_apppf_irq_req      ),
    .sh_cl_apppf_irq_ack    (sh_cl_apppf_irq_ack      )
  );


///////////////////////////////////////////////////////////////////////
//////////////////// SDA module ///////////////////////////////////////
///////////////////////////////////////////////////////////////////////

  assign sda_cl_bus.awaddr[31:0]  = sda_cl_awaddr;
  assign cl_sda_awready           = sda_cl_bus.awready;
  assign sda_cl_bus.awvalid       = sda_cl_awvalid;

  assign sda_cl_bus.wdata[31:0]   = sda_cl_wdata;
  assign sda_cl_bus.wstrb[3:0]    = sda_cl_wstrb;
  assign sda_cl_bus.wvalid        = sda_cl_wvalid;
  assign cl_sda_wready            = sda_cl_bus.wready;

  assign cl_sda_bresp             = sda_cl_bus.bresp;
  assign cl_sda_bvalid            = sda_cl_bus.bvalid;
  assign sda_cl_bus.bready        = sda_cl_bready;

  assign sda_cl_bus.araddr[31:0]  = sda_cl_araddr;
  assign sda_cl_bus.arvalid       = sda_cl_arvalid;
  assign cl_sda_arready           = sda_cl_bus.arready;

  assign cl_sda_rdata             = sda_cl_bus.rdata[31:0];
  assign cl_sda_rresp             = sda_cl_bus.rresp;
  assign cl_sda_rvalid            = sda_cl_bus.rvalid;
  assign sda_cl_bus.rready        = sda_cl_rready;

  logic sda_sync_rst_n;

  xpm_cdc_async_rst CDC_ASYNC_RST_N_SDA
  (
    .src_arst               (rst_main_n               ),
    .dest_clk               (clk_main_a0              ),
    .dest_arst              (sda_sync_rst_n           )
  );

  cl_sda_slv CL_SDA_SLV
  (
    .aclk                   (clk_main_a0              ),
    .aresetn                (sda_sync_rst_n           ),
    .sda_cl_bus             (sda_cl_bus               )
  );


///////////////////////////////////////////////////////////////////////
//////////////////// Debug module /////////////////////////////////////
///////////////////////////////////////////////////////////////////////

`ifndef DISABLE_VJTAG_DEBUG

  cl_ila
  #(
    .DDR_A_PRESENT          (`DDR_A_PRESENT           )
  )
  CL_ILA
  (
    .aclk                   (clk_main_a0              ),
    .drck                   (drck                     ),
    .shift                  (shift                    ),
    .tdi                    (tdi                      ),
    .update                 (update                   ),
    .sel                    (sel                      ),
    .tdo                    (tdo                      ),
    .tms                    (tms                      ),
    .tck                    (tck                      ),
    .runtest                (runtest                  ),
    .reset                  (reset                    ),
    .capture                (capture                  ),
    .bscanid_en             (bscanid_en               ),
    .sh_cl_dma_pcis_q       (sh_cl_dma_pcis_q         ),
  `ifndef DDR_A_ABSENT
    .lcl_cl_sh_ddra         (lcl_cl_sh_ddra           )
  `else
    .lcl_cl_sh_ddra         (axi_bus_tied             )
  `endif
  );

  cl_vio CL_VIO
  (
    .clk_extra_a1           (clk_extra_a1             )
  );

`endif //  `ifndef DISABLE_VJTAG_DEBUG

  //-----------------------------------------
  // Virtual JATG ILA Debug core example
  //-----------------------------------------

  // tie off for ILA port when probing block not present
  assign axi_bus_tied.awvalid = 'b0;
  assign axi_bus_tied.awaddr  = 'b0;
  assign axi_bus_tied.awready = 'b0;
  assign axi_bus_tied.wvalid  = 'b0;
  assign axi_bus_tied.wstrb   = 'b0;
  assign axi_bus_tied.wlast   = 'b0;
  assign axi_bus_tied.wready  = 'b0;
  assign axi_bus_tied.wdata   = 'b0;
  assign axi_bus_tied.arready = 'b0;
  assign axi_bus_tied.rdata   = 'b0;
  assign axi_bus_tied.araddr  = 'b0;
  assign axi_bus_tied.arvalid = 'b0;
  assign axi_bus_tied.awid    = 'b0;
  assign axi_bus_tied.arid    = 'b0;
  assign axi_bus_tied.awlen   = 'b0;
  assign axi_bus_tied.rlast   = 'b0;
  assign axi_bus_tied.rresp   = 'b0;
  assign axi_bus_tied.rid     = 'b0;
  assign axi_bus_tied.rvalid  = 'b0;
  assign axi_bus_tied.arlen   = 'b0;
  assign axi_bus_tied.bresp   = 'b0;
  assign axi_bus_tied.rready  = 'b0;
  assign axi_bus_tied.bvalid  = 'b0;
  assign axi_bus_tied.bid     = 'b0;
  assign axi_bus_tied.bready  = 'b0;


endmodule // cl_dram_hbm_dma
