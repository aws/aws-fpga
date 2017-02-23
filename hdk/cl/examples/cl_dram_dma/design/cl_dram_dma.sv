// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

//`define NO_CL_DDR_TST_AXI4_REG_SLC
`define OCL_TG_CTL

module cl_dram_dma #(parameter NUM_PCIE=1, parameter NUM_DDR=4, parameter NUM_HMC=4, parameter NUM_GTY = 4) 

(
   `include "cl_ports.vh"

);
  
   localparam DDR_A_PRESENT = 1;
   localparam DDR_B_PRESENT = 1;
   localparam DDR_D_PRESENT = 1;
   
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

`ifdef NO_CL_TST_SCRUBBER
   localparam NO_SCRB_INST = 1;
`else
   localparam NO_SCRB_INST = 0;
`endif   
   
`ifdef DDR_A_SH      
   parameter SH_DDR_A_PRESENT = 1;
`else 
   parameter SH_DDR_A_PRESENT = 0;
`endif   
   
//---------------------------- 
// Internal signals
//---------------------------- 
logic[15:0] lcl_cl_sh_ddr_awid[2:0];
logic[63:0] lcl_cl_sh_ddr_awaddr[2:0];
logic[7:0] lcl_cl_sh_ddr_awlen[2:0];
logic lcl_cl_sh_ddr_awvalid[2:0];
logic[2:0] lcl_sh_cl_ddr_awready;
   
logic[15:0] lcl_cl_sh_ddr_wid[2:0];
logic[511:0] lcl_cl_sh_ddr_wdata[2:0];
logic[63:0] lcl_cl_sh_ddr_wstrb[2:0];
logic[2:0] lcl_cl_sh_ddr_wlast;
logic[2:0] lcl_cl_sh_ddr_wvalid;
logic[2:0] lcl_sh_cl_ddr_wready;
   
logic[15:0] lcl_sh_cl_ddr_bid[2:0];
logic[1:0] lcl_sh_cl_ddr_bresp[2:0];
logic[2:0] lcl_sh_cl_ddr_bvalid;
logic[2:0] lcl_cl_sh_ddr_bready;
   
logic[2:0] dummy_lcl_cl_sh_ddr_arid[2:0];
logic[15:0] lcl_cl_sh_ddr_arid[2:0];
logic[63:0] lcl_cl_sh_ddr_araddr[2:0];
logic[7:0] lcl_cl_sh_ddr_arlen[2:0];
logic[2:0] lcl_cl_sh_ddr_arvalid;
logic[2:0] lcl_sh_cl_ddr_arready;
   
logic[15:0] lcl_sh_cl_ddr_rid[2:0];
logic[511:0] lcl_sh_cl_ddr_rdata[2:0];
logic[1:0] lcl_sh_cl_ddr_rresp[2:0];
logic[2:0] lcl_sh_cl_ddr_rlast;
logic[2:0] lcl_sh_cl_ddr_rvalid;
logic[2:0] lcl_cl_sh_ddr_rready;

logic[5:0] lcl_cl_sh_ddr_awid_q[2:0];
logic[63:0] lcl_cl_sh_ddr_awaddr_q[2:0];
logic[7:0] lcl_cl_sh_ddr_awlen_q[2:0];
logic lcl_cl_sh_ddr_awvalid_q[2:0];
logic[2:0] lcl_sh_cl_ddr_awready_q;
   
logic[5:0] lcl_cl_sh_ddr_wid_q[2:0];
logic[511:0] lcl_cl_sh_ddr_wdata_q[2:0];
logic[63:0] lcl_cl_sh_ddr_wstrb_q[2:0];
logic[2:0] lcl_cl_sh_ddr_wlast_q;
logic[2:0] lcl_cl_sh_ddr_wvalid_q;
logic[2:0] lcl_sh_cl_ddr_wready_q;
   
logic[5:0] lcl_sh_cl_ddr_bid_q[2:0];
logic[9:0] dummy_lcl_sh_cl_ddr_bid_q[2:0];
logic[1:0] lcl_sh_cl_ddr_bresp_q[2:0];
logic[2:0] lcl_sh_cl_ddr_bvalid_q;
logic[2:0] lcl_cl_sh_ddr_bready_q;
   
logic[5:0] lcl_cl_sh_ddr_arid_q[2:0];
logic[63:0] lcl_cl_sh_ddr_araddr_q[2:0];
logic[7:0] lcl_cl_sh_ddr_arlen_q[2:0];
logic[2:0] lcl_cl_sh_ddr_arvalid_q;
logic[2:0] lcl_sh_cl_ddr_arready_q;
   
logic[5:0] lcl_sh_cl_ddr_rid_q[2:0];
logic[9:0] dummy_lcl_sh_cl_ddr_rid_q[2:0];
logic[511:0] lcl_sh_cl_ddr_rdata_q[2:0];
logic[1:0] lcl_sh_cl_ddr_rresp_q[2:0];
logic[2:0] lcl_sh_cl_ddr_rlast_q;
logic[2:0] lcl_sh_cl_ddr_rvalid_q;
logic[2:0] lcl_cl_sh_ddr_rready_q;

logic[5:0] lcl_cl_sh_ddr_awid_qq[2:0];
logic[63:0] lcl_cl_sh_ddr_awaddr_qq[2:0];
logic[7:0] lcl_cl_sh_ddr_awlen_qq[2:0];
logic lcl_cl_sh_ddr_awvalid_qq[2:0];
logic[2:0] lcl_sh_cl_ddr_awready_qq;
   
logic[5:0] lcl_cl_sh_ddr_wid_qq[2:0];
logic[511:0] lcl_cl_sh_ddr_wdata_qq[2:0];
logic[63:0] lcl_cl_sh_ddr_wstrb_qq[2:0];
logic[2:0] lcl_cl_sh_ddr_wlast_qq;
logic[2:0] lcl_cl_sh_ddr_wvalid_qq;
logic[2:0] lcl_sh_cl_ddr_wready_qq;
   
logic[5:0] lcl_sh_cl_ddr_bid_qq[2:0];
logic[9:0] dummy_lcl_sh_cl_ddr_bid_qq[2:0];
logic[1:0] lcl_sh_cl_ddr_bresp_qq[2:0];
logic[2:0] lcl_sh_cl_ddr_bvalid_qq;
logic[2:0] lcl_cl_sh_ddr_bready_qq;
   
logic[5:0] lcl_cl_sh_ddr_arid_qq[2:0];
logic[63:0] lcl_cl_sh_ddr_araddr_qq[2:0];
logic[7:0] lcl_cl_sh_ddr_arlen_qq[2:0];
logic[2:0] lcl_cl_sh_ddr_arvalid_qq;
logic[2:0] lcl_sh_cl_ddr_arready_qq;
   
logic[5:0] lcl_sh_cl_ddr_rid_qq[2:0];
logic[9:0] dummy_lcl_sh_cl_ddr_rid_qq[2:0];
logic[511:0] lcl_sh_cl_ddr_rdata_qq[2:0];
logic[1:0] lcl_sh_cl_ddr_rresp_qq[2:0];
logic[2:0] lcl_sh_cl_ddr_rlast_qq;
logic[2:0] lcl_sh_cl_ddr_rvalid_qq;
logic[2:0] lcl_cl_sh_ddr_rready_qq;


logic[15:0] lcl_cl_sh_ddr_awid_q3[2:0];
logic[63:0] lcl_cl_sh_ddr_awaddr_q3[2:0];
logic[7:0] lcl_cl_sh_ddr_awlen_q3[2:0];
logic lcl_cl_sh_ddr_awvalid_q3[2:0];
logic[2:0] lcl_sh_cl_ddr_awready_q3;
   
logic[15:0] lcl_cl_sh_ddr_wid_q3[2:0];
logic[511:0] lcl_cl_sh_ddr_wdata_q3[2:0];
logic[63:0] lcl_cl_sh_ddr_wstrb_q3[2:0];
logic[2:0] lcl_cl_sh_ddr_wlast_q3;
logic[2:0] lcl_cl_sh_ddr_wvalid_q3;
logic[2:0] lcl_sh_cl_ddr_wready_q3;
   
logic[15:0] lcl_sh_cl_ddr_bid_q3[2:0];
logic[1:0] lcl_sh_cl_ddr_bresp_q3[2:0];
logic[2:0] lcl_sh_cl_ddr_bvalid_q3;
logic[2:0] lcl_cl_sh_ddr_bready_q3;
   
logic[15:0] lcl_cl_sh_ddr_arid_q3[2:0];
logic[63:0] lcl_cl_sh_ddr_araddr_q3[2:0];
logic[7:0] lcl_cl_sh_ddr_arlen_q3[2:0];
logic[2:0] lcl_cl_sh_ddr_arvalid_q3;
logic[2:0] lcl_sh_cl_ddr_arready_q3;
   
logic[15:0] lcl_sh_cl_ddr_rid_q3[2:0];
logic[511:0] lcl_sh_cl_ddr_rdata_q3[2:0];
logic[1:0] lcl_sh_cl_ddr_rresp_q3[2:0];
logic[2:0] lcl_sh_cl_ddr_rlast_q3;
logic[2:0] lcl_sh_cl_ddr_rvalid_q3;
logic[2:0] lcl_cl_sh_ddr_rready_q3;

   
logic[2:0] lcl_sh_cl_ddr_is_ready;

logic[3:0] dummy_cl_sh_pcim_arid; 
logic dummy_cl_sh_pcim_awid; 

   logic [2:0] dummy_cl_sh_ddr_arid;
   
   logic [3:0] all_ddr_is_ready;

logic[5:0] cl_sh_hmc_awid[NUM_HMC-1:0];
logic[63:0] cl_sh_hmc_awaddr[NUM_HMC-1:0];
logic[7:0] cl_sh_hmc_awlen[NUM_HMC-1:0];
logic [8:0] cl_sh_hmc_awuser[NUM_HMC-1:0];
logic [NUM_HMC-1:0] cl_sh_hmc_awvalid;
logic[NUM_HMC-1:0] sh_cl_hmc_awready;

logic[5:0] cl_sh_hmc_wid[NUM_HMC-1:0];
logic[511:0] cl_sh_hmc_wdata[NUM_HMC-1:0];
logic[63:0] cl_sh_hmc_wstrb[NUM_HMC-1:0];
logic[NUM_HMC-1:0] cl_sh_hmc_wlast;
logic[NUM_HMC-1:0] cl_sh_hmc_wvalid;
logic[NUM_HMC-1:0] sh_cl_hmc_wready;

logic[5:0] sh_cl_hmc_bid[NUM_HMC-1:0];
logic[1:0] sh_cl_hmc_bresp[NUM_HMC-1:0];
logic[NUM_HMC-1:0] sh_cl_hmc_bvalid;
logic [17:0] sh_cl_hmc_buser[NUM_HMC-1:0];
logic[NUM_HMC-1:0] cl_sh_hmc_bready;

logic[8:0] cl_sh_hmc_arid[NUM_HMC-1:0];
logic[63:0] cl_sh_hmc_araddr[NUM_HMC-1:0];
logic[7:0] cl_sh_hmc_arlen[NUM_HMC-1:0];
logic [8:0] cl_sh_hmc_aruser[NUM_HMC-1:0];
logic[NUM_HMC-1:0] cl_sh_hmc_arvalid;
logic[NUM_HMC-1:0] sh_cl_hmc_arready;

logic[8:0] sh_cl_hmc_rid[NUM_HMC-1:0];
logic [17 : 0] sh_cl_hmc_ruser[NUM_HMC-1:0];
logic[511:0] sh_cl_hmc_rdata[NUM_HMC-1:0];
logic[1:0] sh_cl_hmc_rresp[NUM_HMC-1:0];
logic[NUM_HMC-1:0] sh_cl_hmc_rlast;
logic[NUM_HMC-1:0] sh_cl_hmc_rvalid;
logic[NUM_HMC-1:0] cl_sh_hmc_rready;

logic[NUM_HMC-1:0] sh_cl_hmc_is_ready;

logic [7:0] sh_ddr_stat_addr_q[2:0];
logic[2:0] sh_ddr_stat_wr_q;
logic[2:0] sh_ddr_stat_rd_q; 
logic[31:0] sh_ddr_stat_wdata_q[2:0];
logic[2:0] ddr_sh_stat_ack_q;
logic[31:0] ddr_sh_stat_rdata_q[2:0];
logic[7:0] ddr_sh_stat_int_q[2:0];

logic[7:0] sh_hmc_stat_addr_q;
logic sh_hmc_stat_wr_q;
logic sh_hmc_stat_rd_q;
logic[31:0] sh_hmc_stat_wdata_q;

logic hmc_sh_stat_ack_q;
logic[31:0] hmc_sh_stat_rdata_q;

logic[7:0] hmc_sh_stat_int_q;

logic [7:0] sh_aurora_stat_addr_q;
logic sh_aurora_stat_wr_q; 
logic sh_aurora_stat_rd_q; 
logic [31:0] sh_aurora_stat_wdata_q; 
logic aurora_sh_stat_ack_q;
logic[31:0] aurora_sh_stat_rdata_q;
logic[7:0] aurora_sh_stat_int_q;

   logic[63:0] sh_cl_pcis_awaddr;
   logic[5:0] sh_cl_pcis_awid;
   logic[7:0] sh_cl_pcis_awlen;
   logic sh_cl_pcis_awvalid;
   logic cl_sh_pcis_awready;
   
   logic[511:0] sh_cl_pcis_wdata;
   logic[63:0] sh_cl_pcis_wstrb;
   logic sh_cl_pcis_wlast;
   logic sh_cl_pcis_wvalid;
   logic cl_sh_pcis_wready;
   
   logic[1:0] cl_sh_pcis_bresp;
   logic[5:0] cl_sh_pcis_bid;
   logic cl_sh_pcis_bvalid;
   logic sh_cl_pcis_bready;
   
   logic[63:0] sh_cl_pcis_araddr;
   logic[5:0] sh_cl_pcis_arid;
   logic[7:0] sh_cl_pcis_arlen;
   logic sh_cl_pcis_arvalid;
   logic cl_sh_pcis_arready;
   
   logic[511:0] cl_sh_pcis_rdata;
   logic[1:0] cl_sh_pcis_rresp;
   logic[5:0] cl_sh_pcis_rid;
   logic cl_sh_pcis_rlast;
   logic cl_sh_pcis_rvalid;
   logic sh_cl_pcis_rready;


logic pre_sync_rst_n;
logic sync_rst_n;

logic pipe_rst_n;

logic sh_cl_flr_assert_q;

logic sda_cl_awvalid_q;
logic[31:0] sda_cl_awaddr_q;
logic cl_sda_awready_q;

logic sda_cl_wvalid_q;
logic[31:0] sda_cl_wdata_q;
logic[3:0] sda_cl_wstrb_q;
logic cl_sda_wready_q;

logic cl_sda_bvalid_q;
logic[1:0] cl_sda_bresp_q;
logic sda_cl_bready_q;

logic sda_cl_arvalid_q;
logic[31:0] sda_cl_araddr_q;
logic cl_sda_arready_q;

logic cl_sda_rvalid_q;
logic[31:0] cl_sda_rdata_q;
logic[1:0] cl_sda_rresp_q;

logic sda_cl_rready_q;

logic sh_ocl_awvalid_q;
logic[31:0] sh_ocl_awaddr_q;
logic ocl_sh_awready_q;
                                                                                                                               
logic sh_ocl_wvalid_q;
logic[31:0] sh_ocl_wdata_q;
logic[3:0] sh_ocl_wstrb_q;
logic ocl_sh_wready_q;
                                                                                                                               
logic ocl_sh_bvalid_q;
logic[1:0] ocl_sh_bresp_q;
logic sh_ocl_bready_q;
                                                                                                                               
logic sh_ocl_arvalid_q;
logic[31:0] sh_ocl_araddr_q;
logic ocl_sh_arready_q;
                                                                                                                               
logic ocl_sh_rvalid_q;
logic[31:0] ocl_sh_rdata_q;
logic[1:0] ocl_sh_rresp_q;
                                                                                                                               
logic sh_ocl_rready_q;

logic sh_bar1_awvalid_q;
logic[31:0] sh_bar1_awaddr_q;
logic bar1_sh_awready_q;
                                                                                                                               
logic sh_bar1_wvalid_q;
logic[31:0] sh_bar1_wdata_q;
logic[3:0] sh_bar1_wstrb_q;
logic bar1_sh_wready_q;
                                                                                                                               
logic bar1_sh_bvalid_q;
logic[1:0] bar1_sh_bresp_q;
logic sh_bar1_bready_q;
                                                                                                                               
logic sh_bar1_arvalid_q;
logic[31:0] sh_bar1_araddr_q;
logic bar1_sh_arready_q;
                                                                                                                               
logic bar1_sh_rvalid_q;
logic[31:0] bar1_sh_rdata_q;
logic[1:0] bar1_sh_rresp_q;
                                                                                                                               
logic sh_bar1_rready_q;   
// End internal signals
//-----------------------------

`ifdef SH_SDA
   logic clk;
   assign clk = clk_main_a0;
`endif
   

assign cl_sh_ddr_wid = 0;

   // FOR TIMING PATHS

lib_pipe #(.WIDTH(1), .STAGES(4)) PIPE_RST_N (.clk(clk), .rst_n(1'b1), .in_bus(rst_main_n), .out_bus(pipe_rst_n));

   
always_ff @(negedge pipe_rst_n or posedge clk)
   if (!pipe_rst_n)
   begin
      pre_sync_rst_n <= 0;
      sync_rst_n <= 0;
   end
   else
   begin
      pre_sync_rst_n <= 1;
      sync_rst_n <= pre_sync_rst_n;
   end

   logic [31:0]                sh_cl_ctl0_q;
   logic [3:0]                 ddr_scrb_en;
   logic [1:0]                 hmc_scrb_en;
   logic [3:0]                 ddr_scrb_en_pipe;
   logic [1:0]                 hmc_scrb_en_pipe;
   logic [3:0]                 ddr_scrb_done;
   logic [1:0]                 hmc_scrb_done;
   logic [3:0]                 ddr_scrb_done_pipe;
   logic [1:0]                 hmc_scrb_done_pipe;
   logic [3:0]                 all_ddr_scrb_done;

   logic [2:0]                 dbg_scrb_mem_sel;
   logic                       dbg_scrb_en;
   logic [63:0]                dbg_ddr_scrb_addr [3:0];
   logic [2:0]                 dbg_ddr_scrb_state [3:0];
   logic [63:0]                dbg_ddr_scrb_addr_pipe [3:0];
   logic [2:0]                 dbg_ddr_scrb_state_pipe [3:0];
   
   // Bit 31: Debug enable (for cl_sh_id0 and cl_sh_id1)
   // Bit 30:28: Debug Scrb memory select
   
   // Bit 5 : HMC1 Scrub enable
   // Bit 4 : HMC0 Scrub enable
   // Bit 3 : DDR3 Scrub enable
   // Bit 2 : DDR2 Scrub enable
   // Bit 1 : DDR1 Scrub enable
   // Bit 0 : DDR0 Scrub enable
   always_ff @(posedge clk or negedge sync_rst_n)
     if (!sync_rst_n)
       sh_cl_ctl0_q <= 32'd0;
     else
       sh_cl_ctl0_q <= sh_cl_ctl0;

   // Create force starts
   
   assign ddr_scrb_en = {sh_cl_ctl0_q[2] , sh_cl_ctl0_q[3], sh_cl_ctl0_q[1:0]};
   assign hmc_scrb_en = sh_cl_ctl0_q[5:4];

   assign dbg_scrb_en = sh_cl_ctl0_q[31];
   assign dbg_scrb_mem_sel[2:0] = sh_cl_ctl0_q[30:28];

   logic [5:0]                 sh_cl_dma_pcis_awid_q;
   logic [63:0]                sh_cl_dma_pcis_awaddr_q;
   logic [7:0] sh_cl_dma_pcis_awlen_q;
   logic         sh_cl_dma_pcis_awvalid_q;
   logic         cl_sh_dma_pcis_awready_q;

   logic [511:0]                sh_cl_dma_pcis_wdata_q;
   logic [63:0]                 sh_cl_dma_pcis_wstrb_q;
   logic         sh_cl_dma_pcis_wlast_q;
   logic         sh_cl_dma_pcis_wvalid_q;
   logic         cl_sh_dma_pcis_wready_q;

   logic [5:0]                 cl_sh_dma_pcis_bid_q;
   logic [1:0]                 cl_sh_dma_pcis_bresp_q;
   logic         cl_sh_dma_pcis_bvalid_q;
   logic         sh_cl_dma_pcis_bready_q;

   logic [5:0]                 sh_cl_dma_pcis_arid_q;
   logic [63:0]                sh_cl_dma_pcis_araddr_q;
   logic [7:0] sh_cl_dma_pcis_arlen_q;
   logic         sh_cl_dma_pcis_arvalid_q;
   logic         cl_sh_dma_pcis_arready_q;

   logic [511:0]               cl_sh_dma_pcis_rdata_q;
   logic [5:0]                 cl_sh_dma_pcis_rid_q;
   logic [1:0]                 cl_sh_dma_pcis_rresp_q;
   logic         cl_sh_dma_pcis_rlast_q;
   logic         cl_sh_dma_pcis_rvalid_q;
   logic         sh_cl_dma_pcis_rready_q;

`ifndef NO_CL_PCI_AXL_REG_SLC
   
 // AXI-Lite Register Slice for signals between CL and HL
   axi4_flop_fifo #(.IN_FIFO(1), .ADDR_WIDTH(64), .DATA_WIDTH(512), .ID_WIDTH(6), .A_USER_WIDTH(1), .FIFO_DEPTH(3)) PCI_AXL_REG_SLC (
    .aclk          (clk),
    .aresetn       (sync_rst_n),
    .sync_rst_n    (1'b1),
    .s_axi_awid    (sh_cl_dma_pcis_awid),
    .s_axi_awaddr  (sh_cl_dma_pcis_awaddr),
    .s_axi_awlen   (sh_cl_dma_pcis_awlen),                                            
    .s_axi_awvalid (sh_cl_dma_pcis_awvalid),
    .s_axi_awuser  (),
    .s_axi_awready (cl_sh_dma_pcis_awready),
    .s_axi_wdata   (sh_cl_dma_pcis_wdata),
    .s_axi_wstrb   (sh_cl_dma_pcis_wstrb),
    .s_axi_wlast   (sh_cl_dma_pcis_wlast),
    .s_axi_wuser   (),
    .s_axi_wvalid  (sh_cl_dma_pcis_wvalid),
    .s_axi_wready  (cl_sh_dma_pcis_wready),
    .s_axi_bid     (cl_sh_dma_pcis_bid),
    .s_axi_bresp   (cl_sh_dma_pcis_bresp),
    .s_axi_bvalid  (cl_sh_dma_pcis_bvalid),
    .s_axi_buser   (),
    .s_axi_bready  (sh_cl_dma_pcis_bready),
    .s_axi_arid    (sh_cl_dma_pcis_arid),
    .s_axi_araddr  (sh_cl_dma_pcis_araddr),
    .s_axi_arlen   (sh_cl_dma_pcis_arlen), 
    .s_axi_arvalid (sh_cl_dma_pcis_arvalid),
    .s_axi_aruser  (1'd0),
    .s_axi_arready (cl_sh_dma_pcis_arready),
    .s_axi_rid     (cl_sh_dma_pcis_rid),
    .s_axi_rdata   (cl_sh_dma_pcis_rdata),
    .s_axi_rresp   (cl_sh_dma_pcis_rresp),
    .s_axi_rlast   (cl_sh_dma_pcis_rlast),
    .s_axi_ruser   (),
    .s_axi_rvalid  (cl_sh_dma_pcis_rvalid),
    .s_axi_rready  (sh_cl_dma_pcis_rready), 
    .m_axi_awid    (sh_cl_dma_pcis_awid_q),
    .m_axi_awaddr  (sh_cl_dma_pcis_awaddr_q), 
    .m_axi_awlen   (sh_cl_dma_pcis_awlen_q),
    .m_axi_awvalid (sh_cl_dma_pcis_awvalid_q),
    .m_axi_awuser  (),
    .m_axi_awready (cl_sh_dma_pcis_awready_q),
    .m_axi_wdata   (sh_cl_dma_pcis_wdata_q),  
    .m_axi_wstrb   (sh_cl_dma_pcis_wstrb_q),
    .m_axi_wvalid  (sh_cl_dma_pcis_wvalid_q), 
    .m_axi_wlast   (sh_cl_dma_pcis_wlast_q),
    .m_axi_wuser   (),
    .m_axi_wready  (cl_sh_dma_pcis_wready_q), 
    .m_axi_bresp   (cl_sh_dma_pcis_bresp_q),  
    .m_axi_bvalid  (cl_sh_dma_pcis_bvalid_q), 
    .m_axi_bid     (cl_sh_dma_pcis_bid_q),
    .m_axi_buser   (),
    .m_axi_bready  (sh_cl_dma_pcis_bready_q), 
    .m_axi_arid    (sh_cl_dma_pcis_arid_q), 
    .m_axi_araddr  (sh_cl_dma_pcis_araddr_q), 
    .m_axi_arlen   (sh_cl_dma_pcis_arlen_q), 
    .m_axi_aruser  (), 
    .m_axi_arvalid (sh_cl_dma_pcis_arvalid_q),
    .m_axi_arready (cl_sh_dma_pcis_arready_q),
    .m_axi_rid     (cl_sh_dma_pcis_rid_q),  
    .m_axi_rdata   (cl_sh_dma_pcis_rdata_q),  
    .m_axi_rresp   (cl_sh_dma_pcis_rresp_q),  
    .m_axi_rlast   (cl_sh_dma_pcis_rlast_q),  
    .m_axi_ruser   (1'b0),
    .m_axi_rvalid  (cl_sh_dma_pcis_rvalid_q), 
    .m_axi_rready  (sh_cl_dma_pcis_rready_q)
   );

`else // !`ifndef NO_CL_PCI_AXL_REG_SLC
   
   assign sh_cl_dma_pcis_awid_q  = sh_cl_dma_pcis_awid ;
   assign sh_cl_dma_pcis_awaddr_q  = sh_cl_dma_pcis_awaddr ;
   assign sh_cl_dma_pcis_awvalid_q = sh_cl_dma_pcis_awvalid;
   assign cl_sh_dma_pcis_awready = cl_sh_dma_pcis_awready_q;
   
   assign sh_cl_dma_pcis_wdata_q   = sh_cl_dma_pcis_wdata  ;
   assign sh_cl_dma_pcis_wstrb_q   = sh_cl_dma_pcis_wstrb  ;
   assign sh_cl_dma_pcis_wvalid_q  = sh_cl_dma_pcis_wvalid ;
   assign cl_sh_dma_pcis_wready  = cl_sh_dma_pcis_wready_q ;
   
   assign cl_sh_dma_pcis_bid     = cl_sh_dma_pcis_bid_q    ;
   assign cl_sh_dma_pcis_bresp   = cl_sh_dma_pcis_bresp_q  ;
   assign cl_sh_dma_pcis_bvalid  = cl_sh_dma_pcis_bvalid_q ;
   assign sh_cl_dma_pcis_bready_q  = sh_cl_dma_pcis_bready ;
   
   assign sh_cl_dma_pcis_arid_q    = sh_cl_dma_pcis_arid ;
   assign sh_cl_dma_pcis_araddr_q  = sh_cl_dma_pcis_araddr ;
   assign sh_cl_dma_pcis_arvalid_q = sh_cl_dma_pcis_arvalid;
   assign cl_sh_dma_pcis_arready   = cl_sh_dma_pcis_arready_q;
   
   assign cl_sh_dma_pcis_rdata   = cl_sh_dma_pcis_rdata_q  ;
   assign cl_sh_dma_pcis_rid     = cl_sh_dma_pcis_rid_q  ;
   assign cl_sh_dma_pcis_rresp   = cl_sh_dma_pcis_rresp_q  ;
   assign cl_sh_dma_pcis_rvalid  = cl_sh_dma_pcis_rvalid_q ;
   assign cl_sh_dma_pcis_rlast   = cl_sh_dma_pcis_rlast_q ;
   assign sh_cl_dma_pcis_rready_q  = sh_cl_dma_pcis_rready ;

`endif // !`ifndef NO_CL_PCI_AXL_REG_SLC

   logic [4:0]                 cl_sh_pcim_awid_q;
   logic [63:0]                cl_sh_pcim_awaddr_q;
   logic [7:0]                 cl_sh_pcim_awlen_q;
   logic [18:0]                cl_sh_pcim_awuser_q; //DW length of transfer
   logic         cl_sh_pcim_awvalid_q;
   logic         sh_cl_pcim_awready_q;

   //   logic [4:0]                 cl_sh_pcim_wid_q;
   logic [511:0]               cl_sh_pcim_wdata_q;
   logic [63:0]                cl_sh_pcim_wstrb_q;
   logic         cl_sh_pcim_wlast_q;
   logic         cl_sh_pcim_wvalid_q;
   logic         sh_cl_pcim_wready_q;

   logic [4:0]                 sh_cl_pcim_bid_q;
   logic [10:0]                dummy_sh_cl_pcim_bid_q;
   logic [1:0]                 sh_cl_pcim_bresp_q;
   logic         sh_cl_pcim_bvalid_q;
   logic         cl_sh_pcim_bready_q;

   logic [4:0]                 cl_sh_pcim_arid_q;
   logic [63:0]                cl_sh_pcim_araddr_q;
   logic [7:0]                 cl_sh_pcim_arlen_q;
   logic [18:0]                cl_sh_pcim_aruser_q; //DW length of transfer
   logic         cl_sh_pcim_arvalid_q;
   logic         sh_cl_pcim_arready_q;

   logic [4:0]                 sh_cl_pcim_rid_q;
   logic [10:0]                dummy_sh_cl_pcim_rid_q;
   logic [511:0]               sh_cl_pcim_rdata_q;
   logic [1:0]                 sh_cl_pcim_rresp_q;
   logic         sh_cl_pcim_rlast_q;
   logic         sh_cl_pcim_rvalid_q;
   logic         cl_sh_pcim_rready_q;

`ifndef NO_CL_PCI_AXI4_REG_SLC
   
   // AXI4 register slice - For signals between CL and HL
   axi4_flop_fifo #(.ADDR_WIDTH(64), .DATA_WIDTH(512), .ID_WIDTH(16), .A_USER_WIDTH(19), .FIFO_DEPTH(3)) PCI_AXI4_REG_SLC (
     .aclk           (clk),
     .aresetn        (sync_rst_n),
     .sync_rst_n     (1'b1),
                                                                                                                         
     .s_axi_awid     ({11'b0, cl_sh_pcim_awid_q}),
     .s_axi_awaddr   (cl_sh_pcim_awaddr_q),
     .s_axi_awlen    (cl_sh_pcim_awlen_q),
     .s_axi_awuser   (cl_sh_pcim_awuser_q),
     .s_axi_awvalid  (cl_sh_pcim_awvalid_q),
     .s_axi_awready  (sh_cl_pcim_awready_q),
     .s_axi_wdata    (cl_sh_pcim_wdata_q),
     .s_axi_wstrb    (cl_sh_pcim_wstrb_q),
     .s_axi_wlast    (cl_sh_pcim_wlast_q),
     .s_axi_wuser    (),
     .s_axi_wvalid   (cl_sh_pcim_wvalid_q),
     .s_axi_wready   (sh_cl_pcim_wready_q),
     .s_axi_bid      ({dummy_sh_cl_pcim_bid_q, sh_cl_pcim_bid_q}),
     .s_axi_bresp    (sh_cl_pcim_bresp_q),
     .s_axi_buser    (),
     .s_axi_bvalid   (sh_cl_pcim_bvalid_q),
     .s_axi_bready   (cl_sh_pcim_bready_q),
     .s_axi_arid     ({11'b0, cl_sh_pcim_arid_q}),
     .s_axi_araddr   (cl_sh_pcim_araddr_q),
     .s_axi_arlen    (cl_sh_pcim_arlen_q),
     .s_axi_aruser   (cl_sh_pcim_aruser_q),
     .s_axi_arvalid  (cl_sh_pcim_arvalid_q),
     .s_axi_arready  (sh_cl_pcim_arready_q),
     .s_axi_rid      ({dummy_sh_cl_pcim_rid_q, sh_cl_pcim_rid_q}),
     .s_axi_rdata    (sh_cl_pcim_rdata_q),
     .s_axi_rresp    (sh_cl_pcim_rresp_q),
     .s_axi_rlast    (sh_cl_pcim_rlast_q),
     .s_axi_ruser    (),
     .s_axi_rvalid   (sh_cl_pcim_rvalid_q),
     .s_axi_rready   (cl_sh_pcim_rready_q),  
     .m_axi_awid     (cl_sh_pcim_awid),   
     .m_axi_awaddr   (cl_sh_pcim_awaddr), 
     .m_axi_awlen    (cl_sh_pcim_awlen),  
     .m_axi_awuser   (cl_sh_pcim_awuser), 
     .m_axi_awvalid  (cl_sh_pcim_awvalid),
     .m_axi_awready  (sh_cl_pcim_awready),
     .m_axi_wdata    (cl_sh_pcim_wdata),  
     .m_axi_wstrb    (cl_sh_pcim_wstrb),  
     .m_axi_wlast    (cl_sh_pcim_wlast),  
     .m_axi_wuser    (),
     .m_axi_wvalid   (cl_sh_pcim_wvalid), 
     .m_axi_wready   (sh_cl_pcim_wready), 
     .m_axi_bid      (sh_cl_pcim_bid),    
     .m_axi_bresp    (sh_cl_pcim_bresp),  
     .m_axi_bvalid   (sh_cl_pcim_bvalid), 
     .m_axi_buser    (),
     .m_axi_bready   (cl_sh_pcim_bready), 
     .m_axi_arid     (cl_sh_pcim_arid),   
     .m_axi_araddr   (cl_sh_pcim_araddr), 
     .m_axi_arlen    (cl_sh_pcim_arlen),  
     .m_axi_aruser   (cl_sh_pcim_aruser), 
     .m_axi_arvalid  (cl_sh_pcim_arvalid),
     .m_axi_arready  (sh_cl_pcim_arready),
     .m_axi_rid      (sh_cl_pcim_rid),    
     .m_axi_rdata    (sh_cl_pcim_rdata),  
     .m_axi_rresp    (sh_cl_pcim_rresp),  
     .m_axi_rlast    (sh_cl_pcim_rlast),  
     .m_axi_rvalid   (sh_cl_pcim_rvalid), 
     .m_axi_ruser    (),
     .m_axi_rready   (cl_sh_pcim_rready)
     );

`else // !`ifndef NO_CL_PCI_AXI4_REG_SLC
   
   assign cl_sh_pcim_awid  = {11'b0, cl_sh_pcim_awid_q} ;
   assign cl_sh_pcim_awaddr  = cl_sh_pcim_awaddr_q ;
   assign cl_sh_pcim_awlen  = cl_sh_pcim_awlen_q ;
   assign cl_sh_pcim_awuser  = cl_sh_pcim_awuser_q ;
   assign cl_sh_pcim_awvalid = cl_sh_pcim_awvalid_q;
   assign sh_cl_pcim_awready_q = sh_cl_pcim_awready;
   
   assign cl_sh_pcim_wdata   = cl_sh_pcim_wdata_q  ;
   assign cl_sh_pcim_wstrb   = cl_sh_pcim_wstrb_q  ;
   assign cl_sh_pcim_wlast   = cl_sh_pcim_wlast_q  ;
   assign cl_sh_pcim_wvalid  = cl_sh_pcim_wvalid_q ;
   assign sh_cl_pcim_wready_q  = sh_cl_pcim_wready ;
   
   assign {dummy_sh_cl_pcim_bid_q, sh_cl_pcim_bid_q}   = sh_cl_pcim_bid  ;
   assign sh_cl_pcim_bresp_q   = sh_cl_pcim_bresp  ;
   assign sh_cl_pcim_bvalid_q  = sh_cl_pcim_bvalid ;
   assign cl_sh_pcim_bready  = cl_sh_pcim_bready_q ;
   
   assign cl_sh_pcim_arid  = {11'b0, cl_sh_pcim_arid_q} ;
   assign cl_sh_pcim_araddr  = cl_sh_pcim_araddr_q ;
   assign cl_sh_pcim_arlen  = cl_sh_pcim_arlen_q ;
   assign cl_sh_pcim_aruser  = cl_sh_pcim_aruser_q ;
   assign cl_sh_pcim_arvalid = cl_sh_pcim_arvalid_q;
   assign sh_cl_pcim_arready_q = sh_cl_pcim_arready;
   
   assign {dummy_sh_cl_pcim_rid_q, sh_cl_pcim_rid_q}   = sh_cl_pcim_rid  ;
   assign sh_cl_pcim_rdata_q   = sh_cl_pcim_rdata  ;
   assign sh_cl_pcim_rresp_q   = sh_cl_pcim_rresp  ;
   assign sh_cl_pcim_rlast_q   = sh_cl_pcim_rlast  ;
   assign sh_cl_pcim_rvalid_q  = sh_cl_pcim_rvalid ;
   assign cl_sh_pcim_rready  = cl_sh_pcim_rready_q ;

`endif // !`ifndef NO_CL_PCI_AXI4_REG_SLC
      
   logic [5:0]                 cl_sh_ddr_awid_q;
   logic [63:0]                cl_sh_ddr_awaddr_q;
   logic [7:0]                 cl_sh_ddr_awlen_q;
   logic                       cl_sh_ddr_awvalid_q;
   logic                       sh_cl_ddr_awready_q;

   logic [511:0]               cl_sh_ddr_wdata_q;
   logic [63:0]                cl_sh_ddr_wstrb_q;
   logic                       cl_sh_ddr_wlast_q;
   logic                       cl_sh_ddr_wvalid_q;
   logic                       sh_cl_ddr_wready_q;

   logic [5:0]                 sh_cl_ddr_bid_q;
   logic [9:0]                 dummy_sh_cl_ddr_bid_q;
   logic [1:0]                 sh_cl_ddr_bresp_q;
   logic                       sh_cl_ddr_bvalid_q;
   logic                       cl_sh_ddr_bready_q;

   logic [5:0]                 cl_sh_ddr_arid_q;
   logic [63:0]                cl_sh_ddr_araddr_q;
   logic [7:0]                 cl_sh_ddr_arlen_q;
   logic                       cl_sh_ddr_arvalid_q;
   logic                       sh_cl_ddr_arready_q;

   logic [5:0]                 sh_cl_ddr_rid_q;
   logic [9:0]                 dummy_sh_cl_ddr_rid_q;
   logic [511:0]               sh_cl_ddr_rdata_q;
   logic [1:0]                 sh_cl_ddr_rresp_q;
   logic                       sh_cl_ddr_rlast_q;
   logic                       sh_cl_ddr_rvalid_q;
   logic                       cl_sh_ddr_rready_q;

   logic [5:0]                 cl_sh_ddr_awid_q2;
   logic [63:0]                cl_sh_ddr_awaddr_q2;
   logic [7:0]                 cl_sh_ddr_awlen_q2;
   logic                       cl_sh_ddr_awvalid_q2;
   logic                       sh_cl_ddr_awready_q2;

   logic [511:0]               cl_sh_ddr_wdata_q2;
   logic [63:0]                cl_sh_ddr_wstrb_q2;
   logic                       cl_sh_ddr_wlast_q2;
   logic                       cl_sh_ddr_wvalid_q2;
   logic                       sh_cl_ddr_wready_q2;

   logic [5:0]                 sh_cl_ddr_bid_q2;
   logic [9:0]                 dummy_sh_cl_ddr_bid_q2;
   logic [1:0]                 sh_cl_ddr_bresp_q2;
   logic                       sh_cl_ddr_bvalid_q2;
   logic                       cl_sh_ddr_bready_q2;

   logic [5:0]                 cl_sh_ddr_arid_q2;
   logic [63:0]                cl_sh_ddr_araddr_q2;
   logic [7:0]                 cl_sh_ddr_arlen_q2;
   logic                       cl_sh_ddr_arvalid_q2;
   logic                       sh_cl_ddr_arready_q2;

   logic [5:0]                 sh_cl_ddr_rid_q2;
   logic [9:0]                 dummy_sh_cl_ddr_rid_q2;
   logic [511:0]               sh_cl_ddr_rdata_q2;
   logic [1:0]                 sh_cl_ddr_rresp_q2;
   logic                       sh_cl_ddr_rlast_q2;
   logic                       sh_cl_ddr_rvalid_q2;
   logic                       cl_sh_ddr_rready_q2;

   logic [5:0]                 cl_sh_ddr_awid_q3;
   logic [63:0]                cl_sh_ddr_awaddr_q3;
   logic [7:0]                 cl_sh_ddr_awlen_q3;
   logic                       cl_sh_ddr_awvalid_q3;
   logic                       sh_cl_ddr_awready_q3;

   logic [511:0]               cl_sh_ddr_wdata_q3;
   logic [63:0]                cl_sh_ddr_wstrb_q3;
   logic                       cl_sh_ddr_wlast_q3;
   logic                       cl_sh_ddr_wvalid_q3;
   logic                       sh_cl_ddr_wready_q3;

   logic [5:0]                 sh_cl_ddr_bid_q3;
   logic [9:0]                 dummy_sh_cl_ddr_bid_q3;
   logic [1:0]                 sh_cl_ddr_bresp_q3;
   logic                       sh_cl_ddr_bvalid_q3;
   logic                       cl_sh_ddr_bready_q3;

   logic [5:0]                 cl_sh_ddr_arid_q3;
   logic [63:0]                cl_sh_ddr_araddr_q3;
   logic [7:0]                 cl_sh_ddr_arlen_q3;
   logic                       cl_sh_ddr_arvalid_q3;
   logic                       sh_cl_ddr_arready_q3;

   logic [5:0]                 sh_cl_ddr_rid_q3;
   logic [9:0]                 dummy_sh_cl_ddr_rid_q3;
   logic [511:0]               sh_cl_ddr_rdata_q3;
   logic [1:0]                 sh_cl_ddr_rresp_q3;
   logic                       sh_cl_ddr_rlast_q3;
   logic                       sh_cl_ddr_rvalid_q3;
   logic                       cl_sh_ddr_rready_q3;


`ifndef NO_CL_DDR_TST_3_AXI4_REG_SLC
   
   // AXI4 register slice - For signals between CL and HL
   axi4_flop_fifo #(.ADDR_WIDTH(64), .DATA_WIDTH(512), .ID_WIDTH(6), .A_USER_WIDTH(1), .FIFO_DEPTH(3)) DDR_TST_3_AXI4_REG_SLC (
     .aclk           (clk),
     .aresetn        (sync_rst_n),
     .sync_rst_n     (1'b1),
                                                                                                                                
     .s_axi_awid     (cl_sh_ddr_awid_q),
     .s_axi_awaddr   ({cl_sh_ddr_awaddr_q[63:32], 2'b0, cl_sh_ddr_awaddr_q[29:0]}),
     .s_axi_awlen    (cl_sh_ddr_awlen_q),
     .s_axi_awuser   (1'b0),
     .s_axi_awvalid  (cl_sh_ddr_awvalid_q),
     .s_axi_awready  (sh_cl_ddr_awready_q),
     .s_axi_wdata    (cl_sh_ddr_wdata_q),
     .s_axi_wstrb    (cl_sh_ddr_wstrb_q),
     .s_axi_wlast    (cl_sh_ddr_wlast_q),
     .s_axi_wvalid   (cl_sh_ddr_wvalid_q),
     .s_axi_wuser    (),
     .s_axi_wready   (sh_cl_ddr_wready_q),
     .s_axi_bid      (sh_cl_ddr_bid_q),
     .s_axi_bresp    (sh_cl_ddr_bresp_q),
     .s_axi_bvalid   (sh_cl_ddr_bvalid_q),
     .s_axi_buser    (),
     .s_axi_bready   (cl_sh_ddr_bready_q),
     .s_axi_arid     (cl_sh_ddr_arid_q),
     .s_axi_araddr   ({cl_sh_ddr_araddr_q[63:32], 2'b0, cl_sh_ddr_araddr_q[29:0]}),
     .s_axi_arlen    (cl_sh_ddr_arlen_q),
     .s_axi_aruser   (1'b0),
     .s_axi_arvalid  (cl_sh_ddr_arvalid_q),
     .s_axi_arready  (sh_cl_ddr_arready_q),
     .s_axi_rid      (sh_cl_ddr_rid_q),
     .s_axi_rdata    (sh_cl_ddr_rdata_q),
     .s_axi_rresp    (sh_cl_ddr_rresp_q),
     .s_axi_rlast    (sh_cl_ddr_rlast_q),
     .s_axi_ruser    (),
     .s_axi_rvalid   (sh_cl_ddr_rvalid_q),
     .s_axi_rready   (cl_sh_ddr_rready_q),  
     .m_axi_awid     (cl_sh_ddr_awid_q2),   
     .m_axi_awaddr   (cl_sh_ddr_awaddr_q2), 
     .m_axi_awlen    (cl_sh_ddr_awlen_q2),  
     .m_axi_awuser   (),
     .m_axi_awvalid  (cl_sh_ddr_awvalid_q2),
     .m_axi_awready  (sh_cl_ddr_awready_q2),
     .m_axi_wdata    (cl_sh_ddr_wdata_q2),  
     .m_axi_wstrb    (cl_sh_ddr_wstrb_q2),  
     .m_axi_wuser    (),
     .m_axi_wlast    (cl_sh_ddr_wlast_q2),  
     .m_axi_wvalid   (cl_sh_ddr_wvalid_q2), 
     .m_axi_wready   (sh_cl_ddr_wready_q2), 
     .m_axi_bid      (sh_cl_ddr_bid_q2),    
     .m_axi_bresp    (sh_cl_ddr_bresp_q2),  
     .m_axi_buser    (),
     .m_axi_bvalid   (sh_cl_ddr_bvalid_q2), 
     .m_axi_bready   (cl_sh_ddr_bready_q2), 
     .m_axi_arid     (cl_sh_ddr_arid_q2),   
     .m_axi_araddr   (cl_sh_ddr_araddr_q2), 
     .m_axi_arlen    (cl_sh_ddr_arlen_q2),  
     .m_axi_aruser   (),
     .m_axi_arvalid  (cl_sh_ddr_arvalid_q2),
     .m_axi_arready  (sh_cl_ddr_arready_q2),
     .m_axi_rid      (sh_cl_ddr_rid_q2),    
     .m_axi_rdata    (sh_cl_ddr_rdata_q2),  
     .m_axi_rresp    (sh_cl_ddr_rresp_q2),  
     .m_axi_ruser    (),
     .m_axi_rlast    (sh_cl_ddr_rlast_q2),  
     .m_axi_rvalid   (sh_cl_ddr_rvalid_q2), 
     .m_axi_rready   (cl_sh_ddr_rready_q2)
     );
`else // !`ifndef NO_CL_DDR_TST_3_AXI4_REG_SLC
   
   assign cl_sh_ddr_awid  = {10'b0, cl_sh_ddr_awid_q} ;
   assign cl_sh_ddr_awaddr  = cl_sh_ddr_awaddr_q ;
   assign cl_sh_ddr_awlen  = cl_sh_ddr_awlen_q ;
   assign cl_sh_ddr_awvalid = cl_sh_ddr_awvalid_q;
   assign sh_cl_ddr_awready_q = sh_cl_ddr_awready;
   
   assign cl_sh_ddr_wdata   = cl_sh_ddr_wdata_q  ;
   assign cl_sh_ddr_wstrb   = cl_sh_ddr_wstrb_q  ;
   assign cl_sh_ddr_wlast   = cl_sh_ddr_wlast_q  ;
   assign cl_sh_ddr_wvalid  = cl_sh_ddr_wvalid_q ;
   assign sh_cl_ddr_wready_q  = sh_cl_ddr_wready ;
   
   assign {dummy_sh_cl_ddr_bid_q, sh_cl_ddr_bid_q}   = sh_cl_ddr_bid  ;
   assign sh_cl_ddr_bresp_q   = sh_cl_ddr_bresp  ;
   assign sh_cl_ddr_bvalid_q  = sh_cl_ddr_bvalid ;
   assign cl_sh_ddr_bready  = cl_sh_ddr_bready_q ;
   
   assign cl_sh_ddr_arid  = {10'b0, cl_sh_ddr_arid_q} ;
   assign cl_sh_ddr_araddr  = cl_sh_ddr_araddr_q ;
   assign cl_sh_ddr_arlen  = cl_sh_ddr_arlen_q ;
   assign cl_sh_ddr_arvalid = cl_sh_ddr_arvalid_q;
   assign sh_cl_ddr_arready_q = sh_cl_ddr_arready;
   
   assign {dummy_sh_cl_ddr_rid_q, sh_cl_ddr_rid_q}   = sh_cl_ddr_rid  ;
   assign sh_cl_ddr_rdata_q   = sh_cl_ddr_rdata  ;
   assign sh_cl_ddr_rresp_q   = sh_cl_ddr_rresp  ;
   assign sh_cl_ddr_rlast_q   = sh_cl_ddr_rlast  ;
   assign sh_cl_ddr_rvalid_q  = sh_cl_ddr_rvalid ;
   assign cl_sh_ddr_rready  = cl_sh_ddr_rready_q ;

`endif // !`ifndef NO_CL_DDR_TST_3_AXI4_REG_SLC
   

//-------------------------------------------------
// Slave state machine (accesses from PCIe)
//-------------------------------------------------
//`ifdef MSIX_PRESENT
//parameter NUM_TST = (NUM_PCIE + NUM_DDR + NUM_HMC + NUM_GTY + 1);
//`else
//parameter NUM_TST = (NUM_PCIE + NUM_DDR + NUM_HMC + NUM_GTY);
//`endif   

parameter NUM_TST = (1 + 4 + 4 + 4 + 1 + 2);

typedef enum logic[2:0] {
   SLV_IDLE = 0,
   SLV_WR_ADDR = 1,
   SLV_CYC = 2,
   SLV_RESP = 3
   } slv_state_t;

slv_state_t slv_state, slv_state_nxt;

logic slv_arb_wr;                //Arbitration winner (write/read)
logic slv_cyc_wr;                //Cycle is write
logic[31:0] slv_mx_addr;         //Mux address
logic slv_mx_rsp_ready;          //Mux the response ready

logic slv_wr_req;                //Write request
logic slv_rd_req;                //Read request

logic slv_cyc_done;              //Cycle is done

logic[31:0] slv_rdata;           //Latch rdata

logic[7:0] slv_sel;              //Slave select

logic[31:0] slv_tst_addr[NUM_TST-1:0];
logic[31:0] slv_tst_wdata[NUM_TST-1:0];
logic[NUM_TST-1:0] slv_tst_wr;
logic[NUM_TST-1:0] slv_tst_rd;
logic slv_mx_req_valid;

logic[NUM_TST-1:0] tst_slv_ack;
logic[31:0] tst_slv_rdata [NUM_TST-1:0];

logic slv_did_req;            //Once cycle request, latch that did the request


logic[31:0] slv_tst_addr_pipe[NUM_TST-1:0];
logic[31:0] slv_tst_wdata_pipe[NUM_TST-1:0];
logic[NUM_TST-1:0] slv_tst_wr_pipe;
logic[NUM_TST-1:0] slv_tst_rd_pipe;

logic[NUM_TST-1:0] tst_slv_ack_pipe;
logic[31:0] tst_slv_rdata_pipe [NUM_TST-1:0];

logic[31:0] ddr_slv_tst_addr[4-1:0];
logic[31:0] ddr_slv_tst_wdata[4-1:0];
logic[4-1:0] ddr_slv_tst_wr;
logic[4-1:0] ddr_slv_tst_rd;

logic[4-1:0] ddr_tst_slv_ack;
logic[31:0] ddr_tst_slv_rdata [4-1:0];

logic[31:0] ddr_slv_tst_addr_pipe[4-1:0];
logic[31:0] ddr_slv_tst_wdata_pipe[4-1:0];
logic[4-1:0] ddr_slv_tst_wr_pipe;
logic[4-1:0] ddr_slv_tst_rd_pipe;

logic[4-1:0] ddr_tst_slv_ack_pipe;
logic[31:0] ddr_tst_slv_rdata_pipe [4-1:0];

//Write request valid when both address is valid
`ifdef OCL_TG_CTL
   assign slv_wr_req = sh_ocl_awvalid_q;
   assign slv_rd_req = sh_ocl_arvalid_q;
   assign slv_mx_rsp_ready = (slv_cyc_wr)? sh_ocl_bready_q: sh_ocl_rready_q;
   assign slv_mx_req_valid = (slv_cyc_wr)?   sh_ocl_wvalid_q: 1'b1;

`else
   assign slv_wr_req = sh_cl_pcis_awvalid;
   assign slv_rd_req = sh_cl_pcis_arvalid;
   assign slv_mx_rsp_ready = (slv_cyc_wr)? sh_cl_pcis_bready: sh_cl_pcis_rready;
   assign slv_mx_req_valid = (slv_cyc_wr)?   sh_cl_pcis_wvalid: 1'b1;
`endif




//Fixed write hi-pri
assign slv_arb_wr = slv_wr_req;

   logic [63:0] slv_req_rd_addr;
   logic [63:0] slv_req_wr_addr;
   logic [5:0]  slv_req_rd_id;
   logic [5:0]  slv_req_wr_id;


`ifdef OCL_TG_CTL
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n)
      begin
       {slv_req_rd_addr, slv_req_wr_addr} <= 128'd0;
       {slv_req_rd_id, slv_req_wr_id} <= 0;
      end
     else if ((slv_state == SLV_IDLE) && (sh_ocl_arvalid_q || sh_ocl_awvalid_q))
      begin
       {slv_req_rd_addr[31:0], slv_req_wr_addr[31:0]} <= {sh_ocl_araddr_q, sh_ocl_awaddr_q};
       {slv_req_rd_id, slv_req_wr_id} <= 0;
      end

`else    
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n)
      begin
       {slv_req_rd_addr, slv_req_wr_addr} <= 128'd0;
       {slv_req_rd_id, slv_req_wr_id} <= 0;
      end
     else if ((slv_state == SLV_IDLE) && (sh_cl_pcis_arvalid || sh_cl_pcis_awvalid))
      begin
       {slv_req_rd_addr, slv_req_wr_addr} <= {sh_cl_pcis_araddr, sh_cl_pcis_awaddr};
       {slv_req_rd_id, slv_req_wr_id} <= {sh_cl_pcis_arid, sh_cl_pcis_awid};
      end
`endif
   
//Mux address
//assign slv_mx_addr = (slv_cyc_wr)? sh_cl_pcis_awaddr: sh_cl_pcis_araddr;
assign slv_mx_addr = (slv_cyc_wr)? slv_req_wr_addr : slv_req_rd_addr;
   
//Slave select (256B per slave)
//assign slv_sel = slv_mx_addr >> 8;
assign slv_sel = slv_mx_addr[15:8];
   
//Latch the winner
always_ff @(negedge sync_rst_n or posedge clk)
   if (!sync_rst_n)
      slv_cyc_wr <= 0;
   else if (slv_state==SLV_IDLE)
      slv_cyc_wr <= slv_arb_wr;

//State machine
always_comb
begin
   slv_state_nxt = slv_state;
   if (sh_cl_flr_assert_q)
      slv_state_nxt = SLV_IDLE;
   else
   begin
   case (slv_state)

      SLV_IDLE:
      begin
         if (slv_wr_req)
            slv_state_nxt = SLV_WR_ADDR;
         else if (slv_rd_req)
            slv_state_nxt = SLV_CYC;
         else
            slv_state_nxt = SLV_IDLE;
      end

      SLV_WR_ADDR:
      begin
         slv_state_nxt = SLV_CYC;
      end

      SLV_CYC:
      begin
         if (slv_cyc_done)
            slv_state_nxt = SLV_RESP;
         else
            slv_state_nxt = SLV_CYC;
      end

      SLV_RESP:
      begin
         if (slv_mx_rsp_ready)
            slv_state_nxt = SLV_IDLE;
         else
            slv_state_nxt = SLV_RESP;
      end

   endcase
   end
end

//State machine flops
always_ff @(negedge sync_rst_n or posedge clk)
   if (!sync_rst_n)
      slv_state <= SLV_IDLE;
   else
      slv_state <= slv_state_nxt;


//Cycle to TST blocks -- Repliacte for timing

`ifdef OCL_TG_CTL
   always_ff @(negedge sync_rst_n or posedge clk)
      if (!sync_rst_n)
      begin
         slv_tst_addr <= '{default:'0};
         slv_tst_wdata <= '{default:'0};
      end
      else
      begin
         for (int i=0; i<NUM_TST; i++)
         begin
            slv_tst_addr[i] <= slv_mx_addr;
            slv_tst_wdata[i] <= sh_ocl_wdata_q;
         end
      end

`else
 
   always_ff @(negedge sync_rst_n or posedge clk)
      if (!sync_rst_n)
      begin
         slv_tst_addr <= '{default:'0};
         slv_tst_wdata <= '{default:'0};
      end
      else
      begin
         for (int i=0; i<NUM_TST; i++)
         begin
            slv_tst_addr[i] <= slv_mx_addr;
            slv_tst_wdata[i] <= sh_cl_pcis_wdata >> (32 * slv_req_wr_addr[5:2]);
         end
      end
`endif

//Test are 1 clock pulses (because want to support clock crossing)
always_ff @(negedge sync_rst_n or posedge clk)
   if (!sync_rst_n)
   begin
      slv_did_req <= 0;
   end
   else if (slv_state==SLV_IDLE)
   begin
      slv_did_req <= 0;
   end
   else if (|slv_tst_wr || |slv_tst_rd)
   begin
      slv_did_req <= 1;
   end

//Flop this for timing
always_ff @(negedge sync_rst_n or posedge clk)
   if (!sync_rst_n)
   begin
      slv_tst_wr <= 0;
      slv_tst_rd <= 0;
   end
   else
   begin
      slv_tst_wr <= ((slv_state==SLV_CYC) & slv_mx_req_valid & slv_cyc_wr & !slv_did_req) << slv_sel;
      slv_tst_rd <= ((slv_state==SLV_CYC) & slv_mx_req_valid & !slv_cyc_wr & !slv_did_req) << slv_sel;
   end

//assign slv_tst_wr = ((slv_state==SLV_CYC) & slv_mx_req_valid & slv_cyc_wr & !slv_did_req) << slv_sel;
//assign slv_tst_rd = ((slv_state==SLV_CYC) & slv_mx_req_valid & !slv_cyc_wr & !slv_did_req) << slv_sel;

assign slv_cyc_done = tst_slv_ack_pipe[slv_sel];

//Latch the return data
always_ff @(negedge sync_rst_n or posedge clk)
   if (!sync_rst_n)
      slv_rdata <= 0;
   else if (slv_cyc_done)
      slv_rdata <= tst_slv_rdata_pipe[slv_sel];

`ifdef OCL_TG_CTL
   //Ready back to AXI for request
   always_ff @(negedge sync_rst_n or posedge clk)
      if (!sync_rst_n)
      begin
         ocl_sh_awready_q <= 0;
         ocl_sh_wready_q <= 0;
         ocl_sh_arready_q <= 0;
      end
      else
      begin
         ocl_sh_awready_q <= (slv_state_nxt==SLV_WR_ADDR);
         ocl_sh_wready_q <= ((slv_state==SLV_CYC) && (slv_state_nxt!=SLV_CYC)) && slv_cyc_wr;
         ocl_sh_arready_q <= ((slv_state==SLV_CYC) && (slv_state_nxt!=SLV_CYC)) && ~slv_cyc_wr;
      end
   
   //Response back to AXI
   assign ocl_sh_bid_q = slv_req_wr_id;
   assign ocl_sh_bresp_q = 0;
   assign ocl_sh_bvalid_q = (slv_state==SLV_RESP) && slv_cyc_wr;
   
   assign ocl_sh_rid_q = slv_req_rd_id;
   assign ocl_sh_rdata_q = slv_rdata;
   assign ocl_sh_rresp_q = 2'b00;
   assign ocl_sh_rvalid_q = (slv_state==SLV_RESP) && !slv_cyc_wr;

`else
   //Ready back to AXI for request
   always_ff @(negedge sync_rst_n or posedge clk)
      if (!sync_rst_n)
      begin
         cl_sh_pcis_awready <= 0;
         cl_sh_pcis_wready <= 0;
         cl_sh_pcis_arready <= 0;
      end
      else
      begin
         cl_sh_pcis_awready <= (slv_state_nxt==SLV_WR_ADDR);
         cl_sh_pcis_wready <= ((slv_state==SLV_CYC) && (slv_state_nxt!=SLV_CYC)) && slv_cyc_wr;
         cl_sh_pcis_arready <= ((slv_state==SLV_CYC) && (slv_state_nxt!=SLV_CYC)) && ~slv_cyc_wr;
      end
   
   //Response back to AXI
   assign cl_sh_pcis_bid = slv_req_wr_id;
   assign cl_sh_pcis_bresp = 0;
   assign cl_sh_pcis_bvalid = (slv_state==SLV_RESP) && slv_cyc_wr;
   
   assign cl_sh_pcis_rid = slv_req_rd_id;
   assign cl_sh_pcis_rdata = slv_rdata << (32 * slv_req_rd_addr[5:2]);
   assign cl_sh_pcis_rresp = 2'b00;
   assign cl_sh_pcis_rvalid = (slv_state==SLV_RESP) && !slv_cyc_wr;
   assign cl_sh_pcis_rlast = 1;         //Right now is always 1 DW
`endif


   // Pipeline the requests

/*   genvar   gslv;
   generate
      for (gslv=0; gslv<NUM_TST; gslv++)
        begin: gen_pipe_slv
           lib_pipe #(.WIDTH(32+32+1+1), .STAGES(4)) PIPE_SLV_REQ (.clk (clk), 
                                                                   .rst_n (sync_rst_n), 
                                                                   .in_bus({slv_tst_addr[gslv], slv_tst_wdata[gslv], slv_tst_wr[gslv], slv_tst_rd[gslv]}),
                                                                   .out_bus({slv_tst_addr_pipe[gslv], slv_tst_wdata_pipe[gslv], slv_tst_wr_pipe[gslv], slv_tst_rd_pipe[gslv]})
                                                                   );

           lib_pipe #(.WIDTH(32+1), .STAGES(4)) PIPE_SLV_ACK (.clk (clk), 
                                                              .rst_n (sync_rst_n), 
                                                              .in_bus({tst_slv_ack[gslv], tst_slv_rdata[gslv]}),
                                                              .out_bus({tst_slv_ack_pipe[gslv], tst_slv_rdata_pipe[gslv]})
                                                              );
           
        end // block: gen_pipe_slv
   endgenerate
*/   
                                                      
//------------------------------------
// Instantiate the TST blocks
//------------------------------------

//PCIE

`ifdef PCI_ATG_CFG_PIPE_ENABLE
      lib_pipe #(.WIDTH(32+32+1+1), .STAGES(NUM_CFG_STGS_PCIE_ATG)) PIPE_SLV_REQ_PCIE (.clk (clk), 
                                                                  .rst_n (sync_rst_n), 
                                                                  .in_bus({slv_tst_addr, slv_tst_wdata, slv_tst_wr, slv_tst_rd}),
                                                                  .out_bus({slv_tst_addr_pipe, slv_tst_wdata_pipe, slv_tst_wr_pipe, slv_tst_rd_pipe})
                                                                   );
      
      lib_pipe #(.WIDTH(32+1), .STAGES(NUM_CFG_STGS_PCIE_ATG)) PIPE_SLV_ACK_PCIE (.clk (clk), 
                                                              .rst_n (sync_rst_n), 
                                                              .in_bus({tst_slv_ack, tst_slv_rdata}),
                                                              .out_bus({tst_slv_ack_pipe, tst_slv_rdata_pipe})
                                                              );
`else // !`ifdef PCI_ATG_CFG_PIPE_ENABLE
      
   assign slv_tst_addr_pipe[0] = slv_tst_addr[0];
   assign slv_tst_wdata_pipe[0] = slv_tst_wdata[0];
   assign slv_tst_wr_pipe[0] = slv_tst_wr[0];
   assign slv_tst_rd_pipe[0] = slv_tst_rd[0];
   assign tst_slv_ack_pipe[0] = tst_slv_ack[0];
   assign tst_slv_rdata_pipe[0] = tst_slv_rdata[0];
`endif // !`ifdef PCI_ATG_CFG_PIPE_ENABLE
      
   // First BE
   assign cl_sh_pcim_awuser_q[14:11] = 4'hf;
   assign cl_sh_pcim_aruser_q[14:11] = 4'hf;

   // Last BE
   assign cl_sh_pcim_awuser_q[18:15] = cl_sh_pcim_awuser_q[10:0] == 11'd1 ? 4'h0 : 4'hf;
   assign cl_sh_pcim_aruser_q[18:15] = cl_sh_pcim_aruser_q[10:0] == 11'd1 ? 4'h0 : 4'hf;
   
      cl_tst #(.DATA_WIDTH(512)) CL_TST_PCI (
   
         .clk(clk),
         .rst_n(sync_rst_n),

         .cfg_addr(slv_tst_addr_pipe[0]),
         .cfg_wdata(slv_tst_wdata_pipe[0]),
         .cfg_wr(slv_tst_wr_pipe[0]),
         .cfg_rd(slv_tst_rd_pipe[0]),
         .tst_cfg_ack(tst_slv_ack[0]),
         .tst_cfg_rdata(tst_slv_rdata[0]),

         .atg_enable(),
  
         .awid({dummy_cl_sh_pcim_awid, cl_sh_pcim_awid_q}),
         .awaddr(cl_sh_pcim_awaddr_q), 
         .awlen(cl_sh_pcim_awlen_q),
         .awvalid(cl_sh_pcim_awvalid_q),
         .awuser(cl_sh_pcim_awuser_q[10:0]),
         .awready(sh_cl_pcim_awready_q),

         //.wid(cl_sh_pcim_wid_q),
         .wid(),
         .wdata(cl_sh_pcim_wdata_q),
         .wstrb(cl_sh_pcim_wstrb_q),
         .wlast(cl_sh_pcim_wlast_q),
         .wvalid(cl_sh_pcim_wvalid_q),
         .wready(sh_cl_pcim_wready_q),

         .bid({1'd0, sh_cl_pcim_bid_q}),
         .bresp(sh_cl_pcim_bresp_q),
         .bvalid(sh_cl_pcim_bvalid_q),
         .buser(18'h0),
         .bready(cl_sh_pcim_bready_q),

         .arid({dummy_cl_sh_pcim_arid, cl_sh_pcim_arid_q}),
         .araddr(cl_sh_pcim_araddr_q),
         .arlen(cl_sh_pcim_arlen_q),
         .aruser(cl_sh_pcim_aruser_q[10:0]),
         .arvalid(cl_sh_pcim_arvalid_q),
         .arready(sh_cl_pcim_arready_q),

         .rid({4'h0, sh_cl_pcim_rid_q}),
         .rdata(sh_cl_pcim_rdata_q),
         .rresp(sh_cl_pcim_rresp_q),
         .rlast(sh_cl_pcim_rlast_q),
         .ruser(18'h0),
         .rvalid(sh_cl_pcim_rvalid_q),
         .rready(cl_sh_pcim_rready_q)
      );

   assign ddr_slv_tst_addr = {slv_tst_addr[3], slv_tst_addr[4], slv_tst_addr[2], slv_tst_addr[1]};
   assign ddr_slv_tst_wdata = {slv_tst_wdata[3], slv_tst_wdata[4], slv_tst_wdata[2], slv_tst_wdata[1]};
   assign ddr_slv_tst_wr = {slv_tst_wr[3], slv_tst_wr[4], slv_tst_wr[2], slv_tst_wr[1]};
   assign ddr_slv_tst_rd = {slv_tst_rd[3], slv_tst_rd[4], slv_tst_rd[2], slv_tst_rd[1]};
   assign {tst_slv_ack_pipe[3], tst_slv_ack_pipe[4], tst_slv_ack_pipe[2], tst_slv_ack_pipe[1]} = ddr_tst_slv_ack_pipe;
   assign {tst_slv_rdata_pipe[3], tst_slv_rdata_pipe[4], tst_slv_rdata_pipe[2], tst_slv_rdata_pipe[1]} = {ddr_tst_slv_rdata_pipe[3], ddr_tst_slv_rdata_pipe[2], ddr_tst_slv_rdata_pipe[1], ddr_tst_slv_rdata_pipe[0]};
   
`ifndef NO_CL_DDR
//DDR

lib_pipe #(.WIDTH(1+1+8+32), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_DDR_STAT0 (.clk(clk), .rst_n(sync_rst_n),
                                                         .in_bus({sh_ddr_stat_wr0, sh_ddr_stat_rd0, sh_ddr_stat_addr0, sh_ddr_stat_wdata0}),
                                                         .out_bus({sh_ddr_stat_wr_q[0], sh_ddr_stat_rd_q[0], sh_ddr_stat_addr_q[0], sh_ddr_stat_wdata_q[0]})
                                                         );


lib_pipe #(.WIDTH(1+8+32), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_DDR_STAT_ACK0 (.clk(clk), .rst_n(sync_rst_n),
                                                         .in_bus({ddr_sh_stat_ack_q[0], ddr_sh_stat_int_q[0], ddr_sh_stat_rdata_q[0]}),
                                                         .out_bus({ddr_sh_stat_ack0, ddr_sh_stat_int0, ddr_sh_stat_rdata0})
                                                         );


lib_pipe #(.WIDTH(1+1+8+32), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_DDR_STAT1 (.clk(clk), .rst_n(sync_rst_n),
                                                         .in_bus({sh_ddr_stat_wr1, sh_ddr_stat_rd1, sh_ddr_stat_addr1, sh_ddr_stat_wdata1}),
                                                         .out_bus({sh_ddr_stat_wr_q[1], sh_ddr_stat_rd_q[1], sh_ddr_stat_addr_q[1], sh_ddr_stat_wdata_q[1]})
                                                         );


lib_pipe #(.WIDTH(1+8+32), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_DDR_STAT_ACK1 (.clk(clk), .rst_n(sync_rst_n),
                                                         .in_bus({ddr_sh_stat_ack_q[1], ddr_sh_stat_int_q[1], ddr_sh_stat_rdata_q[1]}),
                                                         .out_bus({ddr_sh_stat_ack1, ddr_sh_stat_int1, ddr_sh_stat_rdata1})
                                                         );

lib_pipe #(.WIDTH(1+1+8+32), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_DDR_STAT2 (.clk(clk), .rst_n(sync_rst_n),
                                                         .in_bus({sh_ddr_stat_wr2, sh_ddr_stat_rd2, sh_ddr_stat_addr2, sh_ddr_stat_wdata2}),
                                                         .out_bus({sh_ddr_stat_wr_q[2], sh_ddr_stat_rd_q[2], sh_ddr_stat_addr_q[2], sh_ddr_stat_wdata_q[2]})
                                                         );


lib_pipe #(.WIDTH(1+8+32), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_DDR_STAT_ACK2 (.clk(clk), .rst_n(sync_rst_n),
                                                         .in_bus({ddr_sh_stat_ack_q[2], ddr_sh_stat_int_q[2], ddr_sh_stat_rdata_q[2]}),
                                                         .out_bus({ddr_sh_stat_ack2, ddr_sh_stat_int2, ddr_sh_stat_rdata2})
                                                         );


genvar gd;
generate
   for (gd=0; gd<3; gd++)
   begin: gen_ddr_tst 

      if ((gd == 0 && DDR_A_PRESENT == 1) ||
          (gd == 1 && DDR_B_PRESENT == 1) ||
          (gd == 2 && DDR_D_PRESENT == 1)) begin
      lib_pipe #(.WIDTH(32+32+1+1), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_SLV_REQ_DDR (.clk (clk), 
                                                                  .rst_n (sync_rst_n), 
                                                                  .in_bus({ddr_slv_tst_addr[gd], ddr_slv_tst_wdata[gd], ddr_slv_tst_wr[gd], ddr_slv_tst_rd[gd]}),
                                                                  .out_bus({ddr_slv_tst_addr_pipe[gd], ddr_slv_tst_wdata_pipe[gd], ddr_slv_tst_wr_pipe[gd], ddr_slv_tst_rd_pipe[gd]})
                                                                   );
      
      lib_pipe #(.WIDTH(32+1), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_SLV_ACK_DDR (.clk (clk), 
                                                              .rst_n (sync_rst_n), 
                                                              .in_bus({ddr_tst_slv_ack[gd], ddr_tst_slv_rdata[gd]}),
                                                              .out_bus({ddr_tst_slv_ack_pipe[gd], ddr_tst_slv_rdata_pipe[gd]})
                                                              );


      lib_pipe #(.WIDTH(2+3+64), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_SCRB_DDR (.clk(clk), .rst_n(sync_rst_n),
                                                                             .in_bus({ddr_scrb_en[gd], ddr_scrb_done[gd], dbg_ddr_scrb_state[gd], dbg_ddr_scrb_addr[gd]}),
                                                                             .out_bus({ddr_scrb_en_pipe[gd], ddr_scrb_done_pipe[gd], dbg_ddr_scrb_state_pipe[gd], dbg_ddr_scrb_addr_pipe[gd]})
                                                                             );
      cl_tst_scrb #(.DATA_WIDTH(512),
                    .SCRB_BURST_LEN_MINUS1(DDR_SCRB_BURST_LEN_MINUS1),
                    .SCRB_MAX_ADDR(DDR_SCRB_MAX_ADDR),
                    .NO_SCRB_INST(NO_SCRB_INST)) CL_TST_DDR (
   
         .clk(clk),
         .rst_n(sync_rst_n),

         .cfg_addr(ddr_slv_tst_addr_pipe[gd]),
         .cfg_wdata(ddr_slv_tst_wdata_pipe[gd]),
         .cfg_wr(ddr_slv_tst_wr_pipe[gd]),
         .cfg_rd(ddr_slv_tst_rd_pipe[gd]),
         .tst_cfg_ack(ddr_tst_slv_ack[gd]),
         .tst_cfg_rdata(ddr_tst_slv_rdata[gd]),

         .slv_awid(lcl_cl_sh_ddr_awid_q3[gd][5:0]),
         .slv_awaddr(lcl_cl_sh_ddr_awaddr_q3[gd]), 
         .slv_awlen(lcl_cl_sh_ddr_awlen_q3[gd]),
         .slv_awvalid(lcl_cl_sh_ddr_awvalid_q3[gd]),
         .slv_awuser(11'b0),
         .slv_awready(lcl_sh_cl_ddr_awready_q3[gd]),

         .slv_wid(6'b0),
         .slv_wdata(lcl_cl_sh_ddr_wdata_q3[gd]),
         .slv_wstrb(lcl_cl_sh_ddr_wstrb_q3[gd]),
         .slv_wlast(lcl_cl_sh_ddr_wlast_q3[gd]),
         .slv_wvalid(lcl_cl_sh_ddr_wvalid_q3[gd]),
         .slv_wready(lcl_sh_cl_ddr_wready_q3[gd]),

         .slv_bid(lcl_sh_cl_ddr_bid_q3[gd][5:0]),
         .slv_bresp(lcl_sh_cl_ddr_bresp_q3[gd]),
         .slv_buser(),
         .slv_bvalid(lcl_sh_cl_ddr_bvalid_q3[gd]),
         .slv_bready(lcl_cl_sh_ddr_bready_q3[gd]),

         .slv_arid(lcl_cl_sh_ddr_arid_q3[gd][5:0]),
         .slv_araddr(lcl_cl_sh_ddr_araddr_q3[gd]), 
         .slv_arlen(lcl_cl_sh_ddr_arlen_q3[gd]),
         .slv_arvalid(lcl_cl_sh_ddr_arvalid_q3[gd]),
         .slv_aruser(11'b0),
         .slv_arready(lcl_sh_cl_ddr_arready_q3[gd]),        

         .slv_rid(lcl_sh_cl_ddr_rid_q3[gd][5:0]),
         .slv_rdata(lcl_sh_cl_ddr_rdata_q3[gd]),
         .slv_rresp(lcl_sh_cl_ddr_rresp_q3[gd]),
         .slv_rlast(lcl_sh_cl_ddr_rlast_q3[gd]),
         .slv_ruser(),
         .slv_rvalid(lcl_sh_cl_ddr_rvalid_q3[gd]),
         .slv_rready(lcl_cl_sh_ddr_rready_q3[gd]),

   
         .awid(lcl_cl_sh_ddr_awid[gd][5:0]),
         .awaddr(lcl_cl_sh_ddr_awaddr[gd]), 
         .awlen(lcl_cl_sh_ddr_awlen[gd]),
         .awvalid(lcl_cl_sh_ddr_awvalid[gd]),
         .awuser(),
         .awready(lcl_sh_cl_ddr_awready[gd]),

         .wid(lcl_cl_sh_ddr_wid[gd][5:0]),
         .wdata(lcl_cl_sh_ddr_wdata[gd]),
         .wstrb(lcl_cl_sh_ddr_wstrb[gd]),
         .wlast(lcl_cl_sh_ddr_wlast[gd]),
         .wvalid(lcl_cl_sh_ddr_wvalid[gd]),
         .wready(lcl_sh_cl_ddr_wready[gd]),

         .bid(lcl_sh_cl_ddr_bid[gd][5:0]),
         .bresp(lcl_sh_cl_ddr_bresp[gd]),
         .buser(18'h0),
         .bvalid(lcl_sh_cl_ddr_bvalid[gd]),
         .bready(lcl_cl_sh_ddr_bready[gd]),

         .arid(lcl_cl_sh_ddr_arid[gd][5:0]),
         .araddr(lcl_cl_sh_ddr_araddr[gd]),
         .arlen(lcl_cl_sh_ddr_arlen[gd]),
         .arvalid(lcl_cl_sh_ddr_arvalid[gd]),
         .aruser(),
         .arready(lcl_sh_cl_ddr_arready[gd]),

         .rid(lcl_sh_cl_ddr_rid[gd][5:0]),
         .rdata(lcl_sh_cl_ddr_rdata[gd]),
         .rresp(lcl_sh_cl_ddr_rresp[gd]),
         .rlast(lcl_sh_cl_ddr_rlast[gd]),
         .ruser(18'h0),
         .rvalid(lcl_sh_cl_ddr_rvalid[gd]),
         .rready(lcl_cl_sh_ddr_rready[gd]),

         .scrb_enable(ddr_scrb_en_pipe[gd]),
         .scrb_done  (ddr_scrb_done[gd]),

         .scrb_dbg_state(dbg_ddr_scrb_state[gd]),
         .scrb_dbg_addr (dbg_ddr_scrb_addr[gd])
      );
      assign lcl_cl_sh_ddr_awid[gd][15:6] = 10'b0;
      assign lcl_cl_sh_ddr_wid[gd][15:6] = 10'b0;
      assign lcl_cl_sh_ddr_arid[gd][15:6] = 10'b0;


`ifndef NO_CL_DDR_TST_AXI4_REG_SLC
   if ((gd==0) && SH_DDR_A_PRESENT)    //DDR_A is in SH
   begin
     // AXI4 register slice - For signals between CL and HL
      axi4_flop_fifo #(.ADDR_WIDTH(64), .DATA_WIDTH(512), .ID_WIDTH(16), .A_USER_WIDTH(1), .FIFO_DEPTH(3)) DDR_A_CL_TST_AXI4_REG_SLC (
       .aclk           (clk),
       .aresetn        (sync_rst_n),
       .sync_rst_n     (1'b1),
       .s_axi_awid     ({10'b0, lcl_cl_sh_ddr_awid_q[gd]}),
       .s_axi_awaddr   ({lcl_cl_sh_ddr_awaddr_q[gd][63:32], 2'b0, lcl_cl_sh_ddr_awaddr_q[gd][29:0]}),
       .s_axi_awlen    (lcl_cl_sh_ddr_awlen_q[gd]),
       .s_axi_awuser   (1'd0),
       .s_axi_awvalid  (lcl_cl_sh_ddr_awvalid_q[gd]),
       .s_axi_awready  (lcl_sh_cl_ddr_awready_q[gd]),
       .s_axi_wdata    (lcl_cl_sh_ddr_wdata_q[gd]),
       .s_axi_wstrb    (lcl_cl_sh_ddr_wstrb_q[gd]),
       .s_axi_wlast    (lcl_cl_sh_ddr_wlast_q[gd]),
       .s_axi_wvalid   (lcl_cl_sh_ddr_wvalid_q[gd]),
       .s_axi_wuser    (),
       .s_axi_wready   (lcl_sh_cl_ddr_wready_q[gd]),
       .s_axi_bid      ({dummy_lcl_sh_cl_ddr_bid_q[gd], lcl_sh_cl_ddr_bid_q[gd]}),
       .s_axi_bresp    (lcl_sh_cl_ddr_bresp_q[gd]),
       .s_axi_buser    (),
       .s_axi_bvalid   (lcl_sh_cl_ddr_bvalid_q[gd]),
       .s_axi_bready   (lcl_cl_sh_ddr_bready_q[gd]),
       .s_axi_arid     ({10'b0, lcl_cl_sh_ddr_arid_q[gd]}),
       .s_axi_araddr   ({lcl_cl_sh_ddr_araddr_q[gd][63:32], 2'b0, lcl_cl_sh_ddr_araddr_q[gd][29:0]}),
       .s_axi_arlen    (lcl_cl_sh_ddr_arlen_q[gd]),
       .s_axi_aruser   (1'd0),
       .s_axi_arvalid  (lcl_cl_sh_ddr_arvalid_q[gd]),
       .s_axi_arready  (lcl_sh_cl_ddr_arready_q[gd]),
       .s_axi_rid      ({dummy_lcl_sh_cl_ddr_rid_q[gd], lcl_sh_cl_ddr_rid_q[gd]}),
       .s_axi_ruser    (),
       .s_axi_rdata    (lcl_sh_cl_ddr_rdata_q[gd]),
       .s_axi_rresp    (lcl_sh_cl_ddr_rresp_q[gd]),
       .s_axi_rlast    (lcl_sh_cl_ddr_rlast_q[gd]),
       .s_axi_rvalid   (lcl_sh_cl_ddr_rvalid_q[gd]),
       .s_axi_rready   (lcl_cl_sh_ddr_rready_q[gd]),  
       .m_axi_awid     (cl_sh_ddra_awid),   
       .m_axi_awaddra   (cl_sh_ddr_awaddr), 
       .m_axi_awlen    (cl_sh_ddra_awlen),  
       .m_axi_awuser   (),
       .m_axi_awvalid  (cl_sh_ddra_awvalid),
       .m_axi_awready  (sh_cl_ddra_awready),
       .m_axi_wdata    (cl_sh_ddra_wdata),  
       .m_axi_wstrb    (cl_sh_ddra_wstrb),  
       .m_axi_wlast    (cl_sh_ddra_wlast),  
       .m_axi_wuser    (),
       .m_axi_wvalid   (cl_sh_ddra_wvalid), 
       .m_axi_wready   (sh_cl_ddra_wready), 
       .m_axi_bid      (sh_cl_ddra_bid),    
       .m_axi_bresp    (sh_cl_ddra_bresp),  
       .m_axi_buser    (),
       .m_axi_bvalid   (sh_cl_ddra_bvalid), 
       .m_axi_bready   (cl_sh_ddra_bready), 
       .m_axi_arid     (cl_sh_ddra_arid),   
       .m_axi_araddra   (cl_sh_ddr_araddr), 
       .m_axi_arlen    (cl_sh_ddra_arlen),  
       .m_axi_aruser   (),
       .m_axi_arvalid  (cl_sh_ddra_arvalid),
       .m_axi_arready  (sh_cl_ddra_arready),
       .m_axi_rid      (sh_cl_ddra_rid),    
       .m_axi_rdata    (sh_cl_ddra_rdata),  
       .m_axi_rresp    (sh_cl_ddra_rresp),  
       .m_axi_rlast    (sh_cl_ddra_rlast),  
       .m_axi_ruser    (),
       .m_axi_rvalid   (sh_cl_ddra_rvalid), 
       .m_axi_rready   (cl_sh_ddra_rready)
       );
   end
   else
   begin
     // AXI4 register slice - For signals between CL and HL
      src_register_slice DDR_TST_AXI4_REG_SLC_1 (
       .aclk           (clk),
       .aresetn        (sync_rst_n),
       .s_axi_awid     (lcl_cl_sh_ddr_awid_q[gd]),
       .s_axi_awaddr   ({lcl_cl_sh_ddr_awaddr_q[gd][63:32], 2'b0, lcl_cl_sh_ddr_awaddr_q[gd][29:0]}),
       .s_axi_awlen    (lcl_cl_sh_ddr_awlen_q[gd]),
       .s_axi_awsize   (3'b110),
       .s_axi_awburst  (2'b1),
       .s_axi_awlock   (1'b0),
       .s_axi_awcache  (4'b11),
       .s_axi_awprot   (3'b10),
       .s_axi_awregion (4'b0),
       .s_axi_awqos    (4'b0),
       .s_axi_awvalid  (lcl_cl_sh_ddr_awvalid_q[gd]),
       .s_axi_awready  (lcl_sh_cl_ddr_awready_q[gd]),
       .s_axi_wdata    (lcl_cl_sh_ddr_wdata_q[gd]),
       .s_axi_wstrb    (lcl_cl_sh_ddr_wstrb_q[gd]),
       .s_axi_wlast    (lcl_cl_sh_ddr_wlast_q[gd]),
       .s_axi_wvalid   (lcl_cl_sh_ddr_wvalid_q[gd]),
       .s_axi_wready   (lcl_sh_cl_ddr_wready_q[gd]),
       .s_axi_bid      (lcl_sh_cl_ddr_bid_q[gd]),
       .s_axi_bresp    (lcl_sh_cl_ddr_bresp_q[gd]),
       .s_axi_bvalid   (lcl_sh_cl_ddr_bvalid_q[gd]),
       .s_axi_bready   (lcl_cl_sh_ddr_bready_q[gd]),
       .s_axi_arid     (lcl_cl_sh_ddr_arid_q[gd]),
       .s_axi_araddr   ({lcl_cl_sh_ddr_araddr_q[gd][63:32], 2'b0, lcl_cl_sh_ddr_araddr_q[gd][29:0]}),
       .s_axi_arlen    (lcl_cl_sh_ddr_arlen_q[gd]),
       .s_axi_arsize   (3'b110),
       .s_axi_arburst  (2'b1),
       .s_axi_arlock   (1'b0),
       .s_axi_arcache  (4'b11),
       .s_axi_arprot   (3'b10),
       .s_axi_arregion (4'b0),
       .s_axi_arqos    (4'b0),
       .s_axi_arvalid  (lcl_cl_sh_ddr_arvalid_q[gd]),
       .s_axi_arready  (lcl_sh_cl_ddr_arready_q[gd]),
       .s_axi_rid      (lcl_sh_cl_ddr_rid_q[gd]),
       .s_axi_rdata    (lcl_sh_cl_ddr_rdata_q[gd]),
       .s_axi_rresp    (lcl_sh_cl_ddr_rresp_q[gd]),
       .s_axi_rlast    (lcl_sh_cl_ddr_rlast_q[gd]),
       .s_axi_rvalid   (lcl_sh_cl_ddr_rvalid_q[gd]),
       .s_axi_rready   (lcl_cl_sh_ddr_rready_q[gd]),  
       .m_axi_awid     (lcl_cl_sh_ddr_awid_qq[gd]),   
       .m_axi_awaddr   (lcl_cl_sh_ddr_awaddr_qq[gd]), 
       .m_axi_awlen    (lcl_cl_sh_ddr_awlen_qq[gd]),  
       .m_axi_awvalid  (lcl_cl_sh_ddr_awvalid_qq[gd]),
       .m_axi_awready  (lcl_sh_cl_ddr_awready_qq[gd]),
       .m_axi_wdata    (lcl_cl_sh_ddr_wdata_qq[gd]),  
       .m_axi_wstrb    (lcl_cl_sh_ddr_wstrb_qq[gd]),  
       .m_axi_wlast    (lcl_cl_sh_ddr_wlast_qq[gd]),  
       .m_axi_wvalid   (lcl_cl_sh_ddr_wvalid_qq[gd]), 
       .m_axi_wready   (lcl_sh_cl_ddr_wready_qq[gd]), 
       .m_axi_bid      (lcl_sh_cl_ddr_bid_qq[gd]),    
       .m_axi_bresp    (lcl_sh_cl_ddr_bresp_qq[gd]),  
       .m_axi_bvalid   (lcl_sh_cl_ddr_bvalid_qq[gd]), 
       .m_axi_bready   (lcl_cl_sh_ddr_bready_qq[gd]), 
       .m_axi_arid     (lcl_cl_sh_ddr_arid_qq[gd]),   
       .m_axi_araddr   (lcl_cl_sh_ddr_araddr_qq[gd]), 
       .m_axi_arlen    (lcl_cl_sh_ddr_arlen_qq[gd]),  
       .m_axi_arvalid  (lcl_cl_sh_ddr_arvalid_qq[gd]),
       .m_axi_arready  (lcl_sh_cl_ddr_arready_qq[gd]),
       .m_axi_rid      (lcl_sh_cl_ddr_rid_qq[gd]),    
       .m_axi_rdata    (lcl_sh_cl_ddr_rdata_qq[gd]),  
       .m_axi_rresp    (lcl_sh_cl_ddr_rresp_qq[gd]),  
       .m_axi_rlast    (lcl_sh_cl_ddr_rlast_qq[gd]),  
       .m_axi_rvalid   (lcl_sh_cl_ddr_rvalid_qq[gd]), 
       .m_axi_rready   (lcl_cl_sh_ddr_rready_qq[gd])
       );
      dest_register_slice DDR_TST_AXI4_REG_SLC_2 (
       .aclk           (clk),
       .aresetn        (sync_rst_n),
       .s_axi_awid     ({10'b0, lcl_cl_sh_ddr_awid_qq[gd]}),
       .s_axi_awaddr   (lcl_cl_sh_ddr_awaddr_qq[gd]),
       .s_axi_awlen    (lcl_cl_sh_ddr_awlen_qq[gd]),
       .s_axi_awsize   (3'b110),
       .s_axi_awburst  (2'b1),
       .s_axi_awlock   (1'b0),
       .s_axi_awcache  (4'b11),
       .s_axi_awprot   (3'b10),
       .s_axi_awregion (4'b0),
       .s_axi_awqos    (4'b0),
       .s_axi_awvalid  (lcl_cl_sh_ddr_awvalid_qq[gd]),
       .s_axi_awready  (lcl_sh_cl_ddr_awready_qq[gd]),
       .s_axi_wdata    (lcl_cl_sh_ddr_wdata_qq[gd]),
       .s_axi_wstrb    (lcl_cl_sh_ddr_wstrb_qq[gd]),
       .s_axi_wlast    (lcl_cl_sh_ddr_wlast_qq[gd]),
       .s_axi_wvalid   (lcl_cl_sh_ddr_wvalid_qq[gd]),
       .s_axi_wready   (lcl_sh_cl_ddr_wready_qq[gd]),
       .s_axi_bid      ({dummy_lcl_sh_cl_ddr_bid_qq[gd], lcl_sh_cl_ddr_bid_qq[gd]}),
       .s_axi_bresp    (lcl_sh_cl_ddr_bresp_qq[gd]),
       .s_axi_bvalid   (lcl_sh_cl_ddr_bvalid_qq[gd]),
       .s_axi_bready   (lcl_cl_sh_ddr_bready_qq[gd]),
       .s_axi_arid     ({10'b0, lcl_cl_sh_ddr_arid_qq[gd]}),
       .s_axi_araddr   (lcl_cl_sh_ddr_araddr_qq[gd]),
       .s_axi_arlen    (lcl_cl_sh_ddr_arlen_qq[gd]),
       .s_axi_arsize   (3'b110),
       .s_axi_arburst  (2'b1),
       .s_axi_arlock   (1'b0),
       .s_axi_arcache  (4'b11),
       .s_axi_arprot   (3'b10),
       .s_axi_arregion (4'b0),
       .s_axi_arqos    (4'b0),
       .s_axi_arvalid  (lcl_cl_sh_ddr_arvalid_qq[gd]),
       .s_axi_arready  (lcl_sh_cl_ddr_arready_qq[gd]),
       .s_axi_rid      ({dummy_lcl_sh_cl_ddr_rid_qq[gd], lcl_sh_cl_ddr_rid_qq[gd]}),
       .s_axi_rdata    (lcl_sh_cl_ddr_rdata_qq[gd]),
       .s_axi_rresp    (lcl_sh_cl_ddr_rresp_qq[gd]),
       .s_axi_rlast    (lcl_sh_cl_ddr_rlast_qq[gd]),
       .s_axi_rvalid   (lcl_sh_cl_ddr_rvalid_qq[gd]),
       .s_axi_rready   (lcl_cl_sh_ddr_rready_qq[gd]),  
       .m_axi_awid     (lcl_cl_sh_ddr_awid_q3[gd]),   
       .m_axi_awaddr   (lcl_cl_sh_ddr_awaddr_q3[gd]), 
       .m_axi_awlen    (lcl_cl_sh_ddr_awlen_q3[gd]),  
       .m_axi_awvalid  (lcl_cl_sh_ddr_awvalid_q3[gd]),
       .m_axi_awready  (lcl_sh_cl_ddr_awready_q3[gd]),
       .m_axi_wdata    (lcl_cl_sh_ddr_wdata_q3[gd]),  
       .m_axi_wstrb    (lcl_cl_sh_ddr_wstrb_q3[gd]),  
       .m_axi_wlast    (lcl_cl_sh_ddr_wlast_q3[gd]),  
       .m_axi_wvalid   (lcl_cl_sh_ddr_wvalid_q3[gd]), 
       .m_axi_wready   (lcl_sh_cl_ddr_wready_q3[gd]), 
       .m_axi_bid      ({10'b0, lcl_sh_cl_ddr_bid_q3[gd][5:0]}),    
       .m_axi_bresp    (lcl_sh_cl_ddr_bresp_q3[gd]),  
       .m_axi_bvalid   (lcl_sh_cl_ddr_bvalid_q3[gd]), 
       .m_axi_bready   (lcl_cl_sh_ddr_bready_q3[gd]), 
       .m_axi_arid     (lcl_cl_sh_ddr_arid_q3[gd]),   
       .m_axi_araddr   (lcl_cl_sh_ddr_araddr_q3[gd]), 
       .m_axi_arlen    (lcl_cl_sh_ddr_arlen_q3[gd]),  
       .m_axi_arvalid  (lcl_cl_sh_ddr_arvalid_q3[gd]),
       .m_axi_arready  (lcl_sh_cl_ddr_arready_q3[gd]),
       .m_axi_rid      ({10'b0, lcl_sh_cl_ddr_rid_q3[gd][5:0]}),    
       .m_axi_rdata    (lcl_sh_cl_ddr_rdata_q3[gd]),  
       .m_axi_rresp    (lcl_sh_cl_ddr_rresp_q3[gd]),  
       .m_axi_rlast    (lcl_sh_cl_ddr_rlast_q3[gd]),  
       .m_axi_rvalid   (lcl_sh_cl_ddr_rvalid_q3[gd]), 
       .m_axi_rready   (lcl_cl_sh_ddr_rready_q3[gd])
       );
/*
       axi_bram_ctrl_1 AXI_BRAM_CTRL (
       .s_axi_aclk           (clk),
       .s_axi_aresetn        (sync_rst_n),
       .s_axi_awid     (lcl_cl_sh_ddr_awid[gd]),
       .s_axi_awaddr   (lcl_cl_sh_ddr_awaddr[gd]),
       .s_axi_awlen    (lcl_cl_sh_ddr_awlen[gd]),
       .s_axi_awsize   (3'b110),
       .s_axi_awburst  (2'b1),
       .s_axi_awlock   (1'b0),
       .s_axi_awcache  (4'b11),
       .s_axi_awprot   (3'b10),
       .s_axi_awvalid  (lcl_cl_sh_ddr_awvalid[gd]),
       .s_axi_awready  (lcl_sh_cl_ddr_awready[gd]),
       .s_axi_wdata    (lcl_cl_sh_ddr_wdata[gd]),
       .s_axi_wstrb    (lcl_cl_sh_ddr_wstrb[gd]),
       .s_axi_wlast    (lcl_cl_sh_ddr_wlast[gd]),
       .s_axi_wvalid   (lcl_cl_sh_ddr_wvalid[gd]),
       .s_axi_wready   (lcl_sh_cl_ddr_wready[gd]),
       .s_axi_bid      (lcl_sh_cl_ddr_bid[gd]),
       .s_axi_bresp    (lcl_sh_cl_ddr_bresp[gd]),
       .s_axi_bvalid   (lcl_sh_cl_ddr_bvalid[gd]),
       .s_axi_bready   (lcl_cl_sh_ddr_bready[gd]),
       .s_axi_arid     (lcl_cl_sh_ddr_arid[gd]),
       .s_axi_araddr   (lcl_cl_sh_ddr_araddr[gd]),
       .s_axi_arlen    (lcl_cl_sh_ddr_arlen[gd]),
       .s_axi_arsize   (3'b110),
       .s_axi_arburst  (2'b1),
       .s_axi_arlock   (1'b0),
       .s_axi_arcache  (4'b11),
       .s_axi_arprot   (3'b10),
       .s_axi_arvalid  (lcl_cl_sh_ddr_arvalid[gd]),
       .s_axi_arready  (lcl_sh_cl_ddr_arready[gd]),
       .s_axi_rid      (lcl_sh_cl_ddr_rid[gd]),
       .s_axi_rdata    (lcl_sh_cl_ddr_rdata[gd]),
       .s_axi_rresp    (lcl_sh_cl_ddr_rresp[gd]),
       .s_axi_rlast    (lcl_sh_cl_ddr_rlast[gd]),
       .s_axi_rvalid   (lcl_sh_cl_ddr_rvalid[gd]),
       .s_axi_rready   (lcl_cl_sh_ddr_rready[gd])  
       ); 
*/
   end

`else // !`ifndef NO_CL_DDR_TST_AXI4_REG_SLC

   if ((gd==0) && SH_DDR_A_PRESENT)    //DDR_A is in SH
   begin
      `ifdef DDR_A_SH    //This is needed so don't get compile errors.
      assign cl_sh_ddra_awid  = {10'b0, lcl_cl_sh_ddr_awid_q[gd]} ;
      assign cl_sh_ddra_awaddr  = lcl_cl_sh_ddr_awaddr_q[gd] ;
      assign cl_sh_ddra_awlen  = lcl_cl_sh_ddr_awlen_q[gd] ;
      assign cl_sh_ddra_awvalid = lcl_cl_sh_ddr_awvalid_q[gd];
      assign lcl_sh_cl_ddr_awready_q[gd] = sh_cl_ddra_awready;
      
      assign cl_sh_ddra_wdata   = lcl_cl_sh_ddr_wdata_q[gd]  ;
      assign cl_sh_ddra_wstrb   = lcl_cl_sh_ddr_wstrb_q[gd]  ;
      assign cl_sh_ddra_wlast   = lcl_cl_sh_ddr_wlast_q[gd]  ;
      assign cl_sh_ddra_wvalid  = lcl_cl_sh_ddr_wvalid_q[gd] ;
      assign lcl_sh_cl_ddr_wready_q[gd]  = sh_cl_ddra_wready ;
      
      assign {dummy_lcl_sh_cl_ddr_bid_q[gd], lcl_sh_cl_ddr_bid_q[gd]}   = sh_cl_ddra_bid  ;
      assign lcl_sh_cl_ddr_bresp_q[gd]   = sh_cl_ddra_bresp  ;
      assign lcl_sh_cl_ddr_bvalid_q[gd]  = sh_cl_ddra_bvalid ;
      assign cl_sh_ddra_bready  = lcl_cl_sh_ddr_bready_q[gd] ;
      
      assign cl_sh_ddra_arid  = {10'b0, lcl_cl_sh_ddr_arid_q[gd]} ;
      assign cl_sh_ddra_araddr  = lcl_cl_sh_ddr_araddr_q[gd] ;
      assign cl_sh_ddra_arlen  = lcl_cl_sh_ddr_arlen_q[gd] ;
      assign cl_sh_ddra_arvalid = lcl_cl_sh_ddr_arvalid_q[gd];
      assign lcl_sh_cl_ddr_arready_q[gd] = sh_cl_ddra_arready;
      
      assign {dummy_lcl_sh_cl_ddr_rid_q[gd], lcl_sh_cl_ddr_rid_q[gd]}   = sh_cl_ddra_rid;
      assign lcl_sh_cl_ddr_rdata_q[gd]   = sh_cl_ddra_rdata  ;
      assign lcl_sh_cl_ddr_rresp_q[gd]   = sh_cl_ddra_rresp  ;
      assign lcl_sh_cl_ddr_rlast_q[gd]   = sh_cl_ddra_rlast  ;
      assign lcl_sh_cl_ddr_rvalid_q[gd]  = sh_cl_ddra_rvalid ;
      assign cl_sh_ddra_rready  = lcl_cl_sh_ddr_rready_q[gd] ;
      `endif
   end
   else
   begin

   assign lcl_cl_sh_ddr_awid_q3[gd]  = {10'b0, lcl_cl_sh_ddr_awid_q[gd]} ;
   assign lcl_cl_sh_ddr_awaddr_q3[gd]  = lcl_cl_sh_ddr_awaddr_q[gd] ;
   assign lcl_cl_sh_ddr_awlen_q3[gd]  = lcl_cl_sh_ddr_awlen_q[gd] ;
   assign lcl_cl_sh_ddr_awvalid_q3[gd] = lcl_cl_sh_ddr_awvalid_q[gd];
   assign lcl_sh_cl_ddr_awready_q[gd] = lcl_sh_cl_ddr_awready_q3[gd];
   
   assign lcl_cl_sh_ddr_wdata_q3[gd]   = lcl_cl_sh_ddr_wdata_q[gd]  ;
   assign lcl_cl_sh_ddr_wstrb_q3[gd]   = lcl_cl_sh_ddr_wstrb_q[gd]  ;
   assign lcl_cl_sh_ddr_wlast_q3[gd]   = lcl_cl_sh_ddr_wlast_q[gd]  ;
   assign lcl_cl_sh_ddr_wvalid_q3[gd]  = lcl_cl_sh_ddr_wvalid_q[gd] ;
   assign lcl_sh_cl_ddr_wready_q[gd]  = lcl_sh_cl_ddr_wready_q3[gd] ;
   
   assign {dummy_lcl_sh_cl_ddr_bid_q[gd], lcl_sh_cl_ddr_bid_q[gd]}   = {10'b0, lcl_sh_cl_ddr_bid_q3[gd]}  ;
   assign lcl_sh_cl_ddr_bresp_q[gd]   = lcl_sh_cl_ddr_bresp_q3[gd]  ;
   assign lcl_sh_cl_ddr_bvalid_q[gd]  = lcl_sh_cl_ddr_bvalid_q3[gd] ;
   assign lcl_cl_sh_ddr_bready_q3[gd]  = lcl_cl_sh_ddr_bready_q[gd] ;
   
   assign lcl_cl_sh_ddr_arid_q3[gd]  = {10'b0, lcl_cl_sh_ddr_arid_q[gd]} ;
   assign lcl_cl_sh_ddr_araddr_q3[gd]  = lcl_cl_sh_ddr_araddr_q[gd] ;
   assign lcl_cl_sh_ddr_arlen_q3[gd]  = lcl_cl_sh_ddr_arlen_q[gd] ;
   assign lcl_cl_sh_ddr_arvalid_q3[gd] = lcl_cl_sh_ddr_arvalid_q[gd];
   assign lcl_sh_cl_ddr_arready_q[gd] = lcl_sh_cl_ddr_arready_q3[gd];
   
   assign {dummy_lcl_sh_cl_ddr_rid_q[gd], lcl_sh_cl_ddr_rid_q[gd]}   = {10'b0, lcl_sh_cl_ddr_rid_q3[gd]}  ;
   assign lcl_sh_cl_ddr_rdata_q[gd]   = lcl_sh_cl_ddr_rdata_q3[gd]  ;
   assign lcl_sh_cl_ddr_rresp_q[gd]   = lcl_sh_cl_ddr_rresp_q3[gd]  ;
   assign lcl_sh_cl_ddr_rlast_q[gd]   = lcl_sh_cl_ddr_rlast_q3[gd]  ;
   assign lcl_sh_cl_ddr_rvalid_q[gd]  = lcl_sh_cl_ddr_rvalid_q3[gd] ;
   assign lcl_cl_sh_ddr_rready_q3[gd]  = lcl_cl_sh_ddr_rready_q[gd] ;
   end

`endif // !`ifndef NO_CL_DDR_TST_AXI4_REG_SLC

      end // if ((gd == 0 && DDR_A_PRESENT == 1) ||...
                  
   end // block: gen_ddr_tst
   
endgenerate
`else // !`ifndef NO_CL_DDR
   assign ddr_scrb_done_pipe[2:0] = 3'd7;

   assign lcl_sh_cl_ddr_awready_q = 0;
   assign lcl_sh_cl_ddr_wready_q = 0;
   assign lcl_sh_cl_ddr_bresp_q = '{default:'0};
   assign lcl_sh_cl_ddr_bvalid_q = 0;
   assign lcl_sh_cl_ddr_arready_q = 0;
   assign lcl_sh_cl_ddr_rresp_q = '{default:'0};
   assign lcl_sh_cl_ddr_rlast_q = 0;
   assign lcl_sh_cl_ddr_rvalid_q = 0;
`endif //  `ifndef NO_CL_DDR
   
   
`ifdef DDR_3_ATG_CFG_PIPE_ENABLE
   lib_pipe #(.WIDTH(32+32+1+1), .STAGES(NUM_CFG_STGS_SH_DDR_ATG)) PIPE_SLV_REQ_DDR_3 (.clk (clk), 
                                                           .rst_n (sync_rst_n), 
                                                           .in_bus({ddr_slv_tst_addr[3], ddr_slv_tst_wdata[3], ddr_slv_tst_wr[3], ddr_slv_tst_rd[3]}),
                                                           .out_bus({ddr_slv_tst_addr_pipe[3], ddr_slv_tst_wdata_pipe[3], ddr_slv_tst_wr_pipe[3], ddr_slv_tst_rd_pipe[3]})
                                                           );

   lib_pipe #(.WIDTH(32+1), .STAGES(NUM_CFG_STGS_SH_DDR_ATG)) PIPE_SLV_ACK_DDR_3 (.clk (clk), 
                                                      .rst_n (sync_rst_n), 
                                                      .in_bus({ddr_tst_slv_ack[3], ddr_tst_slv_rdata[3]}),
                                                      .out_bus({ddr_tst_slv_ack_pipe[3], ddr_tst_slv_rdata_pipe[3]})
                                                      );

   lib_pipe #(.WIDTH(2+3+64), .STAGES(NUM_CFG_STGS_SH_DDR_ATG)) PIPE_SCRB_DDR_3 (.clk(clk), .rst_n(sync_rst_n),
                                                                            .in_bus({ddr_scrb_en[3], ddr_scrb_done[3], dbg_ddr_scrb_state[3], dbg_ddr_scrb_addr[3]}),
                                                                            .out_bus({ddr_scrb_en_pipe[3], ddr_scrb_done_pipe[3], dbg_ddr_scrb_state_pipe[3], dbg_ddr_scrb_addr_pipe[3]})
                                                                            );

`else // !`ifdef DDR_3_ATG_CFG_PIPE_ENABLE
   assign ddr_slv_tst_addr_pipe[3] = ddr_slv_tst_addr[3];
   assign ddr_slv_tst_wdata_pipe[3] = ddr_slv_tst_wdata[3];
   assign ddr_slv_tst_wr_pipe[3] = ddr_slv_tst_wr[3];
   assign ddr_slv_tst_rd_pipe[3] = ddr_slv_tst_rd[3];
   assign ddr_tst_slv_ack_pipe[3] = ddr_tst_slv_ack[3];
   assign ddr_tst_slv_rdata_pipe[3] = ddr_tst_slv_rdata[3];
   assign ddr_scrb_en_pipe[3] = ddr_scrb_en[3];
   assign ddr_scrb_done_pipe[3] = ddr_scrb_done[3];
   assign dbg_ddr_scrb_state_pipe[3] = dbg_ddr_scrb_state[3];
   assign dbg_ddr_scrb_addr_pipe[3] = dbg_ddr_scrb_addr[3];
   
`endif //  `ifdef DDR_3_ATG_CFG_PIPE_ENABLE

      cl_tst_scrb #(.DATA_WIDTH(512),
                    .SCRB_BURST_LEN_MINUS1(DDR_SCRB_BURST_LEN_MINUS1),
                    .SCRB_MAX_ADDR(DDR_SCRB_MAX_ADDR),
                    .NO_SCRB_INST(NO_SCRB_INST)) CL_TST_DDR_3 (
   
         .clk(clk),
         .rst_n(sync_rst_n),

         .cfg_addr(ddr_slv_tst_addr_pipe[3]),
         .cfg_wdata(ddr_slv_tst_wdata_pipe[3]),
         .cfg_wr(ddr_slv_tst_wr_pipe[3]),
         .cfg_rd(ddr_slv_tst_rd_pipe[3]),
         .tst_cfg_ack(ddr_tst_slv_ack[3]),
         .tst_cfg_rdata(ddr_tst_slv_rdata[3]),

         .slv_awid(cl_sh_ddr_awid_q2[5:0]),
         .slv_awaddr(cl_sh_ddr_awaddr_q2), 
         .slv_awlen(cl_sh_ddr_awlen_q2),
         .slv_awvalid(cl_sh_ddr_awvalid_q2),
         .slv_awuser(11'b0),
         .slv_awready(sh_cl_ddr_awready_q2),

         .slv_wid(6'b0),
         .slv_wdata(cl_sh_ddr_wdata_q2),
         .slv_wstrb(cl_sh_ddr_wstrb_q2),
         .slv_wlast(cl_sh_ddr_wlast_q2),
         .slv_wvalid(cl_sh_ddr_wvalid_q2),
         .slv_wready(sh_cl_ddr_wready_q2),

         .slv_bid(sh_cl_ddr_bid_q2[5:0]),
         .slv_bresp(sh_cl_ddr_bresp_q2),
         .slv_buser(),
         .slv_bvalid(sh_cl_ddr_bvalid_q2),
         .slv_bready(cl_sh_ddr_bready_q2),

         .slv_arid(cl_sh_ddr_arid_q2[5:0]),
         .slv_araddr(cl_sh_ddr_araddr_q2), 
         .slv_arlen(cl_sh_ddr_arlen_q2),
         .slv_arvalid(cl_sh_ddr_arvalid_q2),
         .slv_aruser(11'b0),
         .slv_arready(sh_cl_ddr_arready_q2),        

         .slv_rid(sh_cl_ddr_rid_q2[5:0]),
         .slv_rdata(sh_cl_ddr_rdata_q2),
         .slv_rresp(sh_cl_ddr_rresp_q2),
         .slv_rlast(sh_cl_ddr_rlast_q2),
         .slv_ruser(),
         .slv_rvalid(sh_cl_ddr_rvalid_q2),
         .slv_rready(cl_sh_ddr_rready_q2),

                                               
         .awid(cl_sh_ddr_awid_q3),
         .awaddr(cl_sh_ddr_awaddr_q3), 
         .awlen(cl_sh_ddr_awlen_q3),
         .awvalid(cl_sh_ddr_awvalid_q3),
         .awuser(),
         .awready(sh_cl_ddr_awready_q3),

         //.wid(cl_sh_ddr_wid_q3),
         .wid(),
         .wdata(cl_sh_ddr_wdata_q3),
         .wstrb(cl_sh_ddr_wstrb_q3),
         .wlast(cl_sh_ddr_wlast_q3),
         .wvalid(cl_sh_ddr_wvalid_q3),
         .wready(sh_cl_ddr_wready_q3),

         .bid(sh_cl_ddr_bid_q3),
         .bresp(sh_cl_ddr_bresp_q3),
         .buser(18'h0),
         .bvalid(sh_cl_ddr_bvalid_q3),
         .bready(cl_sh_ddr_bready_q3),

         .arid(cl_sh_ddr_arid_q3),
         .araddr(cl_sh_ddr_araddr_q3),
         .arlen(cl_sh_ddr_arlen_q3),
         .arvalid(cl_sh_ddr_arvalid_q3),
         .aruser(),
         .arready(sh_cl_ddr_arready_q3),

         .rid(sh_cl_ddr_rid_q3),
         .rdata(sh_cl_ddr_rdata_q3),
         .rresp(sh_cl_ddr_rresp_q3),
         .rlast(sh_cl_ddr_rlast_q3),
         .ruser(18'h0),
         .rvalid(sh_cl_ddr_rvalid_q3),
         .rready(cl_sh_ddr_rready_q3),

         .scrb_enable(ddr_scrb_en_pipe[3]),
         .scrb_done  (ddr_scrb_done[3]),

         .scrb_dbg_state(dbg_ddr_scrb_state[3]),
         .scrb_dbg_addr (dbg_ddr_scrb_addr[3])
      );

  axi4_flop_fifo #(.ADDR_WIDTH(64), .DATA_WIDTH(512), .ID_WIDTH(16), .A_USER_WIDTH(1), .FIFO_DEPTH(3)) DDR_TST_3_AXI4_REG_SLC_1 (
     .aclk           (clk),
     .aresetn        (sync_rst_n),
     .sync_rst_n     (1'b1),
                                                                                                                                
     .s_axi_awid     ({10'b0, cl_sh_ddr_awid_q3}),
     .s_axi_awaddr   ({cl_sh_ddr_awaddr_q3}),
     .s_axi_awlen    (cl_sh_ddr_awlen_q3),
     .s_axi_awuser   (1'b0),
     .s_axi_awvalid  (cl_sh_ddr_awvalid_q3),
     .s_axi_awready  (sh_cl_ddr_awready_q3),
     .s_axi_wdata    (cl_sh_ddr_wdata_q3),
     .s_axi_wstrb    (cl_sh_ddr_wstrb_q3),
     .s_axi_wlast    (cl_sh_ddr_wlast_q3),
     .s_axi_wvalid   (cl_sh_ddr_wvalid_q3),
     .s_axi_wuser    (),
     .s_axi_wready   (sh_cl_ddr_wready_q3),
     .s_axi_bid      ({dummy_sh_cl_ddr_bid_q, sh_cl_ddr_bid_q3}),
     .s_axi_bresp    (sh_cl_ddr_bresp_q3),
     .s_axi_bvalid   (sh_cl_ddr_bvalid_q3),
     .s_axi_buser    (),
     .s_axi_bready   (cl_sh_ddr_bready_q3),
     .s_axi_arid     ({10'b0, cl_sh_ddr_arid_q3}),
     .s_axi_araddr   (cl_sh_ddr_araddr_q3),
     .s_axi_arlen    (cl_sh_ddr_arlen_q3),
     .s_axi_aruser   (1'b0),
     .s_axi_arvalid  (cl_sh_ddr_arvalid_q3),
     .s_axi_arready  (sh_cl_ddr_arready_q3),
     .s_axi_rid      ({dummy_sh_cl_ddr_rid_q, sh_cl_ddr_rid_q3}),
     .s_axi_rdata    (sh_cl_ddr_rdata_q3),
     .s_axi_rresp    (sh_cl_ddr_rresp_q3),
     .s_axi_rlast    (sh_cl_ddr_rlast_q3),
     .s_axi_ruser    (),
     .s_axi_rvalid   (sh_cl_ddr_rvalid_q3),
     .s_axi_rready   (cl_sh_ddr_rready_q3),  
     .m_axi_awid     (cl_sh_ddr_awid),   
     .m_axi_awaddr   (cl_sh_ddr_awaddr), 
     .m_axi_awlen    (cl_sh_ddr_awlen),  
     .m_axi_awuser   (),
     .m_axi_awvalid  (cl_sh_ddr_awvalid),
     .m_axi_awready  (sh_cl_ddr_awready),
     .m_axi_wdata    (cl_sh_ddr_wdata),  
     .m_axi_wstrb    (cl_sh_ddr_wstrb),  
     .m_axi_wuser    (),
     .m_axi_wlast    (cl_sh_ddr_wlast),  
     .m_axi_wvalid   (cl_sh_ddr_wvalid), 
     .m_axi_wready   (sh_cl_ddr_wready), 
     .m_axi_bid      (sh_cl_ddr_bid),    
     .m_axi_bresp    (sh_cl_ddr_bresp),  
     .m_axi_buser    (),
     .m_axi_bvalid   (sh_cl_ddr_bvalid), 
     .m_axi_bready   (cl_sh_ddr_bready), 
     .m_axi_arid     (cl_sh_ddr_arid),   
     .m_axi_araddr   (cl_sh_ddr_araddr), 
     .m_axi_arlen    (cl_sh_ddr_arlen),  
     .m_axi_aruser   (),
     .m_axi_arvalid  (cl_sh_ddr_arvalid),
     .m_axi_arready  (sh_cl_ddr_arready),
     .m_axi_rid      (sh_cl_ddr_rid),    
     .m_axi_rdata    (sh_cl_ddr_rdata),  
     .m_axi_rresp    (sh_cl_ddr_rresp),  
     .m_axi_ruser    (),
     .m_axi_rlast    (sh_cl_ddr_rlast),  
     .m_axi_rvalid   (sh_cl_ddr_rvalid), 
     .m_axi_rready   (cl_sh_ddr_rready)
     );


`ifdef HMC_PRESENT   
//HMC
genvar gh;
generate
   for (gh=0; gh<NUM_HMC; gh++)
   begin: gen_hmc_tst 

      lib_pipe #(.WIDTH(32+32+1+1), .STAGES(NUM_CFG_STGS_HMC_ATG)) PIPE_SLV_REQ_HMC (.clk (clk), 
                                                              .rst_n (sync_rst_n), 
                                                              .in_bus({slv_tst_addr[1+4+gh], slv_tst_wdata[1+4+gh], slv_tst_wr[1+4+gh], slv_tst_rd[1+4+gh]}),
                                                              .out_bus({slv_tst_addr_pipe[1+4+gh], slv_tst_wdata_pipe[1+4+gh], slv_tst_wr_pipe[1+4+gh], slv_tst_rd_pipe[1+4+gh]})
                                                              );

      lib_pipe #(.WIDTH(32+1), .STAGES(NUM_CFG_STGS_HMC_ATG)) PIPE_SLV_ACK_HMC (.clk (clk), 
                                                         .rst_n (sync_rst_n), 
                                                         .in_bus({tst_slv_ack[1+4+gh], tst_slv_rdata[1+4+gh]}),
                                                         .out_bus({tst_slv_ack_pipe[1+4+gh], tst_slv_rdata_pipe[1+4+gh]})
                                                         );

      lib_pipe #(.WIDTH(2), .STAGES(NUM_CFG_STGS_HMC_ATG)) PIPE_SCRB_HMC (.clk(clk), .rst_n(sync_rst_n),
                                                                          .in_bus({hmc_scrb_en[gh], hmc_scrb_done[gh]}),
                                                                          .out_bus({hmc_scrb_en_pipe[gh], hmc_scrb_done_pipe[gh]})
                                                                          );

      cl_tst_scrb #(.DATA_WIDTH(512),
                    .SCRB_BURST_LEN_MINUS1(HMC_SCRB_BURST_LEN_MINUS1),
                    .SCRB_MAX_ADDR(HMC_SCRB_MAX_ADDR),
                    .NO_SCRB_INST(NO_SCRB_INST)) CL_TST_HMC (
   
         .clk(clk),
         .rst_n(sync_rst_n),

         .cfg_addr(slv_tst_addr_pipe[1+4+gh]),
         .cfg_wdata(slv_tst_wdata_pipe[1+4+gh]),
         .cfg_wr(slv_tst_wr_pipe[1+4+gh]),
         .cfg_rd(slv_tst_rd_pipe[1+4+gh]),
         .tst_cfg_ack(tst_slv_ack[1+4+gh]),
         .tst_cfg_rdata(tst_slv_rdata[1+4+gh]),

         .awid(cl_sh_hmc_awid[gh]),
         .awaddr(cl_sh_hmc_awaddr[gh]), 
         .awlen(cl_sh_hmc_awlen[gh]),
         .awuser(cl_sh_hmc_awuser[gh]),
         .awvalid(cl_sh_hmc_awvalid[gh]),
         .awready(sh_cl_hmc_awready[gh]),
   
         .wid(cl_sh_hmc_wid[gh]),
         .wdata(cl_sh_hmc_wdata[gh]),
         .wstrb(cl_sh_hmc_wstrb[gh]),
         .wlast(cl_sh_hmc_wlast[gh]),
         .wvalid(cl_sh_hmc_wvalid[gh]),
         .wready(sh_cl_hmc_wready[gh]),

         .bid(sh_cl_hmc_bid[gh]),
         .bresp(sh_cl_hmc_bresp[gh]),
         .buser(sh_cl_hmc_buser[gh]),
         .bvalid(sh_cl_hmc_bvalid[gh]),
         .bready(cl_sh_hmc_bready[gh]),

         .arid(cl_sh_hmc_arid[gh]),
         .araddr(cl_sh_hmc_araddr[gh]),
         .arlen(cl_sh_hmc_arlen[gh]),
         .aruser(cl_sh_hmc_aruser[gh]),
         .arvalid(cl_sh_hmc_arvalid[gh]),
         .arready(sh_cl_hmc_arready[gh]),

         .rid(sh_cl_hmc_rid[gh]),
         .rdata(sh_cl_hmc_rdata[gh]),
         .rresp(sh_cl_hmc_rresp[gh]),
         .rlast(sh_cl_hmc_rlast[gh]),
         .ruser(sh_cl_hmc_ruser[gh]),
         .rvalid(sh_cl_hmc_rvalid[gh]),
         .rready(cl_sh_hmc_rready[gh]),

         .scrb_enable(hmc_scrb_en_pipe[gh]),
         .scrb_done  (hmc_scrb_done[gh]),

         .scrb_dbg_state(),
         .scrb_dbg_addr ()
      );
   end
endgenerate
`else // !`ifdef HMC_PRESENT
   assign hmc_scrb_done_pipe[1:0] = 2'd3;
   assign hmc_stat_ack = 1;
   assign hmc_stat_rdata = 32'h0;
   assign hmc_stat_int = 0;

`endif //  `ifdef HMC_PRESENT
   
`ifdef AURORA
//Aurora
   logic  [511:0]       cl_sh_aurora_tx_tdata [NUM_GTY-1:0]   ;
   logic  [NUM_GTY-1:0] cl_sh_aurora_tx_tlast                 ;
   logic  [63:0]        cl_sh_aurora_tx_tkeep [NUM_GTY-1:0]   ;
   logic  [NUM_GTY-1:0] cl_sh_aurora_tx_tvalid                ;
   logic [NUM_GTY-1:0] sh_cl_aurora_tx_tready                 ;
   logic [511:0]       sh_cl_aurora_rx_tdata [NUM_GTY-1:0]    ;
   logic [NUM_GTY-1:0] sh_cl_aurora_rx_tlast                  ;
   logic [63:0]        sh_cl_aurora_rx_tkeep [NUM_GTY-1:0]    ;
   logic [NUM_GTY-1:0] sh_cl_aurora_rx_tvalid                 ;
   logic  [NUM_GTY-1:0]  cl_sh_aurora_nfc_tvalid              ;
   logic  [15:0]         cl_sh_aurora_nfc_tdata [NUM_GTY-1:0] ;
   logic [NUM_GTY-1:0] sh_cl_aurora_nfc_tready;                

genvar gq;
generate
   for (gq=0; gq<NUM_GTY; gq++)
   begin: gen_qsfp_tst 

      lib_pipe #(.WIDTH(32+32+1+1), .STAGES(NUM_CFG_STGS_AURORA_ATG)) PIPE_SLV_REQ_AURORA (.clk (clk), 
                                                              .rst_n (sync_rst_n), 
                                                              .in_bus({slv_tst_addr[1+4+4+gq], slv_tst_wdata[1+4+4+gq], slv_tst_wr[1+4+4+gq], slv_tst_rd[1+4+4+gq]}),
                                                              .out_bus({slv_tst_addr_pipe[1+4+4+gq], slv_tst_wdata_pipe[1+4+4+gq], slv_tst_wr_pipe[1+4+4+gq], slv_tst_rd_pipe[1+4+4+gq]})
                                                              );

      lib_pipe #(.WIDTH(32+1), .STAGES(NUM_CFG_STGS_AURORA_ATG)) PIPE_SLV_ACK_AURORA (.clk (clk), 
                                                         .rst_n (sync_rst_n), 
                                                         .in_bus({tst_slv_ack[1+4+4+gq], tst_slv_rdata[1+4+4+gq]}),
                                                         .out_bus({tst_slv_ack_pipe[1+4+4+gq], tst_slv_rdata_pipe[1+4+4+gq]})
                                                         );

      cl_pkt_tst #(.DATA_WIDTH(512)) CL_PKT_TST_QSFP (
   
         .clk(clk),
         .rst_n(sync_rst_n),

         .cfg_addr(slv_tst_addr_pipe[1+4+4+gq]),
         .cfg_wdata(slv_tst_wdata_pipe[1+4+4+gq]),
         .cfg_wr(slv_tst_wr_pipe[1+4+4+gq]),
         .cfg_rd(slv_tst_rd_pipe[1+4+4+gq]),
         .tst_cfg_ack(tst_slv_ack[1+4+4+gq]),
         .tst_cfg_rdata(tst_slv_rdata[1+4+4+gq]),

         .channel_ready  (cl_sh_aurora_channel_up[gq]),
         .axis_tx_tvalid (cl_sh_aurora_tx_tvalid[gq]),
         .axis_tx_tdata  (cl_sh_aurora_tx_tdata[gq]),
         .axis_tx_tlast  (cl_sh_aurora_tx_tlast[gq]),
         .axis_tx_tkeep  (cl_sh_aurora_tx_tkeep[gq]),
         .axis_tx_tready (sh_cl_aurora_tx_tready[gq]),

         .axis_rx_tvalid (sh_cl_aurora_rx_tvalid[gq]),
         .axis_rx_tdata  (sh_cl_aurora_rx_tdata[gq]),
         .axis_rx_tlast  (sh_cl_aurora_rx_tlast[gq]),
         .axis_rx_tkeep  (sh_cl_aurora_rx_tkeep[gq]),
         .axis_rx_tready ()
                                                      
       );
   end // block: gen_qsfp_tst
endgenerate

`endif //  `ifdef AURORA
   
`ifndef VU190
    lib_pipe #(.WIDTH(32+32+1+1), .STAGES(NUM_CFG_STGS_INT_TST)) PIPE_SLV_REQ_INT (.clk (clk), 
                                                                .rst_n (sync_rst_n), 
                                                                .in_bus({slv_tst_addr[1+4+4+4], slv_tst_wdata[1+4+4+4], slv_tst_wr[1+4+4+4], slv_tst_rd[1+4+4+4]}),
                                                                .out_bus({slv_tst_addr_pipe[1+4+4+4], slv_tst_wdata_pipe[1+4+4+4], slv_tst_wr_pipe[1+4+4+4], slv_tst_rd_pipe[1+4+4+4]})
                                                                );
    
    lib_pipe #(.WIDTH(32+1), .STAGES(NUM_CFG_STGS_INT_TST)) PIPE_SLV_ACK_INT (.clk (clk), 
                                                           .rst_n (sync_rst_n), 
                                                           .in_bus({tst_slv_ack[1+4+4+4], tst_slv_rdata[1+4+4+4]}),
                                                           .out_bus({tst_slv_ack_pipe[1+4+4+4], tst_slv_rdata_pipe[1+4+4+4]})
                                                           );
    
    cl_int_tst CL_INT_TST 
      (
       .clk                 (clk),
       .rst_n               (sync_rst_n),
 
 /*      .cfg_addr            (slv_tst_addr[1+4+4+4]),
       .cfg_wdata           (slv_tst_wdata[1+4+4+4]),
       .cfg_wr              (slv_tst_wr[1+4+4+4]),
       .cfg_rd              (slv_tst_rd[1+4+4+4]),
       .tst_cfg_ack         (tst_slv_ack_pipe[1+4+4+4]),
       .tst_cfg_rdata       (tst_slv_rdata_pipe[1+4+4+4]),
 */
       .cfg_addr            (slv_tst_addr_pipe[1+4+4+4]),
       .cfg_wdata           (slv_tst_wdata_pipe[1+4+4+4]),
       .cfg_wr              (slv_tst_wr_pipe[1+4+4+4]),
       .cfg_rd              (slv_tst_rd_pipe[1+4+4+4]),
       .tst_cfg_ack         (tst_slv_ack[1+4+4+4]),
       .tst_cfg_rdata       (tst_slv_rdata[1+4+4+4])

 `ifndef NO_XDMA
       ,
       .cl_sh_irq_req       (cl_sh_apppf_irq_req),
       .sh_cl_irq_ack       (sh_cl_apppf_irq_ack)
 `else
  `ifdef MSIX_PRESENT
       ,
       .cl_sh_msix_int      (cl_sh_msix_int),
       .cl_sh_msix_vec      (cl_sh_msix_vec),
       .sh_cl_msix_int_sent (sh_cl_msix_int_sent),
       .sh_cl_msix_int_ack  (sh_cl_msix_int_ack)
  `endif
       
 `endif // !`ifndef NO_XDMA
       
       
       );

`endif //  `ifndef VU190


`ifndef NO_XDMA


   `ifdef CL_CLK_COUNT
      //Replace this region with some misc registers (clock count)
      
      logic[31:0] clk_count_main;
      logic[31:0] clk_count_1;
      logic[31:0] clk_count_2;
      logic[31:0] clk_count_3;
      logic clk_count_inp_3;
      logic clk_count_inp_main;
      logic clk_count_inp_1;
      logic clk_count_inp_2;

      logic clk_count_en;
      logic clk_count_rst;
      
      assign tst_slv_ack[1+4+4+4+1] = slv_tst_wr_pipe[1+4+4+4+1] || slv_tst_rd_pipe[1+4+4+4+1];
      
      assign tst_slv_rdata[1+4+4+4+1] =   (slv_tst_addr[1+4+4+4+1][7:0]==8'h00)?    clk_count_main:
                                          (slv_tst_addr[1+4+4+4+1][7:0]==8'h04)?    clk_count_1:
                                          (slv_tst_addr[1+4+4+4+1][7:0]==8'h08)?    clk_count_2:
                                          (slv_tst_addr[1+4+4+4+1][7:0]==8'h0c)?    clk_count_3:
                                          (slv_tst_addr[1+4+4+4+1][7:0]==8'h10)?    clk_count_inp_main:
                                          (slv_tst_addr[1+4+4+4+1][7:0]==8'h14)?    {clk_count_rst, clk_count_en}:
                                                                                    32'hbaad_c1c4;

   
      
      always @(negedge sync_rst_n or posedge clk) 
         if (!sync_rst_n)
         begin
            clk_count_rst <= 0;
            clk_count_en <= 0;
         end
         else if (slv_tst_wr_pipe[1+4+4+4+1]  && (slv_tst_addr_pipe[1+4+4+4+1][7:0]==8'h14))
         begin
            clk_count_rst <= slv_tst_wdata_pipe[1+4+4+4+1][1];
            clk_count_en <= slv_tst_wdata_pipe[1+4+4+4+1][0];
         end
      
      always @(posedge clk_extra_a3)
         clk_count_inp_3 <= (clk_count_3<1000);
      
      sync SYNC_EN_1 (.clk(clk_extra_a1), .rst_n(1'b1), .in(clk_count_en), .sync_out(sync_clk_count_en_1));
      sync SYNC_EN_2 (.clk(clk_extra_a2), .rst_n(1'b1), .in(clk_count_en), .sync_out(sync_clk_count_en_2));
      sync SYNC_EN_3 (.clk(clk_extra_a2), .rst_n(1'b1), .in(clk_count_en), .sync_out(sync_clk_count_en_3));

      sync SYNC_RST_1 (.clk(clk_extra_a1), .rst_n(1'b1), .in(clk_count_rst), .sync_out(sync_clk_count_rst_1));
      sync SYNC_RST_2 (.clk(clk_extra_a2), .rst_n(1'b1), .in(clk_count_rst), .sync_out(sync_clk_count_rst_2));
      sync SYNC_RST_3 (.clk(clk_extra_a2), .rst_n(1'b1), .in(clk_count_rst), .sync_out(sync_clk_count_rst_3));
      
      always @(posedge clk)
         if (clk_count_rst)
            clk_count_main <= 0;
         else if (clk_count_en)
            clk_count_main <= clk_count_main + 1;
        
      always @(posedge clk_extra_a1)
         if (sync_clk_count_rst_1)
            clk_count_1 <= 0;
         else if (sync_clk_count_en_1)
            clk_count_1 <= clk_count_1 + 1;
        
      always @(posedge clk_extra_a2)
         if (sync_clk_count_rst_2)
            clk_count_2 <= 0;
         else if (sync_clk_count_en_2)
            clk_count_2 <= clk_count_2 + 1;
        
      always @(posedge clk_extra_a3)
         if (sync_clk_count_rst_3)
            clk_count_3 <= 0;
         else if (sync_clk_count_en_3)
            clk_count_3 <= clk_count_3 + 1;


         lib_pipe #(.WIDTH(32+32+1+1), .STAGES(NUM_CFG_STGS_XDMA)) PIPE_SLV_REQ_MISC (.clk (clk), 
                                                                                      .rst_n (sync_rst_n), 
                                                                                      .in_bus({slv_tst_addr[1+4+4+4+1], slv_tst_wdata[1+4+4+4+1], slv_tst_wr[1+4+4+4+1], slv_tst_rd[1+4+4+4+1]}),
                                                                                      .out_bus({slv_tst_addr_pipe[1+4+4+4+1], slv_tst_wdata_pipe[1+4+4+4+1], slv_tst_wr_pipe[1+4+4+4+1], slv_tst_rd_pipe[1+4+4+4+1]})
                                                                                      );
         
         lib_pipe #(.WIDTH(32+1), .STAGES(NUM_CFG_STGS_XDMA)) PIPE_SLV_ACK_MISC (.clk (clk), 
                                                                                 .rst_n (sync_rst_n), 
                                                                                 .in_bus({tst_slv_ack[1+4+4+4+1], tst_slv_rdata[1+4+4+4+1]}),
                                                                                 .out_bus({tst_slv_ack_pipe[1+4+4+4+1], tst_slv_rdata_pipe[1+4+4+4+1]})
                                                                                 );
      
   `else    //CL_CLK_COUNT
   //removing XDCFG - sundeepa
   assign tst_slv_ack[1+4+4+4+1] = 0;
   assign tst_slv_rdata[1+4+4+4+1] = 0;
   `endif


 
   
/*        
   // XDMA CFG AXI-L Master
   logic[4:0]   sh_cl_xdma_pcis_awid_q;
   logic [63:0] sh_cl_xdma_pcis_awaddr_q;
   logic [7:0]  sh_cl_xdma_pcis_awlen_q;
   logic        sh_cl_xdma_pcis_awvalid_q;
   logic        cl_sh_xdma_pcis_awready_q;

   logic [511:0] sh_cl_xdma_pcis_wdata_q;
   logic [63:0]  sh_cl_xdma_pcis_wstrb_q;
   logic         sh_cl_xdma_pcis_wlast_q;
   logic         sh_cl_xdma_pcis_wvalid_q;
   logic         cl_sh_xdma_pcis_wready_q;

   logic [4:0]   cl_sh_xdma_pcis_bid_q;
   logic [1:0]   cl_sh_xdma_pcis_bresp_q;
   logic         cl_sh_xdma_pcis_bvalid_q;
   logic         sh_cl_xdma_pcis_bready_q;

   logic [4:0]   sh_cl_xdma_pcis_arid_q;
   logic [63:0]  sh_cl_xdma_pcis_araddr_q;
   logic [7:0]   sh_cl_xdma_pcis_arlen_q;
   logic         sh_cl_xdma_pcis_arvalid_q;
   logic         cl_sh_xdma_pcis_arready_q;

   logic [4:0]   cl_sh_xdma_pcis_rid_q;
   logic [511:0] cl_sh_xdma_pcis_rdata_q;
   logic [1:0]   cl_sh_xdma_pcis_rresp_q;
   logic         cl_sh_xdma_pcis_rlast_q;
   logic         cl_sh_xdma_pcis_rvalid_q;
   logic         sh_cl_xdma_pcis_rready_q;


 // AXI-Lite Register Slice for signals between CL and HL
   axi4_flop_fifo #(.IN_FIFO(1), .ADDR_WIDTH(64), .DATA_WIDTH(512), .ID_WIDTH(5), .A_USER_WIDTH(1), .FIFO_DEPTH(3)) XDMA_TST_AXI_REG_SLC (
    .aclk          (clk),
    .aresetn       (sync_rst_n),
    .sync_rst_n    (1'b1),
    .s_axi_awid    (sh_cl_xdma_pcis_awid),
    .s_axi_awaddr  (sh_cl_xdma_pcis_awaddr),
    .s_axi_awlen   (sh_cl_xdma_pcis_awlen),                                            
    .s_axi_awvalid (sh_cl_xdma_pcis_awvalid),
    .s_axi_awuser  (1'b0),
    .s_axi_awready (cl_sh_xdma_pcis_awready),
    .s_axi_wdata   (sh_cl_xdma_pcis_wdata),
    .s_axi_wstrb   (sh_cl_xdma_pcis_wstrb),
    .s_axi_wlast   (sh_cl_xdma_pcis_wlast),
    .s_axi_wuser   (1'b0),
    .s_axi_wvalid  (sh_cl_xdma_pcis_wvalid),
    .s_axi_wready  (cl_sh_xdma_pcis_wready),
    .s_axi_bid     (cl_sh_xdma_pcis_bid),
    .s_axi_bresp   (cl_sh_xdma_pcis_bresp),
    .s_axi_bvalid  (cl_sh_xdma_pcis_bvalid),
    .s_axi_buser   (),
    .s_axi_bready  (sh_cl_xdma_pcis_bready),
    .s_axi_arid    (sh_cl_xdma_pcis_arid),
    .s_axi_araddr  (sh_cl_xdma_pcis_araddr),
    .s_axi_arlen   (sh_cl_xdma_pcis_arlen), 
    .s_axi_arvalid (sh_cl_xdma_pcis_arvalid),
    .s_axi_aruser  (1'd0),
    .s_axi_arready (cl_sh_xdma_pcis_arready),
    .s_axi_rid     (cl_sh_xdma_pcis_rid),
    .s_axi_rdata   (cl_sh_xdma_pcis_rdata),
    .s_axi_rresp   (cl_sh_xdma_pcis_rresp),
    .s_axi_rlast   (cl_sh_xdma_pcis_rlast),
    .s_axi_ruser   (),
    .s_axi_rvalid  (cl_sh_xdma_pcis_rvalid),
    .s_axi_rready  (sh_cl_xdma_pcis_rready), 
    .m_axi_awid    (sh_cl_xdma_pcis_awid_q),
    .m_axi_awaddr  (sh_cl_xdma_pcis_awaddr_q), 
    .m_axi_awlen   (sh_cl_xdma_pcis_awlen_q),
    .m_axi_awvalid (sh_cl_xdma_pcis_awvalid_q),
    .m_axi_awuser  (),
    .m_axi_awready (cl_sh_xdma_pcis_awready_q),
    .m_axi_wdata   (sh_cl_xdma_pcis_wdata_q),  
    .m_axi_wstrb   (sh_cl_xdma_pcis_wstrb_q),
    .m_axi_wvalid  (sh_cl_xdma_pcis_wvalid_q), 
    .m_axi_wlast   (sh_cl_xdma_pcis_wlast_q),
    .m_axi_wuser   (),
    .m_axi_wready  (cl_sh_xdma_pcis_wready_q), 
    .m_axi_bresp   (cl_sh_xdma_pcis_bresp_q),  
    .m_axi_bvalid  (cl_sh_xdma_pcis_bvalid_q), 
    .m_axi_bid     (cl_sh_xdma_pcis_bid_q),
    .m_axi_buser   (1'b0),
    .m_axi_bready  (sh_cl_xdma_pcis_bready_q), 
    .m_axi_arid    (sh_cl_xdma_pcis_arid_q), 
    .m_axi_araddr  (sh_cl_xdma_pcis_araddr_q), 
    .m_axi_arlen   (sh_cl_xdma_pcis_arlen_q), 
    .m_axi_aruser  (), 
    .m_axi_arvalid (sh_cl_xdma_pcis_arvalid_q),
    .m_axi_arready (cl_sh_xdma_pcis_arready_q),
    .m_axi_rid     (cl_sh_xdma_pcis_rid_q),  
    .m_axi_rdata   (cl_sh_xdma_pcis_rdata_q),  
    .m_axi_rresp   (cl_sh_xdma_pcis_rresp_q),  
    .m_axi_rlast   (cl_sh_xdma_pcis_rlast_q),  
    .m_axi_ruser   (1'b0),
    .m_axi_rvalid  (cl_sh_xdma_pcis_rvalid_q), 
    .m_axi_rready  (sh_cl_xdma_pcis_rready_q)
   );


   cl_slv_axi_tst #(.DATA_WIDTH(512),
                    .ADDR_WIDTH(64),
                    .A_ID_WIDTH(5),
                    .D_ID_WIDTH(5),
                    .LEN_WIDTH(8),
                    .A_USER_WIDTH(1),
                    .W_USER_WIDTH(1),
                    .B_USER_WIDTH(1),
                    .R_USER_WIDTH(1)
                    ) 
   CL_XDMA_TST  (.clk(clk),
                 .rst_n(sync_rst_n),
                 
                 .cfg_addr(slv_tst_addr_pipe[1+4+4+4+1+1]),
                 .cfg_wdata(slv_tst_wdata_pipe[1+4+4+4+1+1]),
                 .cfg_wr(slv_tst_wr_pipe[1+4+4+4+1+1]),
                 .cfg_rd(slv_tst_rd_pipe[1+4+4+4+1+1]),
                 .tst_cfg_ack(tst_slv_ack[1+4+4+4+1+1]),
                 .tst_cfg_rdata(tst_slv_rdata[1+4+4+4+1+1]),
      
                 .awid     (sh_cl_xdma_awid_q),   
                 .awaddr   (sh_cl_xdma_awaddr_q), 
                 .awlen    (sh_cl_xdma_awlen_q),  
                 .awuser   (1'b0),
                 .awvalid  (sh_cl_xdma_awvalid_q),
                 .awready  (cl_sh_xdma_awready_q),
                 .wdata    (sh_cl_xdma_wdata_q),  
                 .wstrb    (sh_cl_xdma_wstrb_q),  
                 .wlast    (sh_cl_xdma_wlast_q),  
                 .wuser    (1'b0),
                 .wvalid   (sh_cl_xdma_wvalid_q), 
                 .wready   (cl_sh_xdma_wready_q), 
                 .bid      (cl_sh_xdma_bid_q),    
                 .bresp    (cl_sh_xdma_bresp_q),  
                 .buser    (),
                 .bvalid   (cl_sh_xdma_bvalid_q), 
                 .bready   (sh_cl_xdma_bready_q), 
                 .arid     (sh_cl_xdma_arid_q),   
                 .araddr   (sh_cl_xdma_araddr_q), 
                 .arlen    (sh_cl_xdma_arlen_q),  
                 .aruser   (1'b0),
                 .arvalid  (sh_cl_xdma_arvalid_q),
                 .arready  (cl_sh_xdma_arready_q),
                 .rid      (cl_sh_xdma_rid_q),    
                 .rdata    (cl_sh_xdma_rdata_q),  
                 .rresp    (cl_sh_xdma_rresp_q),  
                 .rlast    (cl_sh_xdma_rlast_q),  
                 .ruser    (),
                 .rvalid   (cl_sh_xdma_rvalid_q), 
                 .rready   (sh_cl_xdma_rready_q)
                 
                 );
*/
`ifdef OCL_TG_CTL
  assign cl_sh_pcis_awready = 0;
  assign cl_sh_pcis_arready = 0;
  assign cl_sh_pcis_wready = 0;
  assign cl_sh_pcis_bvalid = 0;
  assign cl_sh_pcis_rvalid = 0;
`endif


   axi_crossbar_0 AXI_CROSSBAR (
       .aclk(clk),
       .aresetn(sync_rst_n),

       .s_axi_awid(sh_cl_dma_pcis_awid_q),
       .s_axi_awaddr(sh_cl_dma_pcis_awaddr_q),
       .s_axi_awlen(sh_cl_dma_pcis_awlen_q),
       .s_axi_awsize(3'b110),
       .s_axi_awburst(2'b1),
       .s_axi_awlock(1'b0),
       .s_axi_awcache(4'b11),
       .s_axi_awprot(3'b10),
       .s_axi_awqos(4'b0),
       .s_axi_awvalid(sh_cl_dma_pcis_awvalid_q),
       .s_axi_awready(cl_sh_dma_pcis_awready_q),

       .s_axi_wdata(sh_cl_dma_pcis_wdata_q),
       .s_axi_wstrb(sh_cl_dma_pcis_wstrb_q),
       .s_axi_wlast(sh_cl_dma_pcis_wlast_q),
       .s_axi_wvalid(sh_cl_dma_pcis_wvalid_q),
       .s_axi_wready(cl_sh_dma_pcis_wready_q),

       .s_axi_bid(cl_sh_dma_pcis_bid_q),
       .s_axi_bresp(cl_sh_dma_pcis_bresp_q),
       .s_axi_bvalid(cl_sh_dma_pcis_bvalid_q),
       .s_axi_bready(sh_cl_dma_pcis_bready_q),

       .s_axi_arid(sh_cl_dma_pcis_arid_q),
       .s_axi_araddr(sh_cl_dma_pcis_araddr_q),
       .s_axi_arlen(sh_cl_dma_pcis_arlen_q),
       .s_axi_arsize(3'b110),
       .s_axi_arburst(2'b1),
       .s_axi_arlock(1'b0),
       .s_axi_arcache(4'b11),
       .s_axi_arprot(3'b10),
       .s_axi_arqos(4'b0),
       .s_axi_arvalid(sh_cl_dma_pcis_arvalid_q),
       .s_axi_arready(cl_sh_dma_pcis_arready_q),

       .s_axi_rid(cl_sh_dma_pcis_rid_q),
       .s_axi_rdata(cl_sh_dma_pcis_rdata_q),
       .s_axi_rresp(cl_sh_dma_pcis_rresp_q),
       .s_axi_rlast(cl_sh_dma_pcis_rlast_q),
       .s_axi_rvalid(cl_sh_dma_pcis_rvalid_q),
       .s_axi_rready(sh_cl_dma_pcis_rready_q), 

       .m_axi_awid({sh_cl_pcis_awid, lcl_cl_sh_ddr_awid_q[2][5:0], cl_sh_ddr_awid_q[5:0], lcl_cl_sh_ddr_awid_q[1][5:0], lcl_cl_sh_ddr_awid_q[0][5:0]}),
       .m_axi_awaddr({sh_cl_pcis_awaddr, lcl_cl_sh_ddr_awaddr_q[2], cl_sh_ddr_awaddr_q, lcl_cl_sh_ddr_awaddr_q[1], lcl_cl_sh_ddr_awaddr_q[0]}),
       .m_axi_awlen({sh_cl_pcis_awlen, lcl_cl_sh_ddr_awlen_q[2], cl_sh_ddr_awlen_q, lcl_cl_sh_ddr_awlen_q[1], lcl_cl_sh_ddr_awlen_q[0]}),
       .m_axi_awsize(),
       .m_axi_awburst(),
       .m_axi_awlock(),
       .m_axi_awcache(),
       .m_axi_awprot(),
       .m_axi_awregion(),
       .m_axi_awqos(),
       .m_axi_awvalid({sh_cl_pcis_awvalid, lcl_cl_sh_ddr_awvalid_q[2], cl_sh_ddr_awvalid_q, lcl_cl_sh_ddr_awvalid_q[1], lcl_cl_sh_ddr_awvalid_q[0]}),
       .m_axi_awready({cl_sh_pcis_awready, lcl_sh_cl_ddr_awready_q[2], sh_cl_ddr_awready_q, lcl_sh_cl_ddr_awready_q[1], lcl_sh_cl_ddr_awready_q[0]}),
  
       .m_axi_wdata({sh_cl_pcis_wdata, lcl_cl_sh_ddr_wdata_q[2], cl_sh_ddr_wdata_q, lcl_cl_sh_ddr_wdata_q[1], lcl_cl_sh_ddr_wdata_q[0]}),
       .m_axi_wstrb({sh_cl_pcis_wstrb, lcl_cl_sh_ddr_wstrb_q[2], cl_sh_ddr_wstrb_q, lcl_cl_sh_ddr_wstrb_q[1], lcl_cl_sh_ddr_wstrb_q[0]}),
       .m_axi_wlast({sh_cl_pcis_wlast, lcl_cl_sh_ddr_wlast_q[2], cl_sh_ddr_wlast_q, lcl_cl_sh_ddr_wlast_q[1], lcl_cl_sh_ddr_wlast_q[0]}),
       .m_axi_wvalid({sh_cl_pcis_wvalid, lcl_cl_sh_ddr_wvalid_q[2], cl_sh_ddr_wvalid_q, lcl_cl_sh_ddr_wvalid_q[1], lcl_cl_sh_ddr_wvalid_q[0]}),
       .m_axi_wready({cl_sh_pcis_wready, lcl_sh_cl_ddr_wready_q[2], sh_cl_ddr_wready_q, lcl_sh_cl_ddr_wready_q[1], lcl_sh_cl_ddr_wready_q[0]}),
    
       .m_axi_bid({cl_sh_pcis_bid, lcl_sh_cl_ddr_bid_q[2][5:0], sh_cl_ddr_bid_q[5:0], lcl_sh_cl_ddr_bid_q[1][5:0], lcl_sh_cl_ddr_bid_q[0][5:0]}),
       .m_axi_bresp({cl_sh_pcis_bresp, lcl_sh_cl_ddr_bresp_q[2], sh_cl_ddr_bresp_q, lcl_sh_cl_ddr_bresp_q[1], lcl_sh_cl_ddr_bresp_q[0]}),
       .m_axi_bvalid({cl_sh_pcis_bvalid, lcl_sh_cl_ddr_bvalid_q[2], sh_cl_ddr_bvalid_q, lcl_sh_cl_ddr_bvalid_q[1], lcl_sh_cl_ddr_bvalid_q[0]}),
       .m_axi_bready({sh_cl_pcis_bready, lcl_cl_sh_ddr_bready_q[2], cl_sh_ddr_bready_q, lcl_cl_sh_ddr_bready_q[1], lcl_cl_sh_ddr_bready_q[0]}),
  
       .m_axi_arid({sh_cl_pcis_arid, lcl_cl_sh_ddr_arid_q[2][5:0], cl_sh_ddr_arid_q[5:0], lcl_cl_sh_ddr_arid_q[1][5:0], lcl_cl_sh_ddr_arid_q[0][5:0]}),
       .m_axi_araddr({sh_cl_pcis_araddr, lcl_cl_sh_ddr_araddr_q[2], cl_sh_ddr_araddr_q, lcl_cl_sh_ddr_araddr_q[1], lcl_cl_sh_ddr_araddr_q[0]}),
       .m_axi_arlen({sh_cl_pcis_arlen, lcl_cl_sh_ddr_arlen_q[2], cl_sh_ddr_arlen_q, lcl_cl_sh_ddr_arlen_q[1], lcl_cl_sh_ddr_arlen_q[0]}),
       .m_axi_arsize(),
       .m_axi_arburst(),
       .m_axi_arlock(),
       .m_axi_arcache(),
       .m_axi_arprot(),
       .m_axi_arregion(),
       .m_axi_arqos(),
       .m_axi_arvalid({sh_cl_pcis_arvalid, lcl_cl_sh_ddr_arvalid_q[2], cl_sh_ddr_arvalid_q, lcl_cl_sh_ddr_arvalid_q[1], lcl_cl_sh_ddr_arvalid_q[0]}),
       .m_axi_arready({cl_sh_pcis_arready, lcl_sh_cl_ddr_arready_q[2], sh_cl_ddr_arready_q, lcl_sh_cl_ddr_arready_q[1], lcl_sh_cl_ddr_arready_q[0]}),

       .m_axi_rid({cl_sh_pcis_rid, lcl_sh_cl_ddr_rid_q[2][5:0], sh_cl_ddr_rid_q[5:0], lcl_sh_cl_ddr_rid_q[1][5:0], lcl_sh_cl_ddr_rid_q[0][5:0]}),
       .m_axi_rdata({cl_sh_pcis_rdata, lcl_sh_cl_ddr_rdata_q[2], sh_cl_ddr_rdata_q, lcl_sh_cl_ddr_rdata_q[1], lcl_sh_cl_ddr_rdata_q[0]}),
       .m_axi_rresp({cl_sh_pcis_rresp, lcl_sh_cl_ddr_rresp_q[2], sh_cl_ddr_rresp_q, lcl_sh_cl_ddr_rresp_q[1], lcl_sh_cl_ddr_rresp_q[0]}),
       .m_axi_rlast({cl_sh_pcis_rlast, lcl_sh_cl_ddr_rlast_q[2], sh_cl_ddr_rlast_q, lcl_sh_cl_ddr_rlast_q[1], lcl_sh_cl_ddr_rlast_q[0]}),
       .m_axi_rvalid({cl_sh_pcis_rvalid, lcl_sh_cl_ddr_rvalid_q[2], sh_cl_ddr_rvalid_q, lcl_sh_cl_ddr_rvalid_q[1], lcl_sh_cl_ddr_rvalid_q[0]}),
       .m_axi_rready({sh_cl_pcis_rready, lcl_cl_sh_ddr_rready_q[2], cl_sh_ddr_rready_q, lcl_cl_sh_ddr_rready_q[1], lcl_cl_sh_ddr_rready_q[0]})
   );

   
`endif //  `ifndef NO_XDMA
   
   
//----------------------------------------------------------
// Interfaces 
//----------------------------------------------------------
   
    
`ifndef NO_CL_DDR                                             
//----------------------------------------- 
// DDR controller instantiation   
//----------------------------------------- 
sh_ddr #(
         `ifdef DDR_A_SH 
            .DDR_A_PRESENT(0),
            .DDR_A_IO(0),
         `else
            .DDR_A_PRESENT(DDR_A_PRESENT),
            .DDR_A_IO(1),
         `endif
         .DDR_B_PRESENT(DDR_B_PRESENT),
         .DDR_D_PRESENT(DDR_D_PRESENT)
   ) SH_DDR
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
   .RST_DIMM_A_N(RST_DIMM_A_N),
   .M_A_PAR(M_A_PAR),
   .M_A_DQ(M_A_DQ),
   .M_A_ECC(M_A_ECC),
   .M_A_DQS_DP(M_A_DQS_DP),
   .M_A_DQS_DN(M_A_DQS_DN),
   .cl_RST_DIMM_A_N(cl_RST_DIMM_A_N),
   
   
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
   .cl_RST_DIMM_B_N(cl_RST_DIMM_B_N),

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
   .M_D_DQS_DN(M_D_DQS_DN),
   .cl_RST_DIMM_D_N(cl_RST_DIMM_D_N),

   //------------------------------------------------------
   // DDR-4 Interface from CL (AXI-4)
   //------------------------------------------------------
   .cl_sh_ddr_awid(lcl_cl_sh_ddr_awid),
   .cl_sh_ddr_awaddr(lcl_cl_sh_ddr_awaddr),
   .cl_sh_ddr_awlen(lcl_cl_sh_ddr_awlen),
   .cl_sh_ddr_awvalid(lcl_cl_sh_ddr_awvalid),
   .sh_cl_ddr_awready(lcl_sh_cl_ddr_awready),

   .cl_sh_ddr_wid(lcl_cl_sh_ddr_wid),
   .cl_sh_ddr_wdata(lcl_cl_sh_ddr_wdata),
   .cl_sh_ddr_wstrb(lcl_cl_sh_ddr_wstrb),
   .cl_sh_ddr_wlast(lcl_cl_sh_ddr_wlast),
   .cl_sh_ddr_wvalid(lcl_cl_sh_ddr_wvalid),
   .sh_cl_ddr_wready(lcl_sh_cl_ddr_wready),

   .sh_cl_ddr_bid(lcl_sh_cl_ddr_bid),
   .sh_cl_ddr_bresp(lcl_sh_cl_ddr_bresp),
   .sh_cl_ddr_bvalid(lcl_sh_cl_ddr_bvalid),
   .cl_sh_ddr_bready(lcl_cl_sh_ddr_bready),

   .cl_sh_ddr_arid(lcl_cl_sh_ddr_arid),
   .cl_sh_ddr_araddr(lcl_cl_sh_ddr_araddr),
   .cl_sh_ddr_arlen(lcl_cl_sh_ddr_arlen),
   .cl_sh_ddr_arvalid(lcl_cl_sh_ddr_arvalid),
   .sh_cl_ddr_arready(lcl_sh_cl_ddr_arready),

   .sh_cl_ddr_rid(lcl_sh_cl_ddr_rid),
   .sh_cl_ddr_rdata(lcl_sh_cl_ddr_rdata),
   .sh_cl_ddr_rresp(lcl_sh_cl_ddr_rresp),
   .sh_cl_ddr_rlast(lcl_sh_cl_ddr_rlast),
   .sh_cl_ddr_rvalid(lcl_sh_cl_ddr_rvalid),
   .cl_sh_ddr_rready(lcl_cl_sh_ddr_rready),

   .sh_cl_ddr_is_ready(lcl_sh_cl_ddr_is_ready),

   .sh_ddr_stat_addr0  (sh_ddr_stat_addr_q[0]) ,
   .sh_ddr_stat_wr0    (sh_ddr_stat_wr_q[0]     ) , 
   .sh_ddr_stat_rd0    (sh_ddr_stat_rd_q[0]     ) , 
   .sh_ddr_stat_wdata0 (sh_ddr_stat_wdata_q[0]  ) , 
   .ddr_sh_stat_ack0   (ddr_sh_stat_ack_q[0]    ) ,
   .ddr_sh_stat_rdata0 (ddr_sh_stat_rdata_q[0]  ),
   .ddr_sh_stat_int0   (ddr_sh_stat_int_q[0]    ),

   .sh_ddr_stat_addr1  (sh_ddr_stat_addr_q[1]) ,
   .sh_ddr_stat_wr1    (sh_ddr_stat_wr_q[1]     ) , 
   .sh_ddr_stat_rd1    (sh_ddr_stat_rd_q[1]     ) , 
   .sh_ddr_stat_wdata1 (sh_ddr_stat_wdata_q[1]  ) , 
   .ddr_sh_stat_ack1   (ddr_sh_stat_ack_q[1]    ) ,
   .ddr_sh_stat_rdata1 (ddr_sh_stat_rdata_q[1]  ),
   .ddr_sh_stat_int1   (ddr_sh_stat_int_q[1]    ),

   .sh_ddr_stat_addr2  (sh_ddr_stat_addr_q[2]) ,
   .sh_ddr_stat_wr2    (sh_ddr_stat_wr_q[2]     ) , 
   .sh_ddr_stat_rd2    (sh_ddr_stat_rd_q[2]     ) , 
   .sh_ddr_stat_wdata2 (sh_ddr_stat_wdata_q[2]  ) , 
   .ddr_sh_stat_ack2   (ddr_sh_stat_ack_q[2]    ) ,
   .ddr_sh_stat_rdata2 (ddr_sh_stat_rdata_q[2]  ),
   .ddr_sh_stat_int2   (ddr_sh_stat_int_q[2]    )

   );
`else // !`ifndef NO_CL_DDR
   assign lcl_sh_cl_ddr_is_ready = 3'b111;

   assign ddr_sh_stat_int[0] = 0;
   assign ddr_sh_stat_ack[0] = 1;
   assign ddr_sh_stat_rdata[0] = 0;

   assign ddr_sh_stat_int[1] = 0;
   assign ddr_sh_stat_ack[1] = 1;
   assign ddr_sh_stat_rdata[1] = 0;

   assign ddr_sh_stat_int[2] = 0;
   assign ddr_sh_stat_ack[2] = 1;
   assign ddr_sh_stat_rdata[2] = 0;
   
`endif //  `ifndef NO_CL_DDR
   
   logic sh_cl_ddr_is_ready_q;
   logic sh_cl_ddra_is_ready_q;
   always_ff @(posedge clk or negedge sync_rst_n)
     if (!sync_rst_n)
     begin
       sh_cl_ddr_is_ready_q <= 1'b0;
       sh_cl_ddra_is_ready_q <= 0;
     end
     else
     begin
       sh_cl_ddr_is_ready_q <= sh_cl_ddr_is_ready;
      `ifdef DDR_A_SH
         sh_cl_ddra_is_ready_q <= sh_cl_ddra_is_ready;
      `endif
     end  

`ifdef DDR_A_SH
   assign all_ddr_is_ready = {lcl_sh_cl_ddr_is_ready[2], sh_cl_ddr_is_ready_q, lcl_sh_cl_ddr_is_ready[1], sh_cl_ddra_is_ready_q};
`else 
   assign all_ddr_is_ready = {lcl_sh_cl_ddr_is_ready[2], sh_cl_ddr_is_ready_q, lcl_sh_cl_ddr_is_ready[1:0]};
`endif

   assign all_ddr_scrb_done = {ddr_scrb_done_pipe[2], ddr_scrb_done_pipe[3], ddr_scrb_done_pipe[1:0]};
   
//----------------------------------------- 
// Aurora instantiation   
//----------------------------------------- 
`ifdef AURORA
   lib_pipe #(.WIDTH(1+1+8+32), .STAGES(NUM_CFG_STGS_AURORA_ATG)) PIPE_AURORA_STAT (.clk(clk), .rst_n(sync_rst_n),
                                                               .in_bus({sh_aurora_stat_wr, sh_aurora_stat_rd, sh_aurora_stat_addr, sh_aurora_stat_wdata}),
                                                               .out_bus({sh_aurora_stat_wr_q, sh_aurora_stat_rd_q, sh_aurora_stat_addr_q, sh_aurora_stat_wdata_q})
                                                               );


   lib_pipe #(.WIDTH(1+8+32), .STAGES(NUM_CFG_STGS_AURORA_ATG)) PIPE_AURORA_STAT_ACK (.clk(clk), .rst_n(sync_rst_n),
                                                               .in_bus({aurora_sh_stat_ack_q, aurora_sh_stat_int_q, aurora_sh_stat_rdata_q}),
                                                               .out_bus({aurora_sh_stat_ack, aurora_sh_stat_int, aurora_sh_stat_rdata})
                                                               );
   
aurora_wrapper #(.NUM_GTY(NUM_GTY))
   AURORA_WRAPPER (.core_clk          (clk          ),
                   .core_rst_n        (sync_rst_n        ),
`ifdef SH_SDA
                   .init_clk          (clk_main_a0),
`else                   
                   .init_clk          (clk     ),
`endif
                   
                   //.init_clk          (clk_xtra     ), // Removing clk_xtra. Aurora needs 125MHz init clock                   
                   .gty_refclk_p      (gty_refclk_p ), 
                   .gty_refclk_n      (gty_refclk_n ), 
                   .gty_txp           (gty_txp      ),      
                   .gty_txn           (gty_txn      ),      
                   .gty_rxp           (gty_rxp      ),      
                   .gty_rxn           (gty_rxn      ),      
                   .sh_cl_aurora_channel_up (cl_sh_aurora_channel_up),
                   .cl_sh_aurora_tx_tdata   (cl_sh_aurora_tx_tdata ),
                   .cl_sh_aurora_tx_tlast   (cl_sh_aurora_tx_tlast ),
                   .cl_sh_aurora_tx_tkeep   (cl_sh_aurora_tx_tkeep ),
                   .cl_sh_aurora_tx_tvalid  (cl_sh_aurora_tx_tvalid),
                   .sh_cl_aurora_tx_tready  (sh_cl_aurora_tx_tready),
                   .sh_cl_aurora_rx_tdata   (sh_cl_aurora_rx_tdata ),
                   .sh_cl_aurora_rx_tlast   (sh_cl_aurora_rx_tlast ),
                   .sh_cl_aurora_rx_tkeep   (sh_cl_aurora_rx_tkeep ),
                   .sh_cl_aurora_rx_tvalid  (sh_cl_aurora_rx_tvalid),
                   .cl_sh_aurora_nfc_tvalid   (cl_sh_aurora_nfc_tvalid),
                   .cl_sh_aurora_nfc_tdata    (cl_sh_aurora_nfc_tdata),
                   .sh_cl_aurora_nfc_tready   (sh_cl_aurora_nfc_tready),

                   .sh_aurora_stat_addr   (sh_aurora_stat_addr_q) ,
                   .sh_aurora_stat_wr     (sh_aurora_stat_wr_q     ) , 
                   .sh_aurora_stat_rd     (sh_aurora_stat_rd_q     ) , 
                   .sh_aurora_stat_wdata  (sh_aurora_stat_wdata_q  ) , 
                   .aurora_sh_stat_ack    (aurora_sh_stat_ack_q    ) ,
                   .aurora_sh_stat_rdata  (aurora_sh_stat_rdata_q  ) ,
                   .aurora_sh_stat_int    (aurora_sh_stat_int_q  ) ,
                                       
                   .acc_drp_wr(1'b0),
                   .acc_drp_en(1'b0),
                   .acc_drp_addr(9'd0),
                   .acc_drp_wdata(16'd0)
                   
                   );

`else
   assign aurora_sh_stat_int = 0;
   assign aurora_sh_stat_ack = 1;
   assign aurora_sh_stat_rdata = 0;
`endif //  `ifdef AURORA

//---------------------------------------------
// HMC instantiation
//---------------------------------------------
   logic [NUM_HMC-1:0] hmc_link_up;
   logic [NUM_HMC-1:0] hmc_link_up_pipe;
   
`ifdef HMC
   logic hmc_rst_free;

  `ifdef SIM
    localparam   HMC_SIM_F = 1;
  `else
    localparam   HMC_SIM_F = 0;
  `endif

   `ifdef SIM
      initial
      begin
         hmc_rst_free = 0;
         #100;
         $display("[%t] : Asserting hmc_rst_free", $realtime);
   
         hmc_rst_free = 1;
         repeat(200) @(posedge dev01_refclk_p);
         $display("[%t] : Deasserting hmc_rst_free", $realtime);
         hmc_rst_free = 0;
      end
   `else
      //FIXME 
      assign hmc_rst_free = 1'b0;
   `endif

   lib_pipe #(.WIDTH(1+1+8+32), .STAGES(NUM_CFG_STGS_HMC_ATG)) PIPE_HMC_STAT (.clk(clk), .rst_n(sync_rst_n),
                                                               .in_bus({sh_hmc_stat_wr[gd], sh_hmc_stat_rd[gd], sh_hmc_stat_addr[gd], sh_hmc_stat_wdata[gd]}),
                                                               .out_bus({sh_hmc_stat_wr_q[gd], sh_hmc_stat_rd_q[gd], sh_hmc_stat_addr_q[gd], sh_hmc_stat_wdata_q[gd]})
                                                               );


   lib_pipe #(.WIDTH(1+8+32), .STAGES(NUM_CFG_STGS_HMC_ATG)) PIPE_HMC_STAT_ACK (.clk(clk), .rst_n(sync_rst_n),
                                                               .in_bus({hmc_sh_stat_ack_q[gd], hmc_sh_stat_int_q[gd], hmc_sh_stat_rdata_q[gd]}),
                                                               .out_bus({hmc_sh_stat_ack[gd], hmc_sh_stat_int[gd], hmc_sh_stat_rdata[gd]})
                                                               );
   
   lib_pipe #(.WIDTH(NUM_HMC), .STAGES(NUM_CFG_STGS_HMC_ATG)) PIPE_HMC_LINKUP (.clk(clk), .rst_n(sync_rst_n),
                                                                               .in_bus (hmc_link_up),
                                                                               .out_bus(hmc_link_up_pipe)
                                                                               );
   

   hmc_wrapper #(.NUM_HMC(NUM_HMC),
                 .SIM_F (HMC_SIM_F)
                 ) HMC_WRAPPER
     (.core_clk                  (clk),
      .core_rst                  (hmc_rst_free),
      .dev01_refclk_p   (dev01_refclk_p  ),
      .dev01_refclk_n   (dev01_refclk_n  ),
      .dev23_refclk_p   (dev23_refclk_p  ),
      .dev23_refclk_n   (dev23_refclk_n  ),
      .hmc_iic_scl_i    (hmc_iic_scl_i   ),
      .hmc_iic_scl_o    (hmc_iic_scl_o   ),
      .hmc_iic_scl_t    (hmc_iic_scl_t   ),
      .hmc_iic_sda_i    (hmc_iic_sda_i   ),
      .hmc_iic_sda_o    (hmc_iic_sda_o   ),
      .hmc_iic_sda_t    (hmc_iic_sda_t   ),
      .hmc0_dev_p_rst_n (hmc0_dev_p_rst_n),
      .hmc0_rxps        (hmc0_rxps       ),
      .hmc0_txps        (hmc0_txps       ),
      .hmc0_txp         (hmc0_txp        ),
      .hmc0_txn         (hmc0_txn        ),
      .hmc0_rxp         (hmc0_rxp        ),
      .hmc0_rxn         (hmc0_rxn        ),
      .hmc1_dev_p_rst_n (hmc1_dev_p_rst_n),
      .hmc1_rxps        (hmc1_rxps       ),
      .hmc1_txps        (hmc1_txps       ),
      .hmc1_txp         (hmc1_txp        ),
      .hmc1_txn         (hmc1_txn        ),
      .hmc1_rxp         (hmc1_rxp        ),
      .hmc1_rxn         (hmc1_rxn        ),
      .hmc2_dev_p_rst_n (hmc2_dev_p_rst_n),
      .hmc2_rxps        (hmc2_rxps       ),
      .hmc2_txps        (hmc2_txps       ),
      .hmc2_txp         (hmc2_txp        ),
      .hmc2_txn         (hmc2_txn        ),
      .hmc2_rxp         (hmc2_rxp        ),
      .hmc2_rxn         (hmc2_rxn        ),
      .hmc3_dev_p_rst_n (hmc3_dev_p_rst_n),
      .hmc3_rxps        (hmc3_rxps       ),
      .hmc3_txps        (hmc3_txps       ),
      .hmc3_txp         (hmc3_txp        ),
      .hmc3_txn         (hmc3_txn        ),
      .hmc3_rxp         (hmc3_rxp        ),
      .hmc3_rxn         (hmc3_rxn        ),
      .hmc_link_up      (hmc_link_up     ),
      .hmc_clk_out      (                ),
      .hmc_rst_n_out    (                ),

      .cl_sh_hmc_awid    (cl_sh_hmc_awid    ),
      .cl_sh_hmc_awaddr  (cl_sh_hmc_awaddr  ),
      .cl_sh_hmc_awlen   (cl_sh_hmc_awlen   ),
      .cl_sh_hmc_awuser  (cl_sh_hmc_awuser  ),
      .cl_sh_hmc_awvalid (cl_sh_hmc_awvalid ),
      .sh_cl_hmc_awready (sh_cl_hmc_awready ),
      .cl_sh_hmc_wid     (cl_sh_hmc_wid     ),
      .cl_sh_hmc_wdata   (cl_sh_hmc_wdata   ),
      .cl_sh_hmc_wstrb   (cl_sh_hmc_wstrb   ),
      .cl_sh_hmc_wlast   (cl_sh_hmc_wlast   ),
      .cl_sh_hmc_wvalid  (cl_sh_hmc_wvalid  ),
      .sh_cl_hmc_wready  (sh_cl_hmc_wready  ),
      .sh_cl_hmc_bid     (sh_cl_hmc_bid     ),
      .sh_cl_hmc_bresp   (sh_cl_hmc_bresp   ),
      .sh_cl_hmc_bvalid  (sh_cl_hmc_bvalid  ),
      .sh_cl_hmc_buser   (sh_cl_hmc_buser   ),
      .cl_sh_hmc_bready  (cl_sh_hmc_bready  ),
      .cl_sh_hmc_arid    (cl_sh_hmc_arid    ),
      .cl_sh_hmc_araddr  (cl_sh_hmc_araddr  ),
      .cl_sh_hmc_arlen   (cl_sh_hmc_arlen   ),
      .cl_sh_hmc_aruser  (cl_sh_hmc_aruser  ),
      .cl_sh_hmc_arvalid (cl_sh_hmc_arvalid ),
      .sh_cl_hmc_arready (sh_cl_hmc_arready ),
      .sh_cl_hmc_rid     (sh_cl_hmc_rid     ),
      .sh_cl_hmc_ruser   (sh_cl_hmc_ruser   ),
      .sh_cl_hmc_rdata   (sh_cl_hmc_rdata   ),
      .sh_cl_hmc_rresp   (sh_cl_hmc_rresp   ),
      .sh_cl_hmc_rlast   (sh_cl_hmc_rlast   ),
      .sh_cl_hmc_rvalid  (sh_cl_hmc_rvalid  ),
      .cl_sh_hmc_rready  (cl_sh_hmc_rready  ),

      .sh_hmc_stat_addr  (sh_hmc_stat_addr_q),
      .sh_hmc_stat_wr    (sh_hmc_stat_wr_q),
      .sh_hmc_stat_rd    (sh_hmc_stat_rd_q),
      .sh_hmc_stat_wdata (sh_hmc_stat_wdata_q),

      .hmc_sh_stat_ack   (hmc_sh_stat_ack_q),
      .hmc_sh_stat_rdata (hmc_sh_stat_rdata_q),
      .hmc_sh_stat_int   (hmc_sh_stat_int_q)
      
      );

`else

   assign hmc_sh_stat_int = 0;
   assign hmc_sh_stat_ack = 1;
   assign hmc_sh_stat_rdata = 0;
   assign hmc_link_up_pipe = ({NUM_HMC{1'b0}});
   assign hmc_iic_scl_o = 0;
   assign hmc_iic_sda_o = 0;
   assign hmc_iic_scl_t = 0;
   assign hmc_iic_sda_t = 0;
   
`endif

//FLR response 

always_ff @(negedge sync_rst_n or posedge clk)
   if (!sync_rst_n)
   begin
      sh_cl_flr_assert_q <= 0;
      cl_sh_flr_done <= 0;
   end
   else
   begin
      sh_cl_flr_assert_q <= sh_cl_flr_assert;
      cl_sh_flr_done <= sh_cl_flr_assert_q && !cl_sh_flr_done;
   end

`ifndef CL_VERSION
   `define CL_VERSION 32'hee_ee_ee_00
`endif  

`ifdef CL_SECOND
   wire[31:0] id0 = 32'h2231_1122;
   wire[31:0] id1 = 32'habcd_1122;
`else
   wire[31:0] id0 = 32'h1d50_6789; 
   wire[31:0] id1 = 32'h1d51_fedc; 
`endif
   
  
`ifdef CL_SECOND
   assign cl_sh_status0 = {20'hb222_2, hmc_scrb_done_pipe[1:0], hmc_link_up_pipe[1:0], all_ddr_scrb_done, all_ddr_is_ready};
   assign cl_sh_status1 = `CL_VERSION + 2;
`else 
//   assign cl_sh_status0 = {20'ha111_1, hmc_scrb_done_pipe[1:0], hmc_link_up_pipe[1:0], all_ddr_scrb_done, all_ddr_is_ready};
   always_ff @(posedge clk)
       cl_sh_status0 <= dbg_scrb_en ? {1'b0, dbg_ddr_scrb_state_pipe[2], 
                                       1'b0, dbg_ddr_scrb_state_pipe[3], 
                                       1'b0, dbg_ddr_scrb_state_pipe[1], 
                                       1'b0, dbg_ddr_scrb_state_pipe[0],
                                       4'd0, hmc_scrb_done_pipe[1:0], hmc_link_up_pipe[1:0], all_ddr_scrb_done, all_ddr_is_ready} :
                        {20'ha111_1, hmc_scrb_done_pipe[1:0], hmc_link_up_pipe[1:0], all_ddr_scrb_done, all_ddr_is_ready};
   assign cl_sh_status1 = `CL_VERSION;
`endif


// assign cl_sh_id0 = 32'h1d50_6789;
// assign cl_sh_id1 = 32'h1d51_fedc;

   always_ff @(posedge clk)
       cl_sh_id0 <= dbg_scrb_en ? (dbg_scrb_mem_sel == 3'd3 ? dbg_ddr_scrb_addr_pipe[2][31:0] :
                                   dbg_scrb_mem_sel == 3'd2 ? dbg_ddr_scrb_addr_pipe[3][31:0] :
                                   dbg_scrb_mem_sel == 3'd1 ? dbg_ddr_scrb_addr_pipe[1][31:0] : dbg_ddr_scrb_addr_pipe[0][31:0]) :
                                    id0; 

   always_ff @(posedge clk)
       cl_sh_id1 <= dbg_scrb_en ? (dbg_scrb_mem_sel == 3'd3 ? dbg_ddr_scrb_addr_pipe[2][63:32] :
                                   dbg_scrb_mem_sel == 3'd2 ? dbg_ddr_scrb_addr_pipe[3][63:32] :
                                   dbg_scrb_mem_sel == 3'd1 ? dbg_ddr_scrb_addr_pipe[1][63:32] : dbg_ddr_scrb_addr_pipe[0][63:32]) :
                                    id1;

   assign cl_sh_status_vled = 16'h1E;

//-----------------------------------------------
// Debug bridge, used if need chipscope
//-----------------------------------------------
`ifndef DISABLE_CHIPSCOPE_DEBUG
/*   ila_0 CL_ILA_0 (
                   .clk    (clk),
                   .probe0 (sh_cl_dma_pcis_awvalid_q),
                   .probe1 (sh_cl_dma_pcis_awaddr_q ),
                   .probe2 (cl_sh_dma_pcis_awready_q),
                   .probe3 (sh_cl_dma_pcis_arvalid_q),
                   .probe4 (sh_cl_dma_pcis_araddr_q ),
                   .probe5 (cl_sh_dma_pcis_arready_q)
                   );


   ila_1 CL_XDMA_ILA_0 (
                   .clk    (clk),
                   .probe0 (sh_cl_xdma_pcis_awvalid_q),
                   .probe1 (sh_cl_xdma_pcis_awaddr_q),
                   .probe2 (2'b0),
                   .probe3 (cl_sh_xdma_pcis_awready_q),
                   .probe4 (sh_cl_xdma_pcis_wvalid_q),
                   .probe5 (sh_cl_xdma_pcis_wstrb_q),
                   .probe6 (sh_cl_xdma_pcis_wlast_q),
                   .probe7 (cl_sh_xdma_pcis_wready_q),
                   .probe8 (1'b0),
                   .probe9 (1'b0),
                   .probe10 (sh_cl_xdma_pcis_wdata_q),
                   .probe11 (1'b0),
                   .probe12 (cl_sh_xdma_pcis_arready_q),
                   .probe13 (2'b0),
                   .probe14 (cl_sh_xdma_pcis_rdata_q),
                   .probe15 (sh_cl_xdma_pcis_araddr_q),
                   .probe16 (sh_cl_xdma_pcis_arvalid_q),
                   .probe17 (3'b0),
                   .probe18 (3'b0),
                   .probe19 (sh_cl_xdma_pcis_awid_q),
                   .probe20 (sh_cl_xdma_pcis_arid_q),
                   .probe21 (sh_cl_xdma_pcis_awlen_q),
                   .probe22 (cl_sh_xdma_pcis_rlast_q),
                   .probe23 (3'b0), 
                   .probe24 (cl_sh_xdma_pcis_rresp_q),
                   .probe25 (cl_sh_xdma_pcis_rid_q),
                   .probe26 (cl_sh_xdma_pcis_rvalid_q),
                   .probe27 (sh_cl_xdma_pcis_arlen_q),
                   .probe28 (3'b0),
                   .probe29 (cl_sh_xdma_pcis_bresp_q),
                   .probe30 (sh_cl_xdma_pcis_rready_q),
                   .probe31 (4'b0),
                   .probe32 (4'b0),
                   .probe33 (4'b0),
                   .probe34 (4'b0),
                   .probe35 (cl_sh_xdma_pcis_bvalid_q),
                   .probe36 (4'b0),
                   .probe37 (4'b0),
                   .probe38 (cl_sh_xdma_pcis_bid_q),
                   .probe39 (sh_cl_xdma_pcis_bready_q),
                   .probe40 (1'b0),
                   .probe41 (1'b0),
                   .probe42 (1'b0),
                   .probe43 (1'b0)
                   );

      ila_1 CL_DDRC_ILA_0 (
                   .clk    (clk),
                   .probe0 (lcl_cl_sh_ddr_awvalid[0]),
                   .probe1 (lcl_cl_sh_ddr_awaddr[0]),
                   .probe2 (2'b0),
                   .probe3 (lcl_sh_cl_ddr_awready[0]),
                   .probe4 (lcl_cl_sh_ddr_wvalid[0]),
                   .probe5 (lcl_cl_sh_ddr_wstrb[0]),
                   .probe6 (lcl_cl_sh_ddr_wlast[0]),
                   .probe7 (lcl_sh_cl_ddr_wready[0]),
                   .probe8 (1'b0),
                   .probe9 (1'b0),
                   .probe10 (lcl_cl_sh_ddr_wdata[0]),
                   .probe11 (1'b0),
                   .probe12 (lcl_sh_cl_ddr_arready[0]),
                   .probe13 (2'b0),
                   .probe14 (lcl_sh_cl_ddr_rdata[0]),
                   .probe15 (lcl_cl_sh_ddr_araddr[0]),
                   .probe16 (lcl_cl_sh_ddr_arvalid[0]),
                   .probe17 (3'b0),
                   .probe18 (3'b0),
                   .probe19 (lcl_cl_sh_ddr_awid[0][4:0]),
                   .probe20 (lcl_cl_sh_ddr_arid[0][4:0]),
                   .probe21 (lcl_cl_sh_ddr_awlen[0]),
                   .probe22 (lcl_sh_cl_ddr_rlast[0]),
                   .probe23 (3'b0), 
                   .probe24 (lcl_sh_cl_ddr_rresp[0]),
                   .probe25 (lcl_sh_cl_ddr_rid[0][4:0]),
                   .probe26 (lcl_sh_cl_ddr_rvalid[0]),
                   .probe27 (lcl_cl_sh_ddr_arlen[0]),
                   .probe28 (3'b0),
                   .probe29 (lcl_sh_cl_ddr_bresp[0]),
                   .probe30 (lcl_cl_sh_ddr_rready[0]),
                   .probe31 (4'b0),
                   .probe32 (4'b0),
                   .probe33 (4'b0),
                   .probe34 (4'b0),
                   .probe35 (lcl_sh_cl_ddr_bvalid[0]),
                   .probe36 (4'b0),
                   .probe37 (4'b0),
                   .probe38 (lcl_sh_cl_ddr_bid[0][4:0]),
                   .probe39 (lcl_cl_sh_ddr_bready[0]),
                   .probe40 (1'b0),
                   .probe41 (1'b0),
                   .probe42 (1'b0),
                   .probe43 (1'b0)
                   );



   cl_debug_bridge CL_DEBUG_BRIDGE (
      .clk(clk),
      .drck(drck),
      .shift(shift),
      .tdi(tdi),
      .update(update),
      .sel(sel),
      .tdo(tdo),
      .tms(tms),
      .tck(tck),
      .runtest(runtest),
      .reset(reset),
      .capture(capture),
      .bscanid(bscanid)
   );
*/
`endif

`ifdef SH_SDA


   axi4_flop_fifo #(.IN_FIFO(1), .ADDR_WIDTH(32), .DATA_WIDTH(32), .ID_WIDTH(1), .A_USER_WIDTH(1), .FIFO_DEPTH(3)) AXIL_SDA_REG_SLC (
    .aclk          (clk),
    .aresetn       (sync_rst_n),
    .sync_rst_n    (1'b1),
    .s_axi_awid    (1'b0),
    .s_axi_awaddr  (sda_cl_awaddr),
    .s_axi_awlen   (8'h0),                                            
    .s_axi_awvalid (sda_cl_awvalid),
    .s_axi_awuser  (1'b0),
    .s_axi_awready (cl_sda_awready),
    .s_axi_wdata   (sda_cl_wdata),
    .s_axi_wstrb   (sda_cl_wstrb),
    .s_axi_wlast   (1'b0),
    .s_axi_wuser   (1'b0),
    .s_axi_wvalid  (sda_cl_wvalid),
    .s_axi_wready  (cl_sda_wready),
    .s_axi_bid     (),
    .s_axi_bresp   (cl_sda_bresp),
    .s_axi_bvalid  (cl_sda_bvalid),
    .s_axi_buser   (),
    .s_axi_bready  (sda_cl_bready),
    .s_axi_arid    (1'b0),
    .s_axi_araddr  (sda_cl_araddr),
    .s_axi_arlen   (8'h0), 
    .s_axi_arvalid (sda_cl_arvalid),
    .s_axi_aruser  (1'd0),
    .s_axi_arready (cl_sda_arready),
    .s_axi_rid     (),
    .s_axi_rdata   (cl_sda_rdata),
    .s_axi_rresp   (cl_sda_rresp),
    .s_axi_rlast   (),
    .s_axi_ruser   (),
    .s_axi_rvalid  (cl_sda_rvalid),
    .s_axi_rready  (sda_cl_rready), 
    .m_axi_awid    (),
    .m_axi_awaddr  (sda_cl_awaddr_q), 
    .m_axi_awlen   (),
    .m_axi_awvalid (sda_cl_awvalid_q),
    .m_axi_awuser  (),
    .m_axi_awready (cl_sda_awready_q),
    .m_axi_wdata   (sda_cl_wdata_q),  
    .m_axi_wstrb   (sda_cl_wstrb_q),
    .m_axi_wvalid  (sda_cl_wvalid_q), 
    .m_axi_wlast   (),
    .m_axi_wuser   (),
    .m_axi_wready  (cl_sda_wready_q), 
    .m_axi_bresp   (cl_sda_bresp_q),  
    .m_axi_bvalid  (cl_sda_bvalid_q), 
    .m_axi_bid     (),
    .m_axi_buser   (1'b0),
    .m_axi_bready  (sda_cl_bready_q), 
    .m_axi_arid    (), 
    .m_axi_araddr  (sda_cl_araddr_q), 
    .m_axi_arlen   (), 
    .m_axi_aruser  (), 
    .m_axi_arvalid (sda_cl_arvalid_q),
    .m_axi_arready (cl_sda_arready_q),
    .m_axi_rid     (),  
    .m_axi_rdata   (cl_sda_rdata_q),  
    .m_axi_rresp   (cl_sda_rresp_q),  
    .m_axi_rlast   (),  
    .m_axi_ruser   (1'b0),
    .m_axi_rvalid  (cl_sda_rvalid_q), 
    .m_axi_rready  (sda_cl_rready_q)
   );

   axi4_flop_fifo #(.IN_FIFO(1), .ADDR_WIDTH(32), .DATA_WIDTH(32), .ID_WIDTH(1), .A_USER_WIDTH(1), .FIFO_DEPTH(3)) AXIL_OCL_REG_SLC (
    .aclk          (clk),
    .aresetn       (sync_rst_n),
    .sync_rst_n    (1'b1),
    .s_axi_awid    (1'b0),
    .s_axi_awaddr  (sh_ocl_awaddr),
    .s_axi_awlen   (8'h00),                                            
    .s_axi_awvalid (sh_ocl_awvalid),
    .s_axi_awuser  (1'b0),
    .s_axi_awready (ocl_sh_awready),
    .s_axi_wdata   (sh_ocl_wdata),
    .s_axi_wstrb   (sh_ocl_wstrb),
    .s_axi_wlast   (1'b0),
    .s_axi_wuser   (1'b0),
    .s_axi_wvalid  (sh_ocl_wvalid),
    .s_axi_wready  (ocl_sh_wready),
    .s_axi_bid     (),
    .s_axi_bresp   (ocl_sh_bresp),
    .s_axi_bvalid  (ocl_sh_bvalid),
    .s_axi_buser   (),
    .s_axi_bready  (sh_ocl_bready),
    .s_axi_arid    (1'h0),
    .s_axi_araddr  (sh_ocl_araddr),
    .s_axi_arlen   (8'h0), 
    .s_axi_arvalid (sh_ocl_arvalid),
    .s_axi_aruser  (1'd0),
    .s_axi_arready (ocl_sh_arready),
    .s_axi_rid     (),
    .s_axi_rdata   (ocl_sh_rdata),
    .s_axi_rresp   (ocl_sh_rresp),
    .s_axi_rlast   (),
    .s_axi_ruser   (),
    .s_axi_rvalid  (ocl_sh_rvalid),
    .s_axi_rready  (sh_ocl_rready), 
    .m_axi_awid    (),
    .m_axi_awaddr  (sh_ocl_awaddr_q), 
    .m_axi_awlen   (),
    .m_axi_awvalid (sh_ocl_awvalid_q),
    .m_axi_awuser  (),
    .m_axi_awready (ocl_sh_awready_q),
    .m_axi_wdata   (sh_ocl_wdata_q),  
    .m_axi_wstrb   (sh_ocl_wstrb_q),
    .m_axi_wvalid  (sh_ocl_wvalid_q), 
    .m_axi_wlast   (),
    .m_axi_wuser   (),
    .m_axi_wready  (ocl_sh_wready_q), 
    .m_axi_bresp   (ocl_sh_bresp_q),  
    .m_axi_bvalid  (ocl_sh_bvalid_q), 
    .m_axi_bid     (),
    .m_axi_buser   (1'b0),
    .m_axi_bready  (sh_ocl_bready_q), 
    .m_axi_arid    (), 
    .m_axi_araddr  (sh_ocl_araddr_q), 
    .m_axi_arlen   (), 
    .m_axi_aruser  (), 
    .m_axi_arvalid (sh_ocl_arvalid_q),
    .m_axi_arready (ocl_sh_arready_q),
    .m_axi_rid     (),  
    .m_axi_rdata   (ocl_sh_rdata_q),  
    .m_axi_rresp   (ocl_sh_rresp_q),  
    .m_axi_rlast   (),  
    .m_axi_ruser   (1'b0),
    .m_axi_rvalid  (ocl_sh_rvalid_q), 
    .m_axi_rready  (sh_ocl_rready_q)
   );

   axi4_flop_fifo #(.IN_FIFO(1), .ADDR_WIDTH(32), .DATA_WIDTH(32), .ID_WIDTH(1), .A_USER_WIDTH(1), .FIFO_DEPTH(3)) AXIL_BAR1_REG_SLC (
    .aclk          (clk),
    .aresetn       (sync_rst_n),
    .sync_rst_n    (1'b1),
    .s_axi_awid    (1'h0),
    .s_axi_awaddr  (sh_bar1_awaddr),
    .s_axi_awlen   (8'h0),                                            
    .s_axi_awvalid (sh_bar1_awvalid),
    .s_axi_awuser  (1'b0),
    .s_axi_awready (bar1_sh_awready),
    .s_axi_wdata   (sh_bar1_wdata),
    .s_axi_wstrb   (sh_bar1_wstrb),
    .s_axi_wlast   (1'h0),
    .s_axi_wuser   (1'b0),
    .s_axi_wvalid  (sh_bar1_wvalid),
    .s_axi_wready  (bar1_sh_wready),
    .s_axi_bid     (),
    .s_axi_bresp   (bar1_sh_bresp),
    .s_axi_bvalid  (bar1_sh_bvalid),
    .s_axi_buser   (),
    .s_axi_bready  (sh_bar1_bready),
    .s_axi_arid    (1'h0),
    .s_axi_araddr  (sh_bar1_araddr),
    .s_axi_arlen   (8'h0), 
    .s_axi_arvalid (sh_bar1_arvalid),
    .s_axi_aruser  (1'd0),
    .s_axi_arready (bar1_sh_arready),
    .s_axi_rid     (),
    .s_axi_rdata   (bar1_sh_rdata),
    .s_axi_rresp   (bar1_sh_rresp),
    .s_axi_rlast   (1'h0),
    .s_axi_ruser   (),
    .s_axi_rvalid  (bar1_sh_rvalid),
    .s_axi_rready  (sh_bar1_rready), 
    .m_axi_awid    (),
    .m_axi_awaddr  (sh_bar1_awaddr_q), 
    .m_axi_awlen   (),
    .m_axi_awvalid (sh_bar1_awvalid_q),
    .m_axi_awuser  (),
    .m_axi_awready (bar1_sh_awready_q),
    .m_axi_wdata   (sh_bar1_wdata_q),  
    .m_axi_wstrb   (sh_bar1_wstrb_q),
    .m_axi_wvalid  (sh_bar1_wvalid_q), 
    .m_axi_wlast   (),
    .m_axi_wuser   (),
    .m_axi_wready  (bar1_sh_wready_q), 
    .m_axi_bresp   (bar1_sh_bresp_q),  
    .m_axi_bvalid  (bar1_sh_bvalid_q), 
    .m_axi_bid     (1'b0),
    .m_axi_buser   (1'b0),
    .m_axi_bready  (sh_bar1_bready_q), 
    .m_axi_arid    (), 
    .m_axi_araddr  (sh_bar1_araddr_q), 
    .m_axi_arlen   (), 
    .m_axi_aruser  (), 
    .m_axi_arvalid (sh_bar1_arvalid_q),
    .m_axi_arready (bar1_sh_arready_q),
    .m_axi_rid     (1'b0),  
    .m_axi_rdata   (bar1_sh_rdata_q),  
    .m_axi_rresp   (bar1_sh_rresp_q),  
    .m_axi_rlast   (),  
    .m_axi_ruser   (1'b0),
    .m_axi_rvalid  (bar1_sh_rvalid_q), 
    .m_axi_rready  (sh_bar1_rready_q)
   );


   axil_slave  AXIL_SLAVE(
      .clk(clk),
      .rst_n(sync_rst_n),
     
      .awvalid(sda_cl_awvalid_q), 
      .awaddr({32'b0, sda_cl_awaddr_q}),
      .awready(cl_sda_awready_q),
      
      .wvalid(sda_cl_wvalid_q),
      .wdata(sda_cl_wdata_q),
      .wstrb(sda_cl_wstrb_q),
      .wready(cl_sda_wready_q),
     
      .bvalid(cl_sda_bvalid_q), 
      .bresp(cl_sda_bresp_q),
      .bready(sda_cl_bready_q),
                   
      .arvalid(sda_cl_arvalid_q),
      .araddr({32'b0, sda_cl_araddr_q}),
      .arready(cl_sda_arready_q),
                    
      .rvalid(cl_sda_rvalid_q),
      .rdata(cl_sda_rdata_q),
      .rresp(cl_sda_rresp_q),
        
      .rready(sda_cl_rready_q)
   );

`ifndef OCL_TG_CTL
   axil_slave  AXIL_SLAVE_OCL(
      .clk(clk),
      .rst_n(sync_rst_n),
     
      .awvalid(sh_ocl_awvalid_q), 
      .awaddr({32'b0, sh_ocl_awaddr_q}),
      .awready(ocl_sh_awready_q),
      
      .wvalid(sh_ocl_wvalid_q),
      .wdata(sh_ocl_wdata_q),
      .wstrb(sh_ocl_wstrb_q),
      .wready(ocl_sh_wready_q),
     
      .bvalid(ocl_sh_bvalid_q), 
      .bresp(ocl_sh_bresp_q),
      .bready(sh_ocl_bready_q),
                   
      .arvalid(sh_ocl_arvalid_q),
      .araddr({32'b0, sh_ocl_araddr_q}),
      .arready(ocl_sh_arready_q),
                    
      .rvalid(ocl_sh_rvalid_q),
      .rdata(ocl_sh_rdata_q),
      .rresp(ocl_sh_rresp_q),
        
      .rready(sh_ocl_rready_q)
   );
`endif

   axil_slave  AXIL_SLAVE_BAR1(
      .clk(clk),
      .rst_n(sync_rst_n),
     
      .awvalid(sh_bar1_awvalid_q), 
      .awaddr({32'b0, sh_bar1_awaddr_q}),
      .awready(bar1_sh_awready_q),
      
      .wvalid(sh_bar1_wvalid_q),
      .wdata(sh_bar1_wdata_q),
      .wstrb(sh_bar1_wstrb_q),
      .wready(bar1_sh_wready_q),
     
      .bvalid(bar1_sh_bvalid_q), 
      .bresp(bar1_sh_bresp_q),
      .bready(sh_bar1_bready_q),
                   
      .arvalid(sh_bar1_arvalid_q),
      .araddr({32'b0, sh_bar1_araddr_q}),
      .arready(bar1_sh_arready_q),
                    
      .rvalid(bar1_sh_rvalid_q),
      .rdata(bar1_sh_rdata_q),
      .rresp(bar1_sh_rresp_q),
        
      .rready(sh_bar1_rready_q)
   );

`endif



   //////////////////////////////////////////////
   // VIO Example - Needs Chipscope
   //////////////////////////////////////////////
`ifndef DISABLE_CHIPSCOPE_DEBUG
   // Counter running at 125MHz
   
   logic      vo_cnt_enable;
   logic      vo_cnt_load;
   logic      vo_cnt_clear;
   logic      vo_cnt_oneshot;
   logic [7:0]  vo_tick_value;
   logic [15:0] vo_cnt_load_value;
   logic [15:0] vo_cnt_watermark;

   logic      vo_cnt_enable_q = 0;
   logic      vo_cnt_load_q = 0;
   logic      vo_cnt_clear_q = 0;
   logic      vo_cnt_oneshot_q = 0;
   logic [7:0]  vo_tick_value_q = 0;
   logic [15:0] vo_cnt_load_value_q = 0;
   logic [15:0] vo_cnt_watermark_q = 0;

   logic        vi_tick;
   logic        vi_cnt_ge_watermark;
   logic [7:0]  vi_tick_cnt = 0;
   logic [15:0] vi_cnt = 0;
   
   // Tick counter and main counter
   always @(posedge clk_extra_a1) begin

      vo_cnt_enable_q     <= vo_cnt_enable    ;
      vo_cnt_load_q       <= vo_cnt_load      ;
      vo_cnt_clear_q      <= vo_cnt_clear     ;
      vo_cnt_oneshot_q    <= vo_cnt_oneshot   ;
      vo_tick_value_q     <= vo_tick_value    ;
      vo_cnt_load_value_q <= vo_cnt_load_value;
      vo_cnt_watermark_q  <= vo_cnt_watermark ;

      vi_tick_cnt = vo_cnt_clear_q ? 0 :
                    ~vo_cnt_enable_q ? vi_tick_cnt :
                    (vi_tick_cnt >= vo_tick_value_q) ? 0 :
                    vi_tick_cnt + 1;

      vi_cnt = vo_cnt_clear_q ? 0 :
               vo_cnt_load_q ? vo_cnt_load_value_q :
               ~vo_cnt_enable_q ? vi_cnt :
               (vi_tick_cnt >= vo_tick_value_q) && (~vo_cnt_oneshot_q || (vi_cnt <= 16'hFFFF)) ? vi_cnt + 1 :
               vi_cnt;

      vi_tick = (vi_tick_cnt >= vo_tick_value_q);

      vi_cnt_ge_watermark = (vi_cnt >= vo_cnt_watermark_q);
      
   end // always @ (posedge clk_extra_a1)
   
/*
   vio_0 CL_VIO_0 (
                   .clk    (clk_extra_a1),
                   .probe_in0  (vi_tick),
                   .probe_in1  (vi_cnt_ge_watermark),
                   .probe_in2  (vi_tick_cnt),
                   .probe_in3  (vi_cnt),
                   .probe_out0 (vo_cnt_enable),
                   .probe_out1 (vo_cnt_load),
                   .probe_out2 (vo_cnt_clear),
                   .probe_out3 (vo_cnt_oneshot),
                   .probe_out4 (vo_tick_value),
                   .probe_out5 (vo_cnt_load_value),
                   .probe_out6 (vo_cnt_watermark)
                   );
   
   ila_vio_counter CL_VIO_ILA (
                   .clk     (clk_extra_a1),
                   .probe0  (vi_tick),
                   .probe1  (vi_cnt_ge_watermark),
                   .probe2  (vi_tick_cnt),
                   .probe3  (vi_cnt),
                   .probe4  (vo_cnt_enable_q),
                   .probe5  (vo_cnt_load_q),
                   .probe6  (vo_cnt_clear_q),
                   .probe7  (vo_cnt_oneshot_q),
                   .probe8  (vo_tick_value_q),
                   .probe9  (vo_cnt_load_value_q),
                   .probe10 (vo_cnt_watermark_q)
                   );
*/   
`endif //  `ifndef DISABLE_CHIPSCOPE_DEBUG

   
endmodule





