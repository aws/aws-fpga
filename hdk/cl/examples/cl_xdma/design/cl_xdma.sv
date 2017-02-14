// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

//`define NO_CL_DDR_TST_AXI4_REG_SLC

module cl_xdma #(parameter NUM_PCIE=1, parameter NUM_DDR=4, parameter NUM_HMC=4, parameter NUM_GTY = 4) 

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
logic[1:0] lcl_sh_cl_ddr_bresp_q[2:0];
logic[2:0] lcl_sh_cl_ddr_bvalid_q;
logic[2:0] lcl_cl_sh_ddr_bready_q;
   
logic[5:0] lcl_cl_sh_ddr_arid_q[2:0];
logic[63:0] lcl_cl_sh_ddr_araddr_q[2:0];
logic[7:0] lcl_cl_sh_ddr_arlen_q[2:0];
logic[2:0] lcl_cl_sh_ddr_arvalid_q;
logic[2:0] lcl_sh_cl_ddr_arready_q;
   
logic[5:0] lcl_sh_cl_ddr_rid_q[2:0];
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
logic[9:0] dummy_lcl_sh_cl_ddr_bid_q[2:0];
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
logic[9:0] dummy_lcl_sh_cl_ddr_rid_q[2:0];
logic[511:0] lcl_sh_cl_ddr_rdata_qq[2:0];
logic[1:0] lcl_sh_cl_ddr_rresp_qq[2:0];
logic[2:0] lcl_sh_cl_ddr_rlast_qq;
logic[2:0] lcl_sh_cl_ddr_rvalid_qq;
logic[2:0] lcl_cl_sh_ddr_rready_qq;

   
logic[2:0] lcl_sh_cl_ddr_is_ready;

logic[3:0] dummy_cl_sh_pcim_arid[NUM_PCIE-1:0]; 
logic dummy_cl_sh_pcim_awid[NUM_PCIE-1:0]; 

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
   
// End internal signals
//-----------------------------

`ifdef SH_SDA
   logic clk, rst_n;
   assign clk = clk_main_a0;
   assign rst_n = rst_main_n;
`endif
   

assign cl_sh_ddr_wid = 0;

   // FOR TIMING PATHS

lib_pipe #(.WIDTH(1), .STAGES(4)) PIPE_RST_N (.clk(clk), .rst_n(1'b1), .in_bus(rst_n), .out_bus(pipe_rst_n));

   
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

   logic [5:0]                 sh_cl_xdma_pcis_awid_q;
   logic [63:0]                sh_cl_xdma_pcis_awaddr_q;
   logic [7:0] sh_cl_xdma_pcis_awlen_q;
   logic         sh_cl_xdma_pcis_awvalid_q;
   logic         cl_sh_xdma_pcis_awready_q;

   logic [511:0]                sh_cl_xdma_pcis_wdata_q;
   logic [63:0]                 sh_cl_xdma_pcis_wstrb_q;
   logic         sh_cl_xdma_pcis_wlast_q;
   logic         sh_cl_xdma_pcis_wvalid_q;
   logic         cl_sh_xdma_pcis_wready_q;

   logic [5:0]                 cl_sh_xdma_pcis_bid_q;
   logic [1:0]                 cl_sh_xdma_pcis_bresp_q;
   logic         cl_sh_xdma_pcis_bvalid_q;
   logic         sh_cl_xdma_pcis_bready_q;

   logic [5:0]                 sh_cl_xdma_pcis_arid_q;
   logic [63:0]                sh_cl_xdma_pcis_araddr_q;
   logic [7:0] sh_cl_xdma_pcis_arlen_q;
   logic         sh_cl_xdma_pcis_arvalid_q;
   logic         cl_sh_xdma_pcis_arready_q;

   logic [511:0]               cl_sh_xdma_pcis_rdata_q;
   logic [5:0]                 cl_sh_xdma_pcis_rid_q;
   logic [1:0]                 cl_sh_xdma_pcis_rresp_q;
   logic         cl_sh_xdma_pcis_rlast_q;
   logic         cl_sh_xdma_pcis_rvalid_q;
   logic         sh_cl_xdma_pcis_rready_q;

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
    .m_axi_buser   (),
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

`else // !`ifndef NO_CL_PCI_AXL_REG_SLC
   
   assign sh_cl_xdma_pcis_awid_q  = sh_cl_dma_pcis_awid ;
   assign sh_cl_xdma_pcis_awaddr_q  = sh_cl_dma_pcis_awaddr ;
   assign sh_cl_xdma_pcis_awvalid_q = sh_cl_dma_pcis_awvalid;
   assign cl_sh_dma_pcis_awready = cl_sh_xdma_pcis_awready_q;
   
   assign sh_cl_xdma_pcis_wdata_q   = sh_cl_dma_pcis_wdata  ;
   assign sh_cl_xdma_pcis_wstrb_q   = sh_cl_dma_pcis_wstrb  ;
   assign sh_cl_xdma_pcis_wvalid_q  = sh_cl_dma_pcis_wvalid ;
   assign cl_sh_dma_pcis_wready  = cl_sh_xdma_pcis_wready_q ;
   
   assign cl_sh_dma_pcis_bid     = cl_sh_xdma_pcis_bid_q    ;
   assign cl_sh_dma_pcis_bresp   = cl_sh_xdma_pcis_bresp_q  ;
   assign cl_sh_dma_pcis_bvalid  = cl_sh_xdma_pcis_bvalid_q ;
   assign sh_cl_xdma_pcis_bready_q  = sh_cl_dma_pcis_bready ;
   
   assign sh_cl_xdma_pcis_arid_q    = sh_cl_dma_pcis_arid ;
   assign sh_cl_xdma_pcis_araddr_q  = sh_cl_dma_pcis_araddr ;
   assign sh_cl_xdma_pcis_arvalid_q = sh_cl_dma_pcis_arvalid;
   assign cl_sh_dma_pcis_arready   = cl_sh_xdma_pcis_arready_q;
   
   assign cl_sh_dma_pcis_rdata   = cl_sh_xdma_pcis_rdata_q  ;
   assign cl_sh_dma_pcis_rid     = cl_sh_xdma_pcis_rid_q  ;
   assign cl_sh_dma_pcis_rresp   = cl_sh_xdma_pcis_rresp_q  ;
   assign cl_sh_dma_pcis_rvalid  = cl_sh_xdma_pcis_rvalid_q ;
   assign cl_sh_dma_pcis_rlast   = cl_sh_xdma_pcis_rlast_q ;
   assign sh_cl_xdma_pcis_rready_q  = sh_cl_dma_pcis_rready ;

`endif // !`ifndef NO_CL_PCI_AXL_REG_SLC

   logic [4:0]                 cl_sh_pcim_awid_q[NUM_PCIE-1:0];
   logic [63:0]                cl_sh_pcim_awaddr_q[NUM_PCIE-1:0];
   logic [7:0]                 cl_sh_pcim_awlen_q[NUM_PCIE-1:0];
   logic [18:0]                cl_sh_pcim_awuser_q[NUM_PCIE-1:0]; //DW length of transfer
   logic [NUM_PCIE-1:0]        cl_sh_pcim_awvalid_q;
   logic [NUM_PCIE-1:0]        sh_cl_pcim_awready_q;

   //   logic [4:0]                 cl_sh_pcim_wid_q[NUM_PCIE-1:0];
   logic [511:0]               cl_sh_pcim_wdata_q[NUM_PCIE-1:0];
   logic [63:0]                cl_sh_pcim_wstrb_q[NUM_PCIE-1:0];
   logic [NUM_PCIE-1:0]        cl_sh_pcim_wlast_q;
   logic [NUM_PCIE-1:0]        cl_sh_pcim_wvalid_q;
   logic [NUM_PCIE-1:0]        sh_cl_pcim_wready_q;

   logic [4:0]                 sh_cl_pcim_bid_q[NUM_PCIE-1:0];
   logic [10:0]                dummy_sh_cl_pcim_bid_q[NUM_PCIE-1:0];
   logic [1:0]                 sh_cl_pcim_bresp_q[NUM_PCIE-1:0];
   logic [NUM_PCIE-1:0]        sh_cl_pcim_bvalid_q;
   logic [NUM_PCIE-1:0]        cl_sh_pcim_bready_q;

   logic [4:0]                 cl_sh_pcim_arid_q[NUM_PCIE-1:0];
   logic [63:0]                cl_sh_pcim_araddr_q[NUM_PCIE-1:0];
   logic [7:0]                 cl_sh_pcim_arlen_q[NUM_PCIE-1:0];
   logic [18:0]                cl_sh_pcim_aruser_q[NUM_PCIE-1:0]; //DW length of transfer
   logic [NUM_PCIE-1:0]        cl_sh_pcim_arvalid_q;
   logic [NUM_PCIE-1:0]        sh_cl_pcim_arready_q;

   logic [4:0]                 sh_cl_pcim_rid_q[NUM_PCIE-1:0];
   logic [10:0]                dummy_sh_cl_pcim_rid_q[NUM_PCIE-1:0];
   logic [511:0]               sh_cl_pcim_rdata_q[NUM_PCIE-1:0];
   logic [1:0]                 sh_cl_pcim_rresp_q[NUM_PCIE-1:0];
   logic [NUM_PCIE-1:0]        sh_cl_pcim_rlast_q;
   logic [NUM_PCIE-1:0]        sh_cl_pcim_rvalid_q;
   logic [NUM_PCIE-1:0]        cl_sh_pcim_rready_q;

`ifndef NO_CL_PCI_AXI4_REG_SLC
   
   // AXI4 register slice - For signals between CL and HL
   axi4_flop_fifo #(.ADDR_WIDTH(64), .DATA_WIDTH(512), .ID_WIDTH(16), .A_USER_WIDTH(19), .FIFO_DEPTH(3)) PCI_AXI4_REG_SLC (
     .aclk           (clk),
     .aresetn        (sync_rst_n),
     .sync_rst_n     (1'b1),
                                                                                                                         
     .s_axi_awid     ({11'b0, cl_sh_pcim_awid_q[0]}),
     .s_axi_awaddr   (cl_sh_pcim_awaddr_q[0]),
     .s_axi_awlen    (cl_sh_pcim_awlen_q[0]),
     .s_axi_awuser   (cl_sh_pcim_awuser_q[0]),
     .s_axi_awvalid  (cl_sh_pcim_awvalid_q[0]),
     .s_axi_awready  (sh_cl_pcim_awready_q[0]),
     .s_axi_wdata    (cl_sh_pcim_wdata_q[0]),
     .s_axi_wstrb    (cl_sh_pcim_wstrb_q[0]),
     .s_axi_wlast    (cl_sh_pcim_wlast_q[0]),
     .s_axi_wuser    (),
     .s_axi_wvalid   (cl_sh_pcim_wvalid_q[0]),
     .s_axi_wready   (sh_cl_pcim_wready_q[0]),
     .s_axi_bid      ({dummy_sh_cl_pcim_bid_q[0], sh_cl_pcim_bid_q[0]}),
     .s_axi_bresp    (sh_cl_pcim_bresp_q[0]),
     .s_axi_buser    (),
     .s_axi_bvalid   (sh_cl_pcim_bvalid_q[0]),
     .s_axi_bready   (cl_sh_pcim_bready_q[0]),
     .s_axi_arid     ({11'b0, cl_sh_pcim_arid_q[0]}),
     .s_axi_araddr   (cl_sh_pcim_araddr_q[0]),
     .s_axi_arlen    (cl_sh_pcim_arlen_q[0]),
     .s_axi_aruser   (cl_sh_pcim_aruser_q[0]),
     .s_axi_arvalid  (cl_sh_pcim_arvalid_q[0]),
     .s_axi_arready  (sh_cl_pcim_arready_q[0]),
     .s_axi_rid      ({dummy_sh_cl_pcim_rid_q[0], sh_cl_pcim_rid_q[0]}),
     .s_axi_rdata    (sh_cl_pcim_rdata_q[0]),
     .s_axi_rresp    (sh_cl_pcim_rresp_q[0]),
     .s_axi_rlast    (sh_cl_pcim_rlast_q[0]),
     .s_axi_ruser    (),
     .s_axi_rvalid   (sh_cl_pcim_rvalid_q[0]),
     .s_axi_rready   (cl_sh_pcim_rready_q[0]),  
     .m_axi_awid     (cl_sh_pcim_awid[0]),   
     .m_axi_awaddr   (cl_sh_pcim_awaddr[0]), 
     .m_axi_awlen    (cl_sh_pcim_awlen[0]),  
     .m_axi_awuser   (cl_sh_pcim_awuser[0]), 
     .m_axi_awvalid  (cl_sh_pcim_awvalid[0]),
     .m_axi_awready  (sh_cl_pcim_awready[0]),
     .m_axi_wdata    (cl_sh_pcim_wdata[0]),  
     .m_axi_wstrb    (cl_sh_pcim_wstrb[0]),  
     .m_axi_wlast    (cl_sh_pcim_wlast[0]),  
     .m_axi_wuser    (),
     .m_axi_wvalid   (cl_sh_pcim_wvalid[0]), 
     .m_axi_wready   (sh_cl_pcim_wready[0]), 
     .m_axi_bid      (sh_cl_pcim_bid[0]),    
     .m_axi_bresp    (sh_cl_pcim_bresp[0]),  
     .m_axi_bvalid   (sh_cl_pcim_bvalid[0]), 
     .m_axi_buser    (),
     .m_axi_bready   (cl_sh_pcim_bready[0]), 
     .m_axi_arid     (cl_sh_pcim_arid[0]),   
     .m_axi_araddr   (cl_sh_pcim_araddr[0]), 
     .m_axi_arlen    (cl_sh_pcim_arlen[0]),  
     .m_axi_aruser   (cl_sh_pcim_aruser[0]), 
     .m_axi_arvalid  (cl_sh_pcim_arvalid[0]),
     .m_axi_arready  (sh_cl_pcim_arready[0]),
     .m_axi_rid      (sh_cl_pcim_rid[0]),    
     .m_axi_rdata    (sh_cl_pcim_rdata[0]),  
     .m_axi_rresp    (sh_cl_pcim_rresp[0]),  
     .m_axi_rlast    (sh_cl_pcim_rlast[0]),  
     .m_axi_rvalid   (sh_cl_pcim_rvalid[0]), 
     .m_axi_ruser    (),
     .m_axi_rready   (cl_sh_pcim_rready[0])
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

`ifndef NO_CL_DDR_TST_3_AXI4_REG_SLC
   
   // AXI4 register slice - For signals between CL and HL
   axi4_flop_fifo #(.ADDR_WIDTH(64), .DATA_WIDTH(512), .ID_WIDTH(16), .A_USER_WIDTH(1), .FIFO_DEPTH(3)) DDR_TST_3_AXI4_REG_SLC (
     .aclk           (clk),
     .aresetn        (sync_rst_n),
     .sync_rst_n     (1'b1),
                                                                                                                                
     .s_axi_awid     ({10'b0, cl_sh_ddr_awid_q}),
     .s_axi_awaddr   ({cl_sh_ddr_awaddr_q[63:30], 2'b0, cl_sh_ddr_awaddr_q[27:0]}),
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
     .s_axi_bid      ({dummy_sh_cl_ddr_bid_q, sh_cl_ddr_bid_q}),
     .s_axi_bresp    (sh_cl_ddr_bresp_q),
     .s_axi_bvalid   (sh_cl_ddr_bvalid_q),
     .s_axi_buser    (),
     .s_axi_bready   (cl_sh_ddr_bready_q),
     .s_axi_arid     ({10'b0, cl_sh_ddr_arid_q}),
     .s_axi_araddr   ({cl_sh_ddr_araddr_q[63:30], 2'b0, cl_sh_ddr_araddr_q[27:0]}),
     .s_axi_arlen    (cl_sh_ddr_arlen_q),
     .s_axi_aruser   (1'b0),
     .s_axi_arvalid  (cl_sh_ddr_arvalid_q),
     .s_axi_arready  (sh_cl_ddr_arready_q),
     .s_axi_rid      ({dummy_sh_cl_ddr_rid_q, sh_cl_ddr_rid_q}),
     .s_axi_rdata    (sh_cl_ddr_rdata_q),
     .s_axi_rresp    (sh_cl_ddr_rresp_q),
     .s_axi_rlast    (sh_cl_ddr_rlast_q),
     .s_axi_ruser    (),
     .s_axi_rvalid   (sh_cl_ddr_rvalid_q),
     .s_axi_rready   (cl_sh_ddr_rready_q),  
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
     .m_axi_bid      ({10'b0, sh_cl_ddr_bid[5:0]}),    
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
     .m_axi_rid      ({10'b0, sh_cl_ddr_rid[5:0]}),    
     .m_axi_rdata    (sh_cl_ddr_rdata),  
     .m_axi_rresp    (sh_cl_ddr_rresp),  
     .m_axi_ruser    (),
     .m_axi_rlast    (sh_cl_ddr_rlast),  
     .m_axi_rvalid   (sh_cl_ddr_rvalid), 
     .m_axi_rready   (cl_sh_ddr_rready)
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
assign slv_wr_req = sh_cl_pcis_awvalid;

assign slv_mx_rsp_ready = (slv_cyc_wr)? sh_cl_pcis_bready: sh_cl_pcis_rready;

assign slv_mx_req_valid = (slv_cyc_wr)?   sh_cl_pcis_wvalid:
                                          1'b1;


//Fixed write hi-pri
assign slv_arb_wr = slv_wr_req;

   logic [63:0] slv_req_rd_addr;
   logic [63:0] slv_req_wr_addr;
   logic [5:0]  slv_req_rd_id;
   logic [5:0]  slv_req_wr_id;
   
always_ff @(negedge sync_rst_n or posedge clk)
  if (!sync_rst_n)
    {slv_req_rd_addr, slv_req_wr_addr} <= 128'd0;
  else if ((slv_state == SLV_IDLE) && (sh_cl_pcis_arvalid || sh_cl_pcis_awvalid))
    {slv_req_rd_addr, slv_req_wr_addr} <= {sh_cl_pcis_araddr, sh_cl_pcis_awaddr};
   
always_ff @(negedge sync_rst_n or posedge clk)
  if (!sync_rst_n)
    {slv_req_rd_id, slv_req_wr_id} <= 0;
  else if ((slv_state == SLV_IDLE) && (sh_cl_pcis_arvalid || sh_cl_pcis_awvalid))
    {slv_req_rd_id, slv_req_wr_id} <= {sh_cl_pcis_arid, sh_cl_pcis_awid};
   
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
   case (slv_state)

      SLV_IDLE:
      begin
         if (slv_wr_req)
            slv_state_nxt = SLV_WR_ADDR;
         else if (sh_cl_pcis_arvalid)
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

//State machine flops
always_ff @(negedge sync_rst_n or posedge clk)
   if (!sync_rst_n)
      slv_state <= SLV_IDLE;
   else
      slv_state <= slv_state_nxt;


//Cycle to TST blocks -- Repliacte for timing
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

/*
always_comb
begin
   for (int i=1; i<NUM_PCIE; i++)
   begin
      cl_sh_pcis_bresp[i] = 0;
      cl_sh_pcis_bvalid[i] = 0;

      cl_sh_pcis_rdata[i] = 0;
      cl_sh_pcis_rresp[i] = 0;
      cl_sh_pcis_rvalid[i] = 0;
   end
end
*/

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
genvar gp;
generate
   for (gp=0; gp<NUM_PCIE; gp++)
   begin: gen_pci_tst 

`ifdef PCI_ATG_CFG_PIPE_ENABLE
      lib_pipe #(.WIDTH(32+32+1+1), .STAGES(NUM_CFG_STGS_PCIE_ATG)) PIPE_SLV_REQ_PCIE (.clk (clk), 
                                                                  .rst_n (sync_rst_n), 
                                                                  .in_bus({slv_tst_addr[gp], slv_tst_wdata[gp], slv_tst_wr[gp], slv_tst_rd[gp]}),
                                                                  .out_bus({slv_tst_addr_pipe[gp], slv_tst_wdata_pipe[gp], slv_tst_wr_pipe[gp], slv_tst_rd_pipe[gp]})
                                                                   );
      
      lib_pipe #(.WIDTH(32+1), .STAGES(NUM_CFG_STGS_PCIE_ATG)) PIPE_SLV_ACK_PCIE (.clk (clk), 
                                                              .rst_n (sync_rst_n), 
                                                              .in_bus({tst_slv_ack[gp], tst_slv_rdata[gp]}),
                                                              .out_bus({tst_slv_ack_pipe[gp], tst_slv_rdata_pipe[gp]})
                                                              );
`else // !`ifdef PCI_ATG_CFG_PIPE_ENABLE
      
   assign slv_tst_addr_pipe[gp] = slv_tst_addr[gp];
   assign slv_tst_wdata_pipe[gp] = slv_tst_wdata[gp];
   assign slv_tst_wr_pipe[gp] = slv_tst_wr[gp];
   assign slv_tst_rd_pipe[gp] = slv_tst_rd[gp];
   assign tst_slv_ack_pipe[gp] = tst_slv_ack[gp];
   assign tst_slv_rdata_pipe[gp] = tst_slv_rdata[gp];
`endif // !`ifdef PCI_ATG_CFG_PIPE_ENABLE
      
   // First BE
   assign cl_sh_pcim_awuser_q[0][14:11] = 4'hf;
   assign cl_sh_pcim_aruser_q[0][14:11] = 4'hf;

   // Last BE
   assign cl_sh_pcim_awuser_q[0][18:15] = cl_sh_pcim_awuser_q[0][10:0] == 11'd1 ? 4'h0 : 4'hf;
   assign cl_sh_pcim_aruser_q[0][18:15] = cl_sh_pcim_aruser_q[0][10:0] == 11'd1 ? 4'h0 : 4'hf;
   
      cl_tst #(.DATA_WIDTH(512)) CL_TST_PCI (
   
         .clk(clk),
         .rst_n(sync_rst_n),

         .cfg_addr(slv_tst_addr_pipe[gp]),
         .cfg_wdata(slv_tst_wdata_pipe[gp]),
         .cfg_wr(slv_tst_wr_pipe[gp]),
         .cfg_rd(slv_tst_rd_pipe[gp]),
         .tst_cfg_ack(tst_slv_ack[gp]),
         .tst_cfg_rdata(tst_slv_rdata[gp]),

         .atg_enable(),
  
         .awid({dummy_cl_sh_pcim_awid[gp], cl_sh_pcim_awid_q[gp]}),
         .awaddr(cl_sh_pcim_awaddr_q[gp]), 
         .awlen(cl_sh_pcim_awlen_q[gp]),
         .awvalid(cl_sh_pcim_awvalid_q[gp]),
         .awuser(cl_sh_pcim_awuser_q[gp][10:0]),
         .awready(sh_cl_pcim_awready_q[gp]),

         //.wid(cl_sh_pcim_wid_q[gp]),
         .wid(),
         .wdata(cl_sh_pcim_wdata_q[gp]),
         .wstrb(cl_sh_pcim_wstrb_q[gp]),
         .wlast(cl_sh_pcim_wlast_q[gp]),
         .wvalid(cl_sh_pcim_wvalid_q[gp]),
         .wready(sh_cl_pcim_wready_q[gp]),

         .bid({1'd0, sh_cl_pcim_bid_q[gp]}),
         .bresp(sh_cl_pcim_bresp_q[gp]),
         .bvalid(sh_cl_pcim_bvalid_q[gp]),
         .buser(18'h0),
         .bready(cl_sh_pcim_bready_q[gp]),

         .arid({dummy_cl_sh_pcim_arid[gp], cl_sh_pcim_arid_q[gp]}),
         .araddr(cl_sh_pcim_araddr_q[gp]),
         .arlen(cl_sh_pcim_arlen_q[gp]),
         .aruser(cl_sh_pcim_aruser_q[gp][10:0]),
         .arvalid(cl_sh_pcim_arvalid_q[gp]),
         .arready(sh_cl_pcim_arready_q[gp]),

         .rid({4'h0, sh_cl_pcim_rid_q[gp]}),
         .rdata(sh_cl_pcim_rdata_q[gp]),
         .rresp(sh_cl_pcim_rresp_q[gp]),
         .rlast(sh_cl_pcim_rlast_q[gp]),
         .ruser(18'h0),
         .rvalid(sh_cl_pcim_rvalid_q[gp]),
         .rready(cl_sh_pcim_rready_q[gp])
      );
   end
endgenerate

   assign ddr_slv_tst_addr = {slv_tst_addr[3], slv_tst_addr[4], slv_tst_addr[2], slv_tst_addr[1]};
   assign ddr_slv_tst_wdata = {slv_tst_wdata[3], slv_tst_wdata[4], slv_tst_wdata[2], slv_tst_wdata[1]};
   assign ddr_slv_tst_wr = {slv_tst_wr[3], slv_tst_wr[4], slv_tst_wr[2], slv_tst_wr[1]};
   assign ddr_slv_tst_rd = {slv_tst_rd[3], slv_tst_rd[4], slv_tst_rd[2], slv_tst_rd[1]};
   assign {tst_slv_ack_pipe[3], tst_slv_ack_pipe[4], tst_slv_ack_pipe[2], tst_slv_ack_pipe[1]} = ddr_tst_slv_ack_pipe;
   assign {tst_slv_rdata_pipe[3], tst_slv_rdata_pipe[4], tst_slv_rdata_pipe[2], tst_slv_rdata_pipe[1]} = {ddr_tst_slv_rdata_pipe[3], ddr_tst_slv_rdata_pipe[2], ddr_tst_slv_rdata_pipe[1], ddr_tst_slv_rdata_pipe[0]};
   
`ifndef NO_CL_DDR
//DDR
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

      lib_pipe #(.WIDTH(1+1+8+32), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_DDR_STAT (.clk(clk), .rst_n(sync_rst_n),
                                                               .in_bus({sh_ddr_stat_wr[gd], sh_ddr_stat_rd[gd], sh_ddr_stat_addr[gd], sh_ddr_stat_wdata[gd]}),
                                                               .out_bus({sh_ddr_stat_wr_q[gd], sh_ddr_stat_rd_q[gd], sh_ddr_stat_addr_q[gd], sh_ddr_stat_wdata_q[gd]})
                                                               );


      lib_pipe #(.WIDTH(1+8+32), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_DDR_STAT_ACK (.clk(clk), .rst_n(sync_rst_n),
                                                               .in_bus({ddr_sh_stat_ack_q[gd], ddr_sh_stat_int_q[gd], ddr_sh_stat_rdata_q[gd]}),
                                                               .out_bus({ddr_sh_stat_ack[gd], ddr_sh_stat_int[gd], ddr_sh_stat_rdata[gd]})
                                                               );

      lib_pipe #(.WIDTH(2+3+64), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_SCRB_DDR (.clk(clk), .rst_n(sync_rst_n),
                                                                             .in_bus({ddr_scrb_en[gd], ddr_scrb_done[gd], dbg_ddr_scrb_state[gd], dbg_ddr_scrb_addr[gd]}),
                                                                             .out_bus({ddr_scrb_en_pipe[gd], ddr_scrb_done_pipe[gd], dbg_ddr_scrb_state_pipe[gd], dbg_ddr_scrb_addr_pipe[gd]})
                                                                             );
/*      
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
   
         .awid(lcl_cl_sh_ddr_awid_q[gd]),
         .awaddr(lcl_cl_sh_ddr_awaddr_q[gd]), 
         .awlen(lcl_cl_sh_ddr_awlen_q[gd]),
         .awvalid(lcl_cl_sh_ddr_awvalid_q[gd]),
         .awuser(),
         .awready(lcl_sh_cl_ddr_awready_q[gd]),

         .wid(lcl_cl_sh_ddr_wid_q[gd]),
         .wdata(lcl_cl_sh_ddr_wdata_q[gd]),
         .wstrb(lcl_cl_sh_ddr_wstrb_q[gd]),
         .wlast(lcl_cl_sh_ddr_wlast_q[gd]),
         .wvalid(lcl_cl_sh_ddr_wvalid_q[gd]),
         .wready(lcl_sh_cl_ddr_wready_q[gd]),

         .bid(lcl_sh_cl_ddr_bid_q[gd]),
         .bresp(lcl_sh_cl_ddr_bresp_q[gd]),
         .buser(18'h0),
         .bvalid(lcl_sh_cl_ddr_bvalid_q[gd]),
         .bready(lcl_cl_sh_ddr_bready_q[gd]),

         .arid({dummy_lcl_cl_sh_ddr_arid[gd], lcl_cl_sh_ddr_arid_q[gd]}),
         .araddr(lcl_cl_sh_ddr_araddr_q[gd]),
         .arlen(lcl_cl_sh_ddr_arlen_q[gd]),
         .arvalid(lcl_cl_sh_ddr_arvalid_q[gd]),
         .aruser(),
         .arready(lcl_sh_cl_ddr_arready_q[gd]),

         .rid({3'h0, lcl_sh_cl_ddr_rid_q[gd]}),
         .rdata(lcl_sh_cl_ddr_rdata_q[gd]),
         .rresp(lcl_sh_cl_ddr_rresp_q[gd]),
         .rlast(lcl_sh_cl_ddr_rlast_q[gd]),
         .ruser(18'h0),
         .rvalid(lcl_sh_cl_ddr_rvalid_q[gd]),
         .rready(lcl_cl_sh_ddr_rready_q[gd]),

         .scrb_enable(ddr_scrb_en_pipe[gd]),
         .scrb_done  (ddr_scrb_done[gd]),

         .scrb_dbg_state(dbg_ddr_scrb_state[gd]),
         .scrb_dbg_addr (dbg_ddr_scrb_addr[gd])
      );
*/
      assign ddr_tst_slv_ack[gd] = 1'b0;
      assign ddr_tst_slv_rdata[gd] = 32'b0;
      assign dbg_ddr_scrb_state[gd] = 3'b0;
      assign dbg_ddr_scrb_addr[gd] = 64'b0;

`ifndef NO_CL_DDR_TST_AXI4_REG_SLC
   if ((gd==0) && SH_DDR_A_PRESENT)    //DDR_A is in SH
   begin
     // AXI4 register slice - For signals between CL and HL
      axi4_flop_fifo #(.ADDR_WIDTH(64), .DATA_WIDTH(512), .ID_WIDTH(16), .A_USER_WIDTH(1), .FIFO_DEPTH(3)) DDR_A_CL_TST_AXI4_REG_SLC (
       .aclk           (clk),
       .aresetn        (sync_rst_n),
       .sync_rst_n     (1'b1),
       .s_axi_awid     ({10'b0, lcl_cl_sh_ddr_awid_q[gd]}),
       .s_axi_awaddr   ({lcl_cl_sh_ddr_awaddr_q[gd][63:22], 2'b0, lcl_cl_sh_ddr_awaddr_q[gd][19:0]}),
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
       .s_axi_araddr   ({lcl_cl_sh_ddr_araddr_q[gd][63:22], 2'b0, lcl_cl_sh_ddr_araddr_q[gd][19:0]}),
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
       .s_axi_awaddr   ({lcl_cl_sh_ddr_awaddr_q[gd][63:30], 2'b0, lcl_cl_sh_ddr_awaddr_q[gd][27:0]}),
       .s_axi_awlen    (lcl_cl_sh_ddr_awlen_q[gd]),
       .s_axi_awsize   (3'h110),
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
       .s_axi_araddr   ({lcl_cl_sh_ddr_araddr_q[gd][63:30], 2'b0, lcl_cl_sh_ddr_araddr_q[gd][27:0]}),
       .s_axi_arlen    (lcl_cl_sh_ddr_arlen_q[gd]),
       .s_axi_arsize   (3'h110),
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
       .s_axi_awsize   (3'h110),
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
       .s_axi_arsize   (3'h110),
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
       .m_axi_awid     (lcl_cl_sh_ddr_awid[gd]),   
       .m_axi_awaddr   (lcl_cl_sh_ddr_awaddr[gd]), 
       .m_axi_awlen    (lcl_cl_sh_ddr_awlen[gd]),  
       .m_axi_awvalid  (lcl_cl_sh_ddr_awvalid[gd]),
       .m_axi_awready  (lcl_sh_cl_ddr_awready[gd]),
       .m_axi_wdata    (lcl_cl_sh_ddr_wdata[gd]),  
       .m_axi_wstrb    (lcl_cl_sh_ddr_wstrb[gd]),  
       .m_axi_wlast    (lcl_cl_sh_ddr_wlast[gd]),  
       .m_axi_wvalid   (lcl_cl_sh_ddr_wvalid[gd]), 
       .m_axi_wready   (lcl_sh_cl_ddr_wready[gd]), 
       .m_axi_bid      (lcl_sh_cl_ddr_bid[gd]),    
       .m_axi_bresp    (lcl_sh_cl_ddr_bresp[gd]),  
       .m_axi_bvalid   (lcl_sh_cl_ddr_bvalid[gd]), 
       .m_axi_bready   (lcl_cl_sh_ddr_bready[gd]), 
       .m_axi_arid     (lcl_cl_sh_ddr_arid[gd]),   
       .m_axi_araddr   (lcl_cl_sh_ddr_araddr[gd]), 
       .m_axi_arlen    (lcl_cl_sh_ddr_arlen[gd]),  
       .m_axi_arvalid  (lcl_cl_sh_ddr_arvalid[gd]),
       .m_axi_arready  (lcl_sh_cl_ddr_arready[gd]),
       .m_axi_rid      (lcl_sh_cl_ddr_rid[gd]),    
       .m_axi_rdata    (lcl_sh_cl_ddr_rdata[gd]),  
       .m_axi_rresp    (lcl_sh_cl_ddr_rresp[gd]),  
       .m_axi_rlast    (lcl_sh_cl_ddr_rlast[gd]),  
       .m_axi_rvalid   (lcl_sh_cl_ddr_rvalid[gd]), 
       .m_axi_rready   (lcl_cl_sh_ddr_rready[gd])
       );
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

   assign lcl_cl_sh_ddr_awid[gd]  = {10'b0, lcl_cl_sh_ddr_awid_q[gd]} ;
   assign lcl_cl_sh_ddr_awaddr[gd]  = lcl_cl_sh_ddr_awaddr_q[gd] ;
   assign lcl_cl_sh_ddr_awlen[gd]  = lcl_cl_sh_ddr_awlen_q[gd] ;
   assign lcl_cl_sh_ddr_awvalid[gd] = lcl_cl_sh_ddr_awvalid_q[gd];
   assign lcl_sh_cl_ddr_awready_q[gd] = lcl_sh_cl_ddr_awready[gd];
   
   assign lcl_cl_sh_ddr_wdata[gd]   = lcl_cl_sh_ddr_wdata_q[gd]  ;
   assign lcl_cl_sh_ddr_wstrb[gd]   = lcl_cl_sh_ddr_wstrb_q[gd]  ;
   assign lcl_cl_sh_ddr_wlast[gd]   = lcl_cl_sh_ddr_wlast_q[gd]  ;
   assign lcl_cl_sh_ddr_wvalid[gd]  = lcl_cl_sh_ddr_wvalid_q[gd] ;
   assign lcl_sh_cl_ddr_wready_q[gd]  = lcl_sh_cl_ddr_wready[gd] ;
   
   assign {dummy_lcl_sh_cl_ddr_bid_q[gd], lcl_sh_cl_ddr_bid_q[gd]}   = lcl_sh_cl_ddr_bid[gd]  ;
   assign lcl_sh_cl_ddr_bresp_q[gd]   = lcl_sh_cl_ddr_bresp[gd]  ;
   assign lcl_sh_cl_ddr_bvalid_q[gd]  = lcl_sh_cl_ddr_bvalid[gd] ;
   assign lcl_cl_sh_ddr_bready[gd]  = lcl_cl_sh_ddr_bready_q[gd] ;
   
   assign lcl_cl_sh_ddr_arid[gd]  = {10'b0, lcl_cl_sh_ddr_arid_q[gd]} ;
   assign lcl_cl_sh_ddr_araddr[gd]  = lcl_cl_sh_ddr_araddr_q[gd] ;
   assign lcl_cl_sh_ddr_arlen[gd]  = lcl_cl_sh_ddr_arlen_q[gd] ;
   assign lcl_cl_sh_ddr_arvalid[gd] = lcl_cl_sh_ddr_arvalid_q[gd];
   assign lcl_sh_cl_ddr_arready_q[gd] = lcl_sh_cl_ddr_arready[gd];
   
   assign {dummy_lcl_sh_cl_ddr_rid_q[gd], lcl_sh_cl_ddr_rid_q[gd]}   = lcl_sh_cl_ddr_rid[gd]  ;
   assign lcl_sh_cl_ddr_rdata_q[gd]   = lcl_sh_cl_ddr_rdata[gd]  ;
   assign lcl_sh_cl_ddr_rresp_q[gd]   = lcl_sh_cl_ddr_rresp[gd]  ;
   assign lcl_sh_cl_ddr_rlast_q[gd]   = lcl_sh_cl_ddr_rlast[gd]  ;
   assign lcl_sh_cl_ddr_rvalid_q[gd]  = lcl_sh_cl_ddr_rvalid[gd] ;
   assign lcl_cl_sh_ddr_rready[gd]  = lcl_cl_sh_ddr_rready_q[gd] ;
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

/*   
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
                                               
         .awid(cl_sh_ddr_awid_q),
         .awaddr(cl_sh_ddr_awaddr_q), 
         .awlen(cl_sh_ddr_awlen_q),
         .awvalid(cl_sh_ddr_awvalid_q),
         .awuser(),
         .awready(sh_cl_ddr_awready_q),

         //.wid(cl_sh_ddr_wid_q),
         .wid(),
         .wdata(cl_sh_ddr_wdata_q),
         .wstrb(cl_sh_ddr_wstrb_q),
         .wlast(cl_sh_ddr_wlast_q),
         .wvalid(cl_sh_ddr_wvalid_q),
         .wready(sh_cl_ddr_wready_q),

         .bid(sh_cl_ddr_bid_q),
         .bresp(sh_cl_ddr_bresp_q),
         .buser(18'h0),
         .bvalid(sh_cl_ddr_bvalid_q),
         .bready(cl_sh_ddr_bready_q),

         .arid({dummy_cl_sh_ddr_arid, cl_sh_ddr_arid_q}),
         .araddr(cl_sh_ddr_araddr_q),
         .arlen(cl_sh_ddr_arlen_q),
         .arvalid(cl_sh_ddr_arvalid_q),
         .aruser(),
         .arready(sh_cl_ddr_arready_q),

         .rid({3'h0, sh_cl_ddr_rid_q}),
         .rdata(sh_cl_ddr_rdata_q),
         .rresp(sh_cl_ddr_rresp_q),
         .rlast(sh_cl_ddr_rlast_q),
         .ruser(18'h0),
         .rvalid(sh_cl_ddr_rvalid_q),
         .rready(cl_sh_ddr_rready_q),

         .scrb_enable(ddr_scrb_en_pipe[3]),
         .scrb_done  (ddr_scrb_done[3]),

         .scrb_dbg_state(dbg_ddr_scrb_state[3]),
         .scrb_dbg_addr (dbg_ddr_scrb_addr[3])
      );
*/
      assign ddr_tst_slv_ack[3] = 1'b0;
      assign ddr_tst_slv_rdata[3] = 32'b0;
      assign dbg_ddr_scrb_state[3] = 3'b0;
      assign dbg_ddr_scrb_addr[3] = 64'b0;

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


   //removing XDCFG - sundeepa
   assign tst_slv_ack[1+4+4+4+1] = 0;
   assign tst_slv_rdata[1+4+4+4+1] = 0; 
   
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

   lib_pipe #(.WIDTH(32+32+1+1), .STAGES(NUM_CFG_STGS_XDMA)) PIPE_SLV_REQ_XDMA (.clk (clk), 
                                                                                .rst_n (sync_rst_n), 
                                                                                .in_bus({slv_tst_addr[1+4+4+4+1+1], slv_tst_wdata[1+4+4+4+1+1], slv_tst_wr[1+4+4+4+1+1], slv_tst_rd[1+4+4+4+1+1]}),
                                                                                .out_bus({slv_tst_addr_pipe[1+4+4+4+1+1], slv_tst_wdata_pipe[1+4+4+4+1+1], slv_tst_wr_pipe[1+4+4+4+1+1], slv_tst_rd_pipe[1+4+4+4+1+1]})
                                                                                );
   
   lib_pipe #(.WIDTH(32+1), .STAGES(NUM_CFG_STGS_XDMA)) PIPE_SLV_ACK_XDMA (.clk (clk), 
                                                                           .rst_n (sync_rst_n), 
                                                                           .in_bus({tst_slv_ack[1+4+4+4+1+1], tst_slv_rdata[1+4+4+4+1+1]}),
                                                                           .out_bus({tst_slv_ack_pipe[1+4+4+4+1+1], tst_slv_rdata_pipe[1+4+4+4+1+1]})
                                                                           );

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

   axi_crossbar_0 AXI_CROSSBAR (
       .aclk(clk),
       .aresetn(sync_rst_n),

       .s_axi_awid(sh_cl_xdma_pcis_awid_q),
       .s_axi_awaddr(sh_cl_xdma_pcis_awaddr_q),
       .s_axi_awlen(sh_cl_xdma_pcis_awlen_q),
       .s_axi_awsize(3'b110),
       .s_axi_awburst(2'b1),
       .s_axi_awlock(1'b0),
       .s_axi_awcache(4'b11),
       .s_axi_awprot(3'b10),
       .s_axi_awqos(4'b0),
       .s_axi_awvalid(sh_cl_xdma_pcis_awvalid_q),
       .s_axi_awready(cl_sh_xdma_pcis_awready_q),

       .s_axi_wdata(sh_cl_xdma_pcis_wdata_q),
       .s_axi_wstrb(sh_cl_xdma_pcis_wstrb_q),
       .s_axi_wlast(sh_cl_xdma_pcis_wlast_q),
       .s_axi_wvalid(sh_cl_xdma_pcis_wvalid_q),
       .s_axi_wready(cl_sh_xdma_pcis_wready_q),

       .s_axi_bid(cl_sh_xdma_pcis_bid_q),
       .s_axi_bresp(cl_sh_xdma_pcis_bresp_q),
       .s_axi_bvalid(cl_sh_xdma_pcis_bvalid_q),
       .s_axi_bready(sh_cl_xdma_pcis_bready_q),

       .s_axi_arid(sh_cl_xdma_pcis_arid_q),
       .s_axi_araddr(sh_cl_xdma_pcis_araddr_q),
       .s_axi_arlen(sh_cl_xdma_pcis_arlen_q),
       .s_axi_arsize(3'b110),
       .s_axi_arburst(2'b1),
       .s_axi_arlock(1'b0),
       .s_axi_arcache(4'b11),
       .s_axi_arprot(3'b10),
       .s_axi_arqos(4'b0),
       .s_axi_arvalid(sh_cl_xdma_pcis_arvalid_q),
       .s_axi_arready(cl_sh_xdma_pcis_arready_q),

       .s_axi_rid(cl_sh_xdma_pcis_rid_q),
       .s_axi_rdata(cl_sh_xdma_pcis_rdata_q),
       .s_axi_rresp(cl_sh_xdma_pcis_rresp_q),
       .s_axi_rlast(cl_sh_xdma_pcis_rlast_q),
       .s_axi_rvalid(cl_sh_xdma_pcis_rvalid_q),
       .s_axi_rready(sh_cl_xdma_pcis_rready_q), 

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

   .sh_ddr_stat_addr   (sh_ddr_stat_addr_q) ,
   .sh_ddr_stat_wr     (sh_ddr_stat_wr_q     ) , 
   .sh_ddr_stat_rd     (sh_ddr_stat_rd_q     ) , 
   .sh_ddr_stat_wdata  (sh_ddr_stat_wdata_q  ) , 
   .ddr_sh_stat_ack    (ddr_sh_stat_ack_q    ) ,
   .ddr_sh_stat_rdata  (ddr_sh_stat_rdata_q  ),
   .ddr_sh_stat_int    (ddr_sh_stat_int_q    )
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
                   .init_clk          (kernel_clk0_out),
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
logic sh_cl_flr_assert_q;

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
   always_ff @(posedge clk or negedge sync_rst_n)
     if (!sync_rst_n)
       cl_sh_status0 <= 32'd0;
     else
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

   always_ff @(posedge clk or negedge sync_rst_n)
     if (!sync_rst_n)
       cl_sh_id0 <= 32'd0;
     else
       cl_sh_id0 <= dbg_scrb_en ? (dbg_scrb_mem_sel == 3'd3 ? dbg_ddr_scrb_addr_pipe[2][31:0] :
                                   dbg_scrb_mem_sel == 3'd2 ? dbg_ddr_scrb_addr_pipe[3][31:0] :
                                   dbg_scrb_mem_sel == 3'd1 ? dbg_ddr_scrb_addr_pipe[1][31:0] : dbg_ddr_scrb_addr_pipe[0][31:0]) :
                                    id0; 

   always_ff @(posedge clk or negedge sync_rst_n)
     if (!sync_rst_n)
       cl_sh_id1 <= 32'd0;
     else
       cl_sh_id1 <= dbg_scrb_en ? (dbg_scrb_mem_sel == 3'd3 ? dbg_ddr_scrb_addr_pipe[2][63:32] :
                                   dbg_scrb_mem_sel == 3'd2 ? dbg_ddr_scrb_addr_pipe[3][63:32] :
                                   dbg_scrb_mem_sel == 3'd1 ? dbg_ddr_scrb_addr_pipe[1][63:32] : dbg_ddr_scrb_addr_pipe[0][63:32]) :
                                    id1;

   assign cl_sh_status_vled = 16'h1E;

//-----------------------------------------------
// Debug bridge, used if need chipscope
//-----------------------------------------------
`ifndef DISABLE_CHIPSCOPE_DEBUG
/*
   ila_0 CL_ILA_0 (
                   .clk    (clk),
                   .probe0 (sh_cl_xdma_pcis_awvalid_q),
                   .probe1 (sh_cl_xdma_pcis_awaddr_q),
                   .probe2 (cl_sh_xdma_pcis_awready_q),
                   .probe3 (sh_cl_xdma_pcis_arvalid_q),
                   .probe4 (sh_cl_xdma_pcis_araddr_q),
                   .probe5 (cl_sh_xdma_pcis_arready_q)
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
                   .probe0 (cl_sh_ddr_awvalid_q),
                   .probe1 (cl_sh_ddr_awaddr_q),
                   .probe2 (2'b0),
                   .probe3 (sh_cl_ddr_awready_q),
                   .probe4 (cl_sh_ddr_wvalid_q),
                   .probe5 (cl_sh_ddr_wstrb_q),
                   .probe6 (cl_sh_ddr_wlast_q),
                   .probe7 (sh_cl_ddr_wready_q),
                   .probe8 (1'b0),
                   .probe9 (1'b0),
                   .probe10 (cl_sh_ddr_wdata_q),
                   .probe11 (1'b0),
                   .probe12 (sh_cl_ddr_arready_q),
                   .probe13 (2'b0),
                   .probe14 (sh_cl_ddr_rdata_q),
                   .probe15 (cl_sh_ddr_araddr_q),
                   .probe16 (cl_sh_ddr_arvalid_q),
                   .probe17 (3'b0),
                   .probe18 (3'b0),
                   .probe19 (cl_sh_ddr_awid_q),
                   .probe20 (cl_sh_ddr_arid_q),
                   .probe21 (cl_sh_ddr_awlen_q),
                   .probe22 (sh_cl_ddr_rlast_q),
                   .probe23 (3'b0), 
                   .probe24 (sh_cl_ddr_rresp_q),
                   .probe25 (sh_cl_ddr_rid_q),
                   .probe26 (sh_cl_ddr_rvalid_q),
                   .probe27 (cl_sh_ddr_arlen_q),
                   .probe28 (3'b0),
                   .probe29 (sh_cl_ddr_bresp_q),
                   .probe30 (cl_sh_ddr_rready_q),
                   .probe31 (4'b0),
                   .probe32 (4'b0),
                   .probe33 (4'b0),
                   .probe34 (4'b0),
                   .probe35 (sh_cl_ddr_bvalid_q),
                   .probe36 (4'b0),
                   .probe37 (4'b0),
                   .probe38 (sh_cl_ddr_bid_q),
                   .probe39 (cl_sh_ddr_bready_q),
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
   axil_slave  AXIL_SLAVE(
      .clk(clk),
      .rst_n(rst_n),
     
      .awvalid(sda_cl_awvalid), 
      .awaddr(sda_cl_awaddr),
      .awready(cl_sda_awready),
      
      .wvalid(sda_cl_wvalid),
      .wdata(sda_cl_wdata),
      .wstrb(sda_cl_wstrb),
      .wready(cl_sda_wready),
     
      .bvalid(cl_sda_bvalid), 
      .bresp(cl_sda_bresp),
      .bready(sda_cl_bready),
                   
      .arvalid(sda_cl_arvalid),
      .araddr(sda_cl_araddr),
      .arready(cl_sda_arready),
                    
      .rvalid(cl_sda_rvalid),
      .rdata(cl_sda_rdata),
      .rresp(cl_sda_rresp),
        
      .rready(sda_cl_rready)
   );

   axil_slave  AXIL_SLAVE_OCL(
      .clk(clk),
      .rst_n(rst_n),
     
      .awvalid(sh_ocl_awvalid), 
      .awaddr(sh_ocl_awaddr),
      .awready(ocl_sh_awready),
      
      .wvalid(sh_ocl_wvalid),
      .wdata(sh_ocl_wdata),
      .wstrb(sh_ocl_wstrb),
      .wready(ocl_sh_wready),
     
      .bvalid(ocl_sh_bvalid), 
      .bresp(ocl_sh_bresp),
      .bready(sh_ocl_bready),
                   
      .arvalid(sh_ocl_arvalid),
      .araddr(sh_ocl_araddr),
      .arready(ocl_sh_arready),
                    
      .rvalid(ocl_sh_rvalid),
      .rdata(ocl_sh_rdata),
      .rresp(ocl_sh_rresp),
        
      .rready(sh_ocl_rready)
   );
`endif


   
endmodule





