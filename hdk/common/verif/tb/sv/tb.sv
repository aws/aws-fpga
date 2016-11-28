// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

module tb();

   parameter NUM_DDR = 4;
   parameter NUM_HMC = 4;
   parameter NUM_PCIE = 1;
   parameter NUM_GTY = 4;
   parameter NUM_I2C = 2;
   parameter NUM_POWER = 4;

   logic clk_out;
   logic rst_out_n; 
   logic clk_xtra;
   logic rst_xtra_n;
   logic [1:0] sh_cl_pwr_state;

   logic [1:0] cfg_max_payload[NUM_PCIE-1:0];               //Max payload size - 00:128B, 01:256B, 10:512B
   logic [2:0] cfg_max_read_req[NUM_PCIE-1:0];              //Max read requst size - 000b:128B, 001b:256B, 010b:512B, 011b:1024B

   logic [31:0] sh_cl_ctl0;
   logic [31:0] sh_cl_ctl1;

   logic       sh_cl_flr_assert;
   logic       cl_sh_flr_done;
   
   logic [31:0] cl_sh_status0;
   logic [31:0] cl_sh_status1;
   logic [31:0] cl_sh_id0;
   logic [31:0] cl_sh_id1;
   
   //-------------------------------------
   // PCIe Master interface from CL
   //-------------------------------------
   logic [4:0]  cl_sh_pcim_awid[NUM_PCIE-1:0];
   logic [63:0] cl_sh_pcim_awaddr[NUM_PCIE-1:0];
   logic [7:0]  cl_sh_pcim_awlen[NUM_PCIE-1:0];
   logic [18:0] cl_sh_pcim_awuser[NUM_PCIE-1:0];
   logic [NUM_PCIE-1:0] cl_sh_pcim_awvalid;
   logic [NUM_PCIE-1:0] sh_cl_pcim_awready;
   
   logic [511:0]        cl_sh_pcim_wdata[NUM_PCIE-1:0];
   logic [63:0]         cl_sh_pcim_wstrb[NUM_PCIE-1:0];
   logic [NUM_PCIE-1:0] cl_sh_pcim_wlast;
   logic [NUM_PCIE-1:0] cl_sh_pcim_wvalid;
   logic [NUM_PCIE-1:0] sh_cl_pcim_wready;
   
   logic [4:0]          sh_cl_pcim_bid[NUM_PCIE-1:0];
   logic [1:0]          sh_cl_pcim_bresp[NUM_PCIE-1:0];
   logic [NUM_PCIE-1:0] sh_cl_pcim_bvalid;
   logic [NUM_PCIE-1:0] cl_sh_pcim_bready;
   
   logic [4:0]          cl_sh_pcim_arid[NUM_PCIE-1:0];
   logic [63:0]         cl_sh_pcim_araddr[NUM_PCIE-1:0];
   logic [7:0]          cl_sh_pcim_arlen[NUM_PCIE-1:0];
   logic [18:0]         cl_sh_pcim_aruser[NUM_PCIE-1:0];
   logic [NUM_PCIE-1:0] cl_sh_pcim_arvalid;
   logic [NUM_PCIE-1:0] sh_cl_pcim_arready;
   
   logic [4:0]          sh_cl_pcim_rid[NUM_PCIE-1:0];
   logic [511:0]        sh_cl_pcim_rdata[NUM_PCIE-1:0];
   logic [1:0]          sh_cl_pcim_rresp[NUM_PCIE-1:0];
   logic [NUM_PCIE-1:0] sh_cl_pcim_rlast;
   logic [NUM_PCIE-1:0] sh_cl_pcim_rvalid;
   logic [NUM_PCIE-1:0] cl_sh_pcim_rready;

   //------------------------------------------------
   // PCI Slave interface to CL
   //------------------------------------------------
   logic [63:0] sh_cl_pcis_awaddr[NUM_PCIE-1:0];
   logic [4:0]  sh_cl_pcis_awid[NUM_PCIE-1:0];
   logic [7:0]  sh_cl_pcis_awlen[NUM_PCIE-1:0];
   logic [NUM_PCIE-1:0] sh_cl_pcis_awuser;
   logic [NUM_PCIE-1:0] sh_cl_pcis_awvalid;
   logic [NUM_PCIE-1:0] cl_sh_pcis_awready;

   logic [511:0]        sh_cl_pcis_wdata[NUM_PCIE-1:0];
   logic [63:0]         sh_cl_pcis_wstrb[NUM_PCIE-1:0];
   logic [NUM_PCIE-1:0] sh_cl_pcis_wlast;
   logic [NUM_PCIE-1:0] sh_cl_pcis_wvalid;
   logic [NUM_PCIE-1:0] cl_sh_pcis_wready;
   
   logic [1:0]          cl_sh_pcis_bresp[NUM_PCIE-1:0];
   logic [4:0]          cl_sh_pcis_bid[NUM_PCIE-1:0];
   logic [NUM_PCIE-1:0] cl_sh_pcis_bvalid;
   logic [NUM_PCIE-1:0] sh_cl_pcis_bready;
   
   logic [63:0]         sh_cl_pcis_araddr[NUM_PCIE-1:0];
   logic [4:0]          sh_cl_pcis_arid[NUM_PCIE-1:0];
   logic [7:0]          sh_cl_pcis_arlen[NUM_PCIE-1:0];
   logic [NUM_PCIE-1:0] sh_cl_pcis_aruser;
   logic [NUM_PCIE-1:0] sh_cl_pcis_arvalid;
   logic [NUM_PCIE-1:0] cl_sh_pcis_arready;
   
   logic [4:0]          cl_sh_pcis_rid[NUM_PCIE-1:0];
   logic [511:0]        cl_sh_pcis_rdata[NUM_PCIE-1:0];
   logic [1:0]          cl_sh_pcis_rresp[NUM_PCIE-1:0];
   logic [NUM_PCIE-1:0] cl_sh_pcis_rlast;
   logic [NUM_PCIE-1:0] cl_sh_pcis_rvalid;
   logic [NUM_PCIE-1:0] sh_cl_pcis_rready;

   //------------------------------------------------------
   // DDR-4 Interface from CL (AXI-4)
   //------------------------------------------------------
   logic [5:0]          cl_sh_ddr_awid;
   logic [63:0]         cl_sh_ddr_awaddr;
   logic [7:0]          cl_sh_ddr_awlen;

   logic                cl_sh_ddr_awvalid;
   logic                sh_cl_ddr_awready;
   
   logic [5:0]          cl_sh_ddr_wid;
   logic [511:0]        cl_sh_ddr_wdata;
   logic [63:0]         cl_sh_ddr_wstrb;
   logic                cl_sh_ddr_wlast;
   logic                cl_sh_ddr_wvalid;
   logic                sh_cl_ddr_wready;
   
   logic [5:0]          sh_cl_ddr_bid;
   logic [1:0]          sh_cl_ddr_bresp;
   logic                sh_cl_ddr_bvalid;
   logic                cl_sh_ddr_bready;
   
   logic [5:0]          cl_sh_ddr_arid;
   logic [63:0]         cl_sh_ddr_araddr;
   logic [7:0]          cl_sh_ddr_arlen;

   logic                cl_sh_ddr_arvalid;
   logic                sh_cl_ddr_arready;
   
   logic [5:0]          sh_cl_ddr_rid;
   logic [511:0]        sh_cl_ddr_rdata;
   logic [1:0]          sh_cl_ddr_rresp;
   logic                sh_cl_ddr_rlast;
   logic                sh_cl_ddr_rvalid;
   logic                cl_sh_ddr_rready;
   
   logic                sh_cl_ddr_is_ready;
   logic [7:0]          sh_ddr_stat_addr[2:0];
   logic [2:0]          sh_ddr_stat_wr;
   logic [2:0]          sh_ddr_stat_rd;
   logic [31:0]         sh_ddr_stat_wdata[2:0];
   logic [2:0]          ddr_sh_stat_ack;
   logic [31:0]         ddr_sh_stat_rdata[2:0];
   logic [7:0]          ddr_sh_stat_int[2:0];
   
`include "tb_ddr.svh"
   
   //------------------------------------------------------
   // HMC Stat Interface from CL
   //------------------------------------------------------
   
   logic [7:0]         sh_hmc_stat_addr;
   logic               sh_hmc_stat_wr;
   logic               sh_hmc_stat_rd;
   logic [31:0]        sh_hmc_stat_wdata;   
   logic               hmc_sh_stat_ack;
   logic [31:0]        hmc_sh_stat_rdata;
   logic [7:0]         hmc_sh_stat_int;
   
   //------------------------------------------------------
   // HMC Stat Interface from CL
   //------------------------------------------------------
   
   logic               hmc_iic_scl_i;
   logic               hmc_iic_scl_o;
   logic               hmc_iic_scl_t;
   logic               hmc_iic_sda_i;
   logic               hmc_iic_sda_o;
   logic               hmc_iic_sda_t;
                              
   //------------------------------------------------------
   // Aurora Stat Interface from CL
   //------------------------------------------------------
   
   logic [7:0]         sh_aurora_stat_addr;
   logic               sh_aurora_stat_wr; 
   logic               sh_aurora_stat_rd; 
   logic [31:0]        sh_aurora_stat_wdata; 
   logic               aurora_sh_stat_ack;
   logic [31:0]        aurora_sh_stat_rdata;
   logic [7:0]         aurora_sh_stat_int;
   
   logic [31:0]        sv_host_memory[*];
   logic               use_c_host_memory = 1'b0;
   
`include "sh_dpi_tasks.svh"
   
sh_bfm sh(

   .cl_sh_status0(cl_sh_status0),
   .cl_sh_status1(cl_sh_status1),
   .cl_sh_id0(cl_sh_id0),
   .cl_sh_id1(cl_sh_id1),

   .sh_cl_ctl0(sh_cl_ctl0),
   .sh_cl_ctl1(sh_cl_ctl1),
   .clk_xtra(clk_xtra),
   .rst_xtra_n(rst_xtra_n),
   .clk_out(clk_out),
   .rst_out_n(rst_out_n),
   .sh_cl_pwr_state(sh_cl_pwr_state),

   //------------------------
   // PCI Express
   //------------------------
   .sh_cl_flr_assert(sh_cl_flr_assert),
   .cl_sh_flr_done(cl_sh_flr_done),

   //-------------------------------   
   // HMC
   //-------------------------------   
   .hmc_iic_scl_i(hmc_iic_scl_i),
   .hmc_iic_scl_o(hmc_iic_scl_o),
   .hmc_iic_scl_t(hmc_iic_scl_t),
   .hmc_iic_sda_i(hmc_iic_sda_i),
   .hmc_iic_sda_o(hmc_iic_sda_o),
   .hmc_iic_sda_t(hmc_iic_sda_t),

   .sh_hmc_stat_addr(sh_hmc_stat_addr),
   .sh_hmc_stat_wr(sh_hmc_stat_wr),
   .sh_hmc_stat_rd(sh_hmc_stat_rd),
   .sh_hmc_stat_wdata(sh_hmc_stat_wdata),
   .hmc_sh_stat_ack(hmc_sh_stat_ack),
   .hmc_sh_stat_rdata(hmc_sh_stat_rdata),
   .hmc_sh_stat_int(hmc_sh_stat_int),  

   //-------------------------------------
   // PCIe Interface from CL (AXI-4) (CL is PCI-master)
   //-------------------------------------
   .cl_sh_pcim_awid(cl_sh_pcim_awid),
   .cl_sh_pcim_awaddr(cl_sh_pcim_awaddr),
   .cl_sh_pcim_awlen(cl_sh_pcim_awlen),
   .cl_sh_pcim_awuser(cl_sh_pcim_awuser), // DW length of transfer
   .cl_sh_pcim_awvalid(cl_sh_pcim_awvalid),
   .sh_cl_pcim_awready(sh_cl_pcim_awready),

   .cl_sh_pcim_wdata(cl_sh_pcim_wdata),
   .cl_sh_pcim_wstrb(cl_sh_pcim_wstrb),
   .cl_sh_pcim_wlast(cl_sh_pcim_wlast),
   .cl_sh_pcim_wvalid(cl_sh_pcim_wvalid),
   .sh_cl_pcim_wready(sh_cl_pcim_wready),

   .sh_cl_pcim_bid(sh_cl_pcim_bid),
   .sh_cl_pcim_bresp(sh_cl_pcim_bresp),
   .sh_cl_pcim_bvalid(sh_cl_pcim_bvalid),
   .cl_sh_pcim_bready(cl_sh_pcim_bready),

   .cl_sh_pcim_arid(cl_sh_pcim_arid),
   .cl_sh_pcim_araddr(cl_sh_pcim_araddr),
   .cl_sh_pcim_arlen(cl_sh_pcim_arlen),
   .cl_sh_pcim_aruser(cl_sh_pcim_aruser), //DW length of transfer
   .cl_sh_pcim_arvalid(cl_sh_pcim_arvalid),
   .sh_cl_pcim_arready(sh_cl_pcim_arready),

   .sh_cl_pcim_rid(sh_cl_pcim_rid),
   .sh_cl_pcim_rdata(sh_cl_pcim_rdata),
   .sh_cl_pcim_rresp(sh_cl_pcim_rresp),
   .sh_cl_pcim_rlast(sh_cl_pcim_rlast),
   .sh_cl_pcim_rvalid(sh_cl_pcim_rvalid),
   .cl_sh_pcim_rready(cl_sh_pcim_rready),

   .cfg_max_payload(cfg_max_payload),               //Max payload size - 00:128B, 01:256B, 10:512B
   .cfg_max_read_req(cfg_max_read_req),              //Max read requst size - 000b:128B, 001b:256B, 010b:512B, 011b:1024B
                                                                  // 100b-2048B, 101b:4096B


   //-------------------------------------
   // PCIe Interface to CL (AXI-4) (CL is PCI-slave)
   //-------------------------------------
   .sh_cl_pcis_awaddr(sh_cl_pcis_awaddr),
   .sh_cl_pcis_awid(sh_cl_pcis_awid),
   .sh_cl_pcis_awlen(sh_cl_pcis_awlen),
   .sh_cl_pcis_awvalid(sh_cl_pcis_awvalid),
   .cl_sh_pcis_awready(cl_sh_pcis_awready),

   .sh_cl_pcis_wdata(sh_cl_pcis_wdata),
   .sh_cl_pcis_wstrb(sh_cl_pcis_wstrb),
   .sh_cl_pcis_wvalid(sh_cl_pcis_wvalid),
   .sh_cl_pcis_wlast(sh_cl_pcis_wlast),
   .cl_sh_pcis_wready(cl_sh_pcis_wready),

   .cl_sh_pcis_bresp(cl_sh_pcis_bresp),
   .cl_sh_pcis_bvalid(cl_sh_pcis_bvalid),
   .cl_sh_pcis_bid(cl_sh_pcis_bid),
   .sh_cl_pcis_bready(sh_cl_pcis_bready),

   .sh_cl_pcis_araddr(sh_cl_pcis_araddr),
   .sh_cl_pcis_arid(sh_cl_pcis_arid),
   .sh_cl_pcis_arlen(sh_cl_pcis_arlen),
   .sh_cl_pcis_arvalid(sh_cl_pcis_arvalid),
   .cl_sh_pcis_arready(cl_sh_pcis_arready),

   .cl_sh_pcis_rid(cl_sh_pcis_rid),
   .cl_sh_pcis_rdata(cl_sh_pcis_rdata),
   .cl_sh_pcis_rresp(cl_sh_pcis_rresp),
   .cl_sh_pcis_rlast(cl_sh_pcis_rlast),
   .cl_sh_pcis_rvalid(cl_sh_pcis_rvalid),
   .sh_cl_pcis_rready(sh_cl_pcis_rready),
          
   //-----------------------------------------
   // CL MSIX
   //-----------------------------------------
   .cl_sh_msix_int(),
   .cl_sh_msix_vec(),
   .sh_cl_msix_int_sent(),
   .sh_cl_msix_int_ack(),
    
   .cl_sh_aurora_channel_up(),
   .sh_aurora_stat_addr(sh_aurora_stat_addr),
   .sh_aurora_stat_wr(sh_aurora_stat_wr),
   .sh_aurora_stat_rd(sh_aurora_stat_rd),
   .sh_aurora_stat_wdata(sh_aurora_stat_wdata),

   .aurora_sh_stat_ack(aurora_sh_stat_ack),
   .aurora_sh_stat_rdata(aurora_sh_stat_rdata),
   .aurora_sh_stat_int(aurora_sh_stat_int),

   //--------------------------------------------------------------
   // DDR[3] (M_C_) interface 
   //--------------------------------------------------------------

   // ------------------- DDR4 x72 RDIMM 2100 Interface C ----------------------------------
   .CLK_300M_DIMM2_DP(CLK_300M_DIMM2_DP),
   .CLK_300M_DIMM2_DN(CLK_300M_DIMM2_DN),
   .M_C_ACT_N(M_C_ACT_N),
   .M_C_MA(M_C_MA),
   .M_C_BA(M_C_BA),
   .M_C_BG(M_C_BG),
   .M_C_CKE(M_C_CKE),
   .M_C_ODT(M_C_ODT),
   .M_C_CS_N(M_C_CS_N),
   .M_C_CLK_DN(M_C_CLK_DN),
   .M_C_CLK_DP(M_C_CLK_DP),
   .RST_DIMM_C_N(RST_DIMM_C_N),
   .M_C_PAR(M_C_PAR),
   .M_C_DQ(M_C_DQ),
   .M_C_ECC(M_C_ECC),
   .M_C_DQS_DP(M_C_DQS_DP),
   .M_C_DQS_DN(M_C_DQS_DN),

   //----------------------------------------------
   // DDR stats
   //----------------------------------------------
   .sh_ddr_stat_addr(sh_ddr_stat_addr),
   .sh_ddr_stat_wr(sh_ddr_stat_wr),
   .sh_ddr_stat_rd(sh_ddr_stat_rd),
   .sh_ddr_stat_wdata(sh_ddr_stat_wdata),

   .ddr_sh_stat_ack(ddr_sh_stat_ack),
   .ddr_sh_stat_rdata(ddr_sh_stat_rdata),
   .ddr_sh_stat_int(ddr_sh_stat_int),

   .cl_sh_ddr_awid(cl_sh_ddr_awid),
   .cl_sh_ddr_awaddr(cl_sh_ddr_awaddr),
   .cl_sh_ddr_awlen(cl_sh_ddr_awlen),
   .cl_sh_ddr_awvalid(cl_sh_ddr_awvalid),
   .sh_cl_ddr_awready(sh_cl_ddr_awready),

   .cl_sh_ddr_wid(cl_sh_ddr_wid),
   .cl_sh_ddr_wdata(cl_sh_ddr_wdata),
   .cl_sh_ddr_wstrb(cl_sh_ddr_wstrb),
   .cl_sh_ddr_wlast(cl_sh_ddr_wlast),
   .cl_sh_ddr_wvalid(cl_sh_ddr_wvalid),
   .sh_cl_ddr_wready(sh_cl_ddr_wready),

   .sh_cl_ddr_bid(sh_cl_ddr_bid),
   .sh_cl_ddr_bresp(sh_cl_ddr_bresp),
   .sh_cl_ddr_bvalid(sh_cl_ddr_bvalid),
   .cl_sh_ddr_bready(cl_sh_ddr_bready),

   .cl_sh_ddr_arid(cl_sh_ddr_arid),
   .cl_sh_ddr_araddr(cl_sh_ddr_araddr),
   .cl_sh_ddr_arlen(cl_sh_ddr_arlen),
   .cl_sh_ddr_arvalid(cl_sh_ddr_arvalid),
   .sh_cl_ddr_arready(sh_cl_ddr_arready),

   .sh_cl_ddr_rid(sh_cl_ddr_rid),
   .sh_cl_ddr_rdata(sh_cl_ddr_rdata),
   .sh_cl_ddr_rresp(sh_cl_ddr_rresp),
   .sh_cl_ddr_rlast(sh_cl_ddr_rlast),
   .sh_cl_ddr_rvalid(sh_cl_ddr_rvalid),
   .cl_sh_ddr_rready(cl_sh_ddr_rready),
   .sh_cl_ddr_is_ready(sh_cl_ddr_is_ready),

   .sh_RST_DIMM_A_N(),
   .sh_RST_DIMM_B_N(),
   .sh_RST_DIMM_D_N()

          );

`ifndef CL_NAME
 `define CL_NAME cl_simple
`endif



   //Developer put top level here (replace cl_simple, with top level)
   `CL_NAME #(.NUM_PCIE(NUM_PCIE), .NUM_DDR(NUM_DDR), .NUM_HMC(NUM_HMC), .NUM_GTY(NUM_GTY)) CL (
   
      .clk(clk_out),
      .rst_n(rst_out_n), 
      .clk_xtra (clk_xtra),
      .rst_xtra_n(rst_xtra_n),

      .sh_cl_pwr_state(sh_cl_pwr_state),

      .sh_cl_flr_assert(sh_cl_flr_assert),
      .cl_sh_flr_done(cl_sh_flr_done),

      .cl_sh_status0(cl_sh_status0),
      .cl_sh_status1(cl_sh_status1),
      .cl_sh_id0(cl_sh_id0),
      .cl_sh_id1(cl_sh_id1),

      .sh_cl_ctl0(sh_cl_ctl0),
      .sh_cl_ctl1(sh_cl_ctl1),
  
      .cfg_max_payload(cfg_max_payload),
      .cfg_max_read_req(cfg_max_read_req),
 
      .sh_cl_pcis_awaddr(sh_cl_pcis_awaddr),
      .sh_cl_pcis_awid(sh_cl_pcis_awid),
      .sh_cl_pcis_awlen(sh_cl_pcis_awlen),
      .sh_cl_pcis_awvalid(sh_cl_pcis_awvalid),
      .cl_sh_pcis_awready(cl_sh_pcis_awready),
   
      .sh_cl_pcis_wdata(sh_cl_pcis_wdata),
      .sh_cl_pcis_wstrb(sh_cl_pcis_wstrb),
      .sh_cl_pcis_wlast(sh_cl_pcis_wlast),
      .sh_cl_pcis_wvalid(sh_cl_pcis_wvalid),
      .cl_sh_pcis_wready(cl_sh_pcis_wready),
   
      .cl_sh_pcis_bresp(cl_sh_pcis_bresp),
      .cl_sh_pcis_bid(cl_sh_pcis_bid),
      .cl_sh_pcis_bvalid(cl_sh_pcis_bvalid),
      .sh_cl_pcis_bready(sh_cl_pcis_bready),
   
      .sh_cl_pcis_araddr(sh_cl_pcis_araddr),
      .sh_cl_pcis_arid(sh_cl_pcis_arid),
      .sh_cl_pcis_arlen(sh_cl_pcis_arlen),
      .sh_cl_pcis_arvalid(sh_cl_pcis_arvalid),
      .cl_sh_pcis_arready(cl_sh_pcis_arready),
   
      .cl_sh_pcis_rid(cl_sh_pcis_rid),
      .cl_sh_pcis_rdata(cl_sh_pcis_rdata),
      .cl_sh_pcis_rresp(cl_sh_pcis_rresp),
      .cl_sh_pcis_rlast(cl_sh_pcis_rlast),
      .cl_sh_pcis_rvalid(cl_sh_pcis_rvalid),
      .sh_cl_pcis_rready(sh_cl_pcis_rready),
   
   
      .cl_sh_pcim_awid(cl_sh_pcim_awid),
      .cl_sh_pcim_awaddr(cl_sh_pcim_awaddr),
      .cl_sh_pcim_awlen(cl_sh_pcim_awlen),
      .cl_sh_pcim_awuser(cl_sh_pcim_awuser),
      .cl_sh_pcim_awvalid(cl_sh_pcim_awvalid),
      .sh_cl_pcim_awready(sh_cl_pcim_awready),
   
      .cl_sh_pcim_wdata(cl_sh_pcim_wdata),
      .cl_sh_pcim_wstrb(cl_sh_pcim_wstrb),
      .cl_sh_pcim_wlast(cl_sh_pcim_wlast),
      .cl_sh_pcim_wvalid(cl_sh_pcim_wvalid),
      .sh_cl_pcim_wready(sh_cl_pcim_wready),
   
      .sh_cl_pcim_bid(sh_cl_pcim_bid),
      .sh_cl_pcim_bresp(sh_cl_pcim_bresp),
      .sh_cl_pcim_bvalid(sh_cl_pcim_bvalid),
      .cl_sh_pcim_bready(cl_sh_pcim_bready),
   
      .cl_sh_pcim_arid(cl_sh_pcim_arid),
      .cl_sh_pcim_araddr(cl_sh_pcim_araddr),
      .cl_sh_pcim_arlen(cl_sh_pcim_arlen),
      .cl_sh_pcim_aruser(cl_sh_pcim_aruser),
      .cl_sh_pcim_arvalid(cl_sh_pcim_arvalid),
      .sh_cl_pcim_arready(sh_cl_pcim_arready),
   
      .sh_cl_pcim_rid(sh_cl_pcim_rid),
      .sh_cl_pcim_rdata(sh_cl_pcim_rdata),
      .sh_cl_pcim_rresp(sh_cl_pcim_rresp),
      .sh_cl_pcim_rlast(sh_cl_pcim_rlast),
      .sh_cl_pcim_rvalid(sh_cl_pcim_rvalid),
      .cl_sh_pcim_rready(cl_sh_pcim_rready),

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

      .sh_ddr_stat_addr(sh_ddr_stat_addr),
      .sh_ddr_stat_wr(sh_ddr_stat_wr),
      .sh_ddr_stat_rd(sh_ddr_stat_rd),
      .sh_ddr_stat_wdata(sh_ddr_stat_wdata),

      .ddr_sh_stat_ack(ddr_sh_stat_ack),
      .ddr_sh_stat_rdata(ddr_sh_stat_rdata),
      .ddr_sh_stat_int(ddr_sh_stat_int),

      .cl_sh_ddr_awid(cl_sh_ddr_awid),
      .cl_sh_ddr_awaddr(cl_sh_ddr_awaddr),
      .cl_sh_ddr_awlen(cl_sh_ddr_awlen),
      .cl_sh_ddr_awvalid(cl_sh_ddr_awvalid),
      .sh_cl_ddr_awready(sh_cl_ddr_awready),
   
      .cl_sh_ddr_wid(cl_sh_ddr_wid),
      .cl_sh_ddr_wdata(cl_sh_ddr_wdata),
      .cl_sh_ddr_wstrb(cl_sh_ddr_wstrb),
      .cl_sh_ddr_wlast(cl_sh_ddr_wlast),
      .cl_sh_ddr_wvalid(cl_sh_ddr_wvalid),
      .sh_cl_ddr_wready(sh_cl_ddr_wready),
   
      .sh_cl_ddr_bid(sh_cl_ddr_bid),
      .sh_cl_ddr_bresp(sh_cl_ddr_bresp),
      .sh_cl_ddr_bvalid(sh_cl_ddr_bvalid),
      .cl_sh_ddr_bready(cl_sh_ddr_bready),
   
      .cl_sh_ddr_arid(cl_sh_ddr_arid),
      .cl_sh_ddr_araddr(cl_sh_ddr_araddr),
      .cl_sh_ddr_arlen(cl_sh_ddr_arlen),
      .cl_sh_ddr_arvalid(cl_sh_ddr_arvalid),
      .sh_cl_ddr_arready(sh_cl_ddr_arready),
   
      .sh_cl_ddr_rid(sh_cl_ddr_rid),
      .sh_cl_ddr_rdata(sh_cl_ddr_rdata),
      .sh_cl_ddr_rresp(sh_cl_ddr_rresp),
      .sh_cl_ddr_rlast(sh_cl_ddr_rlast),
      .sh_cl_ddr_rvalid(sh_cl_ddr_rvalid),
      .cl_sh_ddr_rready(cl_sh_ddr_rready),
   
      .sh_cl_ddr_is_ready(sh_cl_ddr_is_ready),

`ifdef ENABLE_CS_DEBUG
      //Debug (chipscope)
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
      .bscanid(bscanid),
`endif
   
   .hmc_iic_scl_i(hmc_iic_scl_i),
   .hmc_iic_scl_o(hmc_iic_scl_o),
   .hmc_iic_scl_t(hmc_iic_scl_t),
   .hmc_iic_sda_i(hmc_iic_sda_i),
   .hmc_iic_sda_o(hmc_iic_sda_o),
   .hmc_iic_sda_t(hmc_iic_sda_t),

   .sh_hmc_stat_addr(sh_hmc_stat_addr),
   .sh_hmc_stat_wr(sh_hmc_stat_wr),
   .sh_hmc_stat_rd(sh_hmc_stat_rd),
   .sh_hmc_stat_wdata(sh_hmc_stat_wdata),

   .hmc_sh_stat_ack(hmc_sh_stat_ack),
   .hmc_sh_stat_rdata(hmc_sh_stat_rdata),

   .hmc_sh_stat_int(hmc_sh_stat_int),

   .sh_aurora_stat_addr   (sh_aurora_stat_addr),
   .sh_aurora_stat_wr     (sh_aurora_stat_wr), 
   .sh_aurora_stat_rd     (sh_aurora_stat_rd), 
   .sh_aurora_stat_wdata  (sh_aurora_stat_wdata), 
   .aurora_sh_stat_ack    (aurora_sh_stat_ack),
   .aurora_sh_stat_rdata  (aurora_sh_stat_rdata),
   .aurora_sh_stat_int    (aurora_sh_stat_int)
                                       
      );

   
endmodule // tb

`ifdef XILINX_SIMULATOR
  module short(in1, in1);
    inout in1;
  endmodule
`endif

