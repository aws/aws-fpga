// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

//FIXME -- Need to do the clocking correctly:
//    - Async Stream between PCIe cores and User logic

module sh_bfm #(
                     parameter NUM_HMC = 4,
                     parameter NUM_QSFP = 4,
                     parameter NUM_PCIE = 1,
                     parameter NUM_GTY = 4,
                     parameter NUM_I2C = 2,
                     parameter NUM_POWER = 4,
                     parameter DDR_C_PRESENT = 0
                  )

   (
   //--------------------
   // Main input clock
   //--------------------

   input [31:0]                cl_sh_status0,
   input [31:0]                cl_sh_status1,
   input [31:0]                cl_sh_id0,
   input [31:0]                cl_sh_id1,

   output logic[31:0]          sh_cl_ctl0,
   output logic[31:0]          sh_cl_ctl1,
   output logic                clk_xtra,
   output logic                rst_xtra_n,
   output logic[1:0]           sh_cl_pwr_state,

   output logic                clk_out,
   output logic                rst_out_n,

   output logic                sh_cl_flr_assert,
   input                       cl_sh_flr_done

   //-------------------------------   
   // HMC
   //-------------------------------   
   ,
   output logic               hmc_iic_scl_i,
   input                      hmc_iic_scl_o,
   input                      hmc_iic_scl_t,
   output logic               hmc_iic_sda_i,
   input                      hmc_iic_sda_o,
   input                      hmc_iic_sda_t,

   output[7:0]                 sh_hmc_stat_addr,
   output                      sh_hmc_stat_wr,
   output                      sh_hmc_stat_rd,
   output[31:0]                sh_hmc_stat_wdata,

   input                       hmc_sh_stat_ack,
   input [31:0]                hmc_sh_stat_rdata,

   input[7:0]                  hmc_sh_stat_int

    
   ,
   //-------------------------------------
   // PCIe Interface from CL (AXI-4) (CL is PCI-master)
   //-------------------------------------
   input [4:0]                 cl_sh_pcim_awid[NUM_PCIE-1:0],
   input [63:0]                cl_sh_pcim_awaddr[NUM_PCIE-1:0],
   input [7:0]                 cl_sh_pcim_awlen[NUM_PCIE-1:0],
   input [18:0]                cl_sh_pcim_awuser[NUM_PCIE-1:0], //DW length of transfer
   input [NUM_PCIE-1:0]        cl_sh_pcim_awvalid,
   output logic [NUM_PCIE-1:0] sh_cl_pcim_awready,

//Not used   input [4:0]                 cl_sh_pcim_wid[NUM_PCIE-1:0],
   input [511:0]               cl_sh_pcim_wdata[NUM_PCIE-1:0],
   input [63:0]                cl_sh_pcim_wstrb[NUM_PCIE-1:0],
   input [NUM_PCIE-1:0]        cl_sh_pcim_wlast,
   input [NUM_PCIE-1:0]        cl_sh_pcim_wvalid,
   output logic [NUM_PCIE-1:0] sh_cl_pcim_wready,

   output logic [4:0]          sh_cl_pcim_bid[NUM_PCIE-1:0],
   output logic [1:0]          sh_cl_pcim_bresp[NUM_PCIE-1:0],
   output logic [NUM_PCIE-1:0] sh_cl_pcim_bvalid,
   input [NUM_PCIE-1:0]        cl_sh_pcim_bready,

   input [4:0]                 cl_sh_pcim_arid[NUM_PCIE-1:0],
   input [63:0]                cl_sh_pcim_araddr[NUM_PCIE-1:0],
   input [7:0]                 cl_sh_pcim_arlen[NUM_PCIE-1:0],
   input [18:0]                cl_sh_pcim_aruser[NUM_PCIE-1:0], //DW length of transfer
   input [NUM_PCIE-1:0]        cl_sh_pcim_arvalid,
   output logic [NUM_PCIE-1:0] sh_cl_pcim_arready,

   output logic [4:0]          sh_cl_pcim_rid[NUM_PCIE-1:0],
   output logic [511:0]        sh_cl_pcim_rdata[NUM_PCIE-1:0],
   output logic [1:0]          sh_cl_pcim_rresp[NUM_PCIE-1:0],
   output logic [NUM_PCIE-1:0] sh_cl_pcim_rlast,
   output logic [NUM_PCIE-1:0] sh_cl_pcim_rvalid,
   input [NUM_PCIE-1:0]        cl_sh_pcim_rready,

   output logic[1:0] cfg_max_payload[NUM_PCIE-1:0],               //Max payload size - 00:128B, 01:256B, 10:512B
   output logic[2:0] cfg_max_read_req[NUM_PCIE-1:0],              //Max read requst size - 000b:128B, 001b:256B, 010b:512B, 011b:1024B
                                                                  // 100b-2048B, 101b:4096B


   //-------------------------------------
   // PCIe Interface to CL (AXI-4) (CL is PCI-slave)
   //-------------------------------------
   output logic [63:0]               sh_cl_pcis_awaddr[NUM_PCIE-1:0],
   output logic [4:0]                sh_cl_pcis_awid[NUM_PCIE-1:0],
   output logic [7:0]                sh_cl_pcis_awlen[NUM_PCIE-1:0],
   output logic [NUM_PCIE-1:0]       sh_cl_pcis_awvalid,
   input [NUM_PCIE-1:0]        cl_sh_pcis_awready,

   output logic [511:0]              sh_cl_pcis_wdata[NUM_PCIE-1:0],
   output logic [63:0]               sh_cl_pcis_wstrb[NUM_PCIE-1:0],
   output logic [NUM_PCIE-1:0]       sh_cl_pcis_wvalid,
   output logic [NUM_PCIE-1:0]       sh_cl_pcis_wlast,
   input [NUM_PCIE-1:0]        cl_sh_pcis_wready,

   input [1:0]                 cl_sh_pcis_bresp[NUM_PCIE-1:0],
   input [NUM_PCIE-1:0]        cl_sh_pcis_bvalid,
   input [4:0]                 cl_sh_pcis_bid[NUM_PCIE-1:0],
   output logic [NUM_PCIE-1:0]       sh_cl_pcis_bready,

   output logic [63:0]         sh_cl_pcis_araddr[NUM_PCIE-1:0],
   output logic [4:0]          sh_cl_pcis_arid[NUM_PCIE-1:0],
   output logic [7:0]          sh_cl_pcis_arlen[NUM_PCIE-1:0],
   output logic [NUM_PCIE-1:0] sh_cl_pcis_arvalid,
   input [NUM_PCIE-1:0]        cl_sh_pcis_arready,

   input [4:0]                 cl_sh_pcis_rid[NUM_PCIE-1:0],
   input [511:0]               cl_sh_pcis_rdata[NUM_PCIE-1:0],
   input [1:0]                 cl_sh_pcis_rresp[NUM_PCIE-1:0],
   input [NUM_PCIE-1:0]        cl_sh_pcis_rlast,
   input [NUM_PCIE-1:0]        cl_sh_pcis_rvalid,
   output logic [NUM_PCIE-1:0] sh_cl_pcis_rready,

`ifndef VU190    
   //-----------------------------------------
   // CL MSIX
   //-----------------------------------------
    input               cl_sh_msix_int,
    input [7:0]         cl_sh_msix_vec,
    output logic        sh_cl_msix_int_sent,
    output logic        sh_cl_msix_int_ack
`endif
    
   ,
   input [NUM_GTY-1:0]        cl_sh_aurora_channel_up,
   output[7:0]                 sh_aurora_stat_addr,
   output                      sh_aurora_stat_wr,
   output                      sh_aurora_stat_rd,
   output[31:0]                sh_aurora_stat_wdata,

   input                       aurora_sh_stat_ack,
   input [31:0]                aurora_sh_stat_rdata,
   input[7:0]                 aurora_sh_stat_int

   //--------------------------------------------------------------
   // DDR[3] (M_C_) interface 
   //--------------------------------------------------------------
   ,
   // ------------------- DDR4 x72 RDIMM 2100 Interface C ----------------------------------
   input                       CLK_300M_DIMM2_DP,
   input                       CLK_300M_DIMM2_DN,
   output logic                M_C_ACT_N,
   output logic [16:0]         M_C_MA,
   output logic [1:0]          M_C_BA,
   output logic [1:0]          M_C_BG,
   output logic [0:0]          M_C_CKE,
   output logic [0:0]          M_C_ODT,
   output logic [0:0]          M_C_CS_N,
   output logic [0:0]          M_C_CLK_DN,
   output logic [0:0]          M_C_CLK_DP,
   output logic                RST_DIMM_C_N,
   output logic                M_C_PAR,
   inout [63:0]                M_C_DQ,
   inout [7:0]                 M_C_ECC,
   inout [17:0]                M_C_DQS_DP,
   inout [17:0]                M_C_DQS_DN,



   //----------------------------------------------
   // DDR stats
   //----------------------------------------------
   output logic[7:0]           sh_ddr_stat_addr[2:0],
   output logic[2:0]           sh_ddr_stat_wr,
   output logic[2:0]           sh_ddr_stat_rd,
   output logic[31:0]          sh_ddr_stat_wdata[2:0],

   input [2:0]                 ddr_sh_stat_ack,
   input [31:0]                ddr_sh_stat_rdata[2:0],
   input[7:0]                  ddr_sh_stat_int[2:0],

   input [5:0]                 cl_sh_ddr_awid,
   input [63:0]                cl_sh_ddr_awaddr,
   input [7:0]                 cl_sh_ddr_awlen,
   input                       cl_sh_ddr_awvalid,
   output logic                sh_cl_ddr_awready,

   input [5:0]                 cl_sh_ddr_wid,
   input [511:0]               cl_sh_ddr_wdata,
   input [63:0]                cl_sh_ddr_wstrb,
   input                       cl_sh_ddr_wlast,
   input                       cl_sh_ddr_wvalid,
   output logic                sh_cl_ddr_wready,

   output logic [5:0]          sh_cl_ddr_bid,
   output logic [1:0]          sh_cl_ddr_bresp,
   output logic                sh_cl_ddr_bvalid,
   input                       cl_sh_ddr_bready,

   input [5:0]                 cl_sh_ddr_arid,
   input [63:0]                cl_sh_ddr_araddr,
   input [7:0]                 cl_sh_ddr_arlen,
   input                       cl_sh_ddr_arvalid,
   output logic                sh_cl_ddr_arready,

   output logic [5:0]          sh_cl_ddr_rid,
   output logic [511:0]        sh_cl_ddr_rdata,
   output logic [1:0]          sh_cl_ddr_rresp,
   output logic                sh_cl_ddr_rlast,
   output logic                sh_cl_ddr_rvalid,
   input                       cl_sh_ddr_rready,

   output logic                sh_cl_ddr_is_ready,

   inout                       SYSMON_SCL,
   inout                       SYSMON_SDA,

   inout[3:0]                 fpga_uctrl_gpio



`ifndef NO_CL_DDR
   ,
   output              sh_RST_DIMM_A_N,
   output              sh_RST_DIMM_B_N,
   output              sh_RST_DIMM_D_N
`endif  
                               

    
  
   );

typedef struct {
   logic [63:0] addr;
   logic [7:0]  len;
   logic [5:0]  id;
   logic [1:0]  resp;
} AXI_Command;
   
typedef struct {
   logic [511:0] data;
   logic [63:0]  strb;
   logic [5:0]   id;
   logic         last;
} AXI_Data;

   AXI_Command sh_cl_wr_cmds[$];
   AXI_Data    sh_cl_wr_data[$];
   AXI_Command sh_cl_rd_cmds[$];
   AXI_Data    cl_sh_rd_data[$];
   AXI_Command sh_cl_b_resps[$];
   
   AXI_Command cl_sh_wr_cmds[$];
   AXI_Data    cl_sh_wr_data[$];
   AXI_Command cl_sh_rd_cmds[$];
   AXI_Data    sh_cl_rd_data[$];
   AXI_Command cl_sh_b_resps[$];
   
   logic         clk_core;
   logic         rst_n;
   logic         pre_sync0_rst_n;
   logic         pre_sync1_rst_n;
   logic         pre_sync2_rst_n;
   logic         pre_sync3_rst_n;
   logic         sync_rst_n;
   logic         intf_sync_rst_n;
   logic         ddr_user_rst;
   logic         ddr_user_rst_n;
   logic         ddr_is_ready_presync;
   logic         ddr_is_ready_sync;

   logic [5:0]   cl_sh_ddr_awid_q;
   logic [63:0]  cl_sh_ddr_awaddr_q;
   logic [7:0]   cl_sh_ddr_awlen_q;
   logic         cl_sh_ddr_awvalid_q;
   logic         sh_cl_ddr_awready_q;

   logic [511:0] cl_sh_ddr_wdata_q;
   logic [63:0]  cl_sh_ddr_wstrb_q;
   logic         cl_sh_ddr_wlast_q;
   logic         cl_sh_ddr_wvalid_q;
   logic         sh_cl_ddr_wready_q;

   logic [5:0]   sh_cl_ddr_bid_q;
   logic [1:0]   sh_cl_ddr_bresp_q;
   logic         sh_cl_ddr_bvalid_q;
   logic         cl_sh_ddr_bready_q;
   
   logic [5:0]   cl_sh_ddr_arid_q;
   logic [63:0]  cl_sh_ddr_araddr_q;
   logic [7:0]   cl_sh_ddr_arlen_q;
   logic         cl_sh_ddr_arvalid_q;
   logic         sh_cl_ddr_arready_q;

   logic [5:0]   sh_cl_ddr_rid_q;
   logic [511:0] sh_cl_ddr_rdata_q;
   logic [1:0]   sh_cl_ddr_rresp_q;
   logic         sh_cl_ddr_rlast_q;
   logic         sh_cl_ddr_rvalid_q;
   logic         cl_sh_ddr_rready_q;

   logic [5:0]   sync_cl_sh_ddr_awid;
   logic [63:0]  sync_cl_sh_ddr_awaddr;
   logic [7:0]   sync_cl_sh_ddr_awlen;
   logic         sync_cl_sh_ddr_awvalid;
   logic         sync_sh_cl_ddr_awready;

   logic [511:0] sync_cl_sh_ddr_wdata;
   logic [63:0]  sync_cl_sh_ddr_wstrb;
   logic         sync_cl_sh_ddr_wlast;
   logic         sync_cl_sh_ddr_wvalid;
   logic         sync_sh_cl_ddr_wready;

   logic [5:0]   sync_sh_cl_ddr_bid;
   logic [1:0]   sync_sh_cl_ddr_bresp;
   logic         sync_sh_cl_ddr_bvalid;
   logic         sync_cl_sh_ddr_bready;

   logic [5:0]   sync_cl_sh_ddr_arid;
   logic [63:0]  sync_cl_sh_ddr_araddr;
   logic [7:0]   sync_cl_sh_ddr_arlen;
   logic         sync_cl_sh_ddr_arvalid;
   logic         sync_sh_cl_ddr_arready;

   logic [5:0]   sync_sh_cl_ddr_rid;
   logic [511:0] sync_sh_cl_ddr_rdata;
   logic [1:0]   sync_sh_cl_ddr_rresp;
   logic         sync_sh_cl_ddr_rlast;
   logic         sync_sh_cl_ddr_rvalid;
   logic         sync_cl_sh_ddr_rready;

   // DEBUG: Need to do something with these...
   logic         ddr_axl_awvalid;
   logic         ddr_axl_awready;
   logic [31:0]  ddr_axl_awaddr;
   logic         ddr_axl_wvalid;
   logic         ddr_axl_wready;
   logic [31:0]  ddr_axl_wdata;
   logic         ddr_axl_bvalid;
   logic         ddr_axl_bready;
   logic [1:0]   ddr_axl_bresp;
   logic         ddr_axl_arvalid;
   logic         ddr_axl_arready;
   logic [31:0]  ddr_axl_araddr;
   logic         ddr_axl_rvalid;
   logic         ddr_axl_rready;
   logic [31:0]  ddr_axl_rdata;
   logic [1:0]   ddr_axl_rresp;
   logic         ddr_axl_interrupt;

   initial begin
      clk_core = 1'b0;      
      forever #5ns clk_core = ~clk_core;
   end
   
   initial begin
      clk_out = 1'b0;      
      forever #2ns clk_out = ~clk_out;
   end
   
   initial begin
      clk_xtra = 1'b0;      
      forever #4ns clk_xtra = ~clk_xtra;
   end

   logic rst_n_i;
   logic rst_out_n_i;
   logic rst_xtra_n_i;

   always @(posedge clk_core)
     rst_n <= rst_n_i;
   
   always @(posedge clk_out)
     rst_out_n <= rst_out_n_i;
   
   always @(posedge clk_xtra)
     rst_xtra_n <= rst_xtra_n_i;

   always_ff @(negedge rst_n or posedge clk_core)
     if (!rst_n)
       begin
          pre_sync0_rst_n <= 0;
          pre_sync1_rst_n <= 0;
          pre_sync2_rst_n <= 0;
          pre_sync3_rst_n <= 0;
          sync_rst_n      <= 0;
       end
     else
       begin
          pre_sync0_rst_n <= 1'b1;
          pre_sync1_rst_n <= pre_sync0_rst_n;
          pre_sync2_rst_n <= pre_sync1_rst_n;
          pre_sync3_rst_n <= pre_sync2_rst_n;
          sync_rst_n      <= pre_sync3_rst_n;
       end

   always @(posedge clk_out) begin
      sh_cl_pwr_state <= 2'b00;
   end

   initial begin
      sh_cl_ctl0 <= 32'h0;
      sh_cl_ctl1 <= 32'h0;
   end

   initial begin
      sh_cl_flr_assert <= 1'b0;
   end

   always_ff @(posedge clk_core or negedge sync_rst_n)
     if (~sync_rst_n)
       intf_sync_rst_n <= 0;
     else
       intf_sync_rst_n <= ~(sh_cl_flr_assert);

   initial begin
      for (int i=0; i<NUM_PCIE; i++) begin
         cfg_max_payload[i] <= 2'b01; // 256 bytes
         cfg_max_read_req[i] <= 3'b001; // 256 bytes
      end
   end

   assign ddr_user_rst_n = ~ddr_user_rst;

   //=================================================
   //
   // sh->cl PCIeS Interface
   //
   //=================================================

   //
   // sh->cl Address Write Channel
   //

   always @(posedge clk_out) begin
      if (sh_cl_wr_cmds.size() != 0) begin

         sh_cl_pcis_awaddr[0]  <= sh_cl_wr_cmds[0].addr;
         sh_cl_pcis_awid[0]    <= sh_cl_wr_cmds[0].id;
         sh_cl_pcis_awlen[0]   <= sh_cl_wr_cmds[0].len;
         
         sh_cl_pcis_awvalid[0] <= !sh_cl_pcis_awvalid[0] ? 1'b1 :
                                  !cl_sh_pcis_awready[0] ? 1'b1 : 1'b0;
         
         if (cl_sh_pcis_awready[0] && sh_cl_pcis_awvalid[0]) begin
            $display("%t - debug popping cmd fifo - %d", $time(), sh_cl_wr_cmds.size());
            sh_cl_wr_cmds.pop_front();
         end

      end
      else
         sh_cl_pcis_awvalid <= 1'b0;
   end


   //
   // write Data Channel
   //

   //
   // sh->cl Address Write Channel
   //

   always @(posedge clk_out) begin
      if (sh_cl_wr_data.size() != 0) begin

         sh_cl_pcis_wdata[0] <= sh_cl_wr_data[0].data;
         sh_cl_pcis_wstrb[0] <= sh_cl_wr_data[0].strb;
         sh_cl_pcis_wlast[0] <= sh_cl_wr_data[0].last;
         
         sh_cl_pcis_wvalid[0] <= !sh_cl_pcis_wvalid[0] ? 1'b1 :
                                 !cl_sh_pcis_wready[0] ? 1'b1 : 1'b0;
         
         if (cl_sh_pcis_wready[0] && sh_cl_pcis_wvalid[0]) begin
            $display("%t - debug popping wr data fifo - %d", $time(), sh_cl_wr_data.size());
            sh_cl_wr_data.pop_front();
         end

      end
      else
         sh_cl_pcis_wvalid <= 1'b0;
   end

   //
   // cl->sh B Response Channel
   //
   always @(posedge clk_out) begin
      sh_cl_pcis_bready[0] <= 1'b1;
   end

   always @(posedge clk_out) begin
      AXI_Command resp;

      if (cl_sh_pcis_bvalid[0] & sh_cl_pcis_bready) begin
         resp.resp     = cl_sh_pcis_bresp[0];
         resp.id       = cl_sh_pcis_bid[0];

         cl_sh_b_resps.push_back(resp);
      end

   end


   //
   // sh->cl Address Read Channel
   //

   always @(posedge clk_out) begin
      if (sh_cl_rd_cmds.size() != 0) begin

         sh_cl_pcis_araddr[0]  <= sh_cl_rd_cmds[0].addr;
         sh_cl_pcis_arid[0]    <= sh_cl_rd_cmds[0].id;
         sh_cl_pcis_arlen[0]   <= sh_cl_rd_cmds[0].len;
         
         sh_cl_pcis_arvalid[0] <= !sh_cl_pcis_arvalid[0] ? 1'b1 :
                                  !cl_sh_pcis_arready[0] ? 1'b1 : 1'b0;
         
         if (cl_sh_pcis_arready[0] && sh_cl_pcis_arvalid[0]) begin
            $display("%t - debug popping cmd fifo - %d", $time(), sh_cl_rd_cmds.size());
            sh_cl_rd_cmds.pop_front();
         end

      end
      else
         sh_cl_pcis_arvalid <= 1'b0;
   end

   //
   // cl->sh Read Data Channel
   //
   always @(posedge clk_out) begin
      sh_cl_pcis_rready[0] <= (cl_sh_rd_data.size() < 16) ? 1'b1 : 1'b0;
   end

   always @(posedge clk_out) begin
      AXI_Data data;

      if (cl_sh_pcis_rvalid[0] & sh_cl_pcis_rready) begin
         data.data     = cl_sh_pcis_rdata[0];
         data.id       = cl_sh_pcis_rid[0];
         data.last     = cl_sh_pcis_rlast[0];

         $display("%t - rddata: %h", $time(), cl_sh_pcis_rdata[0]);
         
         cl_sh_rd_data.push_back(data);
      end

   end

   //=================================================
   //
   // cl->sh PCIeM Interface
   //
   //=================================================

   //
   // cl->sh Write Address Channel
   //

   always @(posedge clk_out) begin
      AXI_Command cmd;

      if (cl_sh_pcim_awvalid[0] && sh_cl_pcim_awready[0]) begin
         cmd.addr = cl_sh_pcim_awaddr[0];
         cmd.id   = cl_sh_pcim_awid[0];
         cmd.len  = cl_sh_pcim_awlen[0];

         cl_sh_wr_cmds.push_back(cmd);         
      end

      if (cl_sh_wr_cmds.size() < 4)
        sh_cl_pcim_awready[0] <= 1'b1;
      else
        sh_cl_pcim_awready[0] <= 1'b0;
        
   end


   //
   // cl-sh write Data Channel
   //

   always @(posedge clk_out) begin
      AXI_Data wr_data;
      
      if (sh_cl_pcim_wready[0] && cl_sh_pcim_wvalid[0]) begin
         wr_data.data = cl_sh_pcim_wdata[0];
         wr_data.strb = cl_sh_pcim_wstrb[0];
         wr_data.last = cl_sh_pcim_wlast[0];

         cl_sh_wr_data.push_back(wr_data);
         
      end
      if (cl_sh_wr_data.size() > 64)
        sh_cl_pcim_wready[0] <= 1'b0;
      else
        sh_cl_pcim_wready[0] <= 1'b1;
        
   end
/*
   //
   // cl->sh B Response Channel
   //
   always @(posedge clk_out) begin
      sh_cl_pcis_bready[0] <= 1'b1;
   end

   always @(posedge clk_out) begin
      AXI_Command resp;

      if (cl_sh_pcis_bvalid[0] & sh_cl_pcis_bready) begin
         resp.resp     = cl_sh_pcis_bresp[0];
         resp.id       = cl_sh_pcis_bid[0];

         cl_sh_b_resps.push_back(resp);
      end

   end


   //
   // sh->cl Address Read Channel
   //

   always @(posedge clk_out) begin
      if (sh_cl_rd_cmds.size() != 0) begin

         sh_cl_pcis_araddr[0]  <= sh_cl_rd_cmds[0].addr;
         sh_cl_pcis_arid[0]    <= sh_cl_rd_cmds[0].id;
         sh_cl_pcis_arlen[0]   <= sh_cl_rd_cmds[0].len;
         
         sh_cl_pcis_arvalid[0] <= !sh_cl_pcis_arvalid[0] ? 1'b1 :
                                  !cl_sh_pcis_arready[0] ? 1'b1 : 1'b0;
         
         if (cl_sh_pcis_arready[0] && sh_cl_pcis_arvalid[0]) begin
            $display("%t - debug popping cmd fifo - %d", $time(), sh_cl_rd_cmds.size());
            sh_cl_rd_cmds.pop_front();
         end

      end
      else
         sh_cl_pcis_arvalid <= 1'b0;
   end

   //
   // cl->sh Read Data Channel
   //
   always @(posedge clk_out) begin
      sh_cl_pcis_rready[0] <= (cl_sh_rd_data.size() < 16) ? 1'b1 : 1'b0;
   end

   always @(posedge clk_out) begin
      AXI_Data data;

      if (cl_sh_pcis_rvalid[0] & sh_cl_pcis_rready) begin
         data.data     = cl_sh_pcis_rdata[0];
         data.id       = cl_sh_pcis_rid[0];
         data.last     = cl_sh_pcis_rlast[0];

         $display("%t - rddata: %h", $time(), cl_sh_pcis_rdata[0]);
         
         cl_sh_rd_data.push_back(data);
      end

   end
*/
   
   //==========================================================

   // DDR Controller
   axi4_flop_fifo #(.IN_FIFO(1), .ADDR_WIDTH(64), .DATA_WIDTH(512), .ID_WIDTH(6), .A_USER_WIDTH(1), .FIFO_DEPTH(3)) DDR_3_AXI4_REG_SLC (
     .aclk           (clk_core),
     .aresetn        (sync_rst_n),
     .sync_rst_n     (intf_sync_rst_n),

     .s_axi_awid     (cl_sh_ddr_awid),
     .s_axi_awaddr   (cl_sh_ddr_awaddr),
     .s_axi_awlen    (cl_sh_ddr_awlen),
     .s_axi_awuser   (1'b0),
     .s_axi_awvalid  (cl_sh_ddr_awvalid),
     .s_axi_awready  (sh_cl_ddr_awready),
     .s_axi_wdata    (cl_sh_ddr_wdata),
     .s_axi_wstrb    (cl_sh_ddr_wstrb),
     .s_axi_wlast    (cl_sh_ddr_wlast),
     .s_axi_wvalid   (cl_sh_ddr_wvalid),
     .s_axi_wuser    (),
     .s_axi_wready   (sh_cl_ddr_wready),
     .s_axi_bid      (sh_cl_ddr_bid),
     .s_axi_bresp    (sh_cl_ddr_bresp),
     .s_axi_bvalid   (sh_cl_ddr_bvalid),
     .s_axi_buser    (),
     .s_axi_bready   (cl_sh_ddr_bready),
     .s_axi_arid     (cl_sh_ddr_arid),
     .s_axi_araddr   (cl_sh_ddr_araddr),
     .s_axi_arlen    (cl_sh_ddr_arlen),
     .s_axi_aruser   (1'b0),
     .s_axi_arvalid  (cl_sh_ddr_arvalid),
     .s_axi_arready  (sh_cl_ddr_arready),
     .s_axi_rid      (sh_cl_ddr_rid),
     .s_axi_rdata    (sh_cl_ddr_rdata),
     .s_axi_rresp    (sh_cl_ddr_rresp),
     .s_axi_rlast    (sh_cl_ddr_rlast),
     .s_axi_ruser    (),
     .s_axi_rvalid   (sh_cl_ddr_rvalid),
     .s_axi_rready   (cl_sh_ddr_rready),
  
     .m_axi_awid     (cl_sh_ddr_awid_q),   
     .m_axi_awaddr   (cl_sh_ddr_awaddr_q), 
     .m_axi_awlen    (cl_sh_ddr_awlen_q),  
     .m_axi_awuser   (),
     .m_axi_awvalid  (cl_sh_ddr_awvalid_q),
     .m_axi_awready  (sh_cl_ddr_awready_q),
     .m_axi_wdata    (cl_sh_ddr_wdata_q),  
     .m_axi_wstrb    (cl_sh_ddr_wstrb_q),  
     .m_axi_wuser    (),
     .m_axi_wlast    (cl_sh_ddr_wlast_q),  
     .m_axi_wvalid   (cl_sh_ddr_wvalid_q), 
     .m_axi_wready   (sh_cl_ddr_wready_q), 
     .m_axi_bid      (sh_cl_ddr_bid_q),    
     .m_axi_bresp    (sh_cl_ddr_bresp_q),  
     .m_axi_buser    (),
     .m_axi_bvalid   (sh_cl_ddr_bvalid_q), 
     .m_axi_bready   (cl_sh_ddr_bready_q), 
     .m_axi_arid     (cl_sh_ddr_arid_q),   
     .m_axi_araddr   (cl_sh_ddr_araddr_q), 
     .m_axi_arlen    (cl_sh_ddr_arlen_q),  
     .m_axi_aruser   (),
     .m_axi_arvalid  (cl_sh_ddr_arvalid_q),
     .m_axi_arready  (sh_cl_ddr_arready_q),
     .m_axi_rid      (sh_cl_ddr_rid_q),    
     .m_axi_rdata    (sh_cl_ddr_rdata_q),  
     .m_axi_rresp    (sh_cl_ddr_rresp_q),  
     .m_axi_ruser    (),
     .m_axi_rlast    (sh_cl_ddr_rlast_q),  
     .m_axi_rvalid   (sh_cl_ddr_rvalid_q), 
     .m_axi_rready   (cl_sh_ddr_rready_q)
     );
   
         axi4_ccf #(.ADDR_WIDTH(64), .DATA_WIDTH(512), .ID_WIDTH(6), .A_USER_WIDTH(1), .FIFO_ADDR_WIDTH(3)) DDR4_3_AXI_CCF (
            .s_axi_aclk(clk_core),
            .s_axi_aresetn(rst_n),

            .s_axi_awid(cl_sh_ddr_awid_q),
            .s_axi_awaddr(cl_sh_ddr_awaddr_q),
            .s_axi_awlen(cl_sh_ddr_awlen_q),
            .s_axi_awuser(1'b0),
            .s_axi_awvalid(cl_sh_ddr_awvalid_q),
            .s_axi_awready(sh_cl_ddr_awready_q),

            .s_axi_wdata(cl_sh_ddr_wdata_q),
            .s_axi_wstrb(cl_sh_ddr_wstrb_q),
            .s_axi_wlast(cl_sh_ddr_wlast_q),
            .s_axi_wuser(),
            .s_axi_wvalid(cl_sh_ddr_wvalid_q),
            .s_axi_wready(sh_cl_ddr_wready_q),
   
            .s_axi_bid(sh_cl_ddr_bid_q),
            .s_axi_bresp(sh_cl_ddr_bresp_q),
            .s_axi_buser(),
            .s_axi_bvalid(sh_cl_ddr_bvalid_q),
            .s_axi_bready(cl_sh_ddr_bready_q),

            .s_axi_arid(cl_sh_ddr_arid_q),
            .s_axi_araddr(cl_sh_ddr_araddr_q),
            .s_axi_arlen(cl_sh_ddr_arlen_q),
            .s_axi_aruser(1'b0),
            .s_axi_arvalid(cl_sh_ddr_arvalid_q),
            .s_axi_arready(sh_cl_ddr_arready_q),

            .s_axi_rid(sh_cl_ddr_rid_q),
            .s_axi_rdata(sh_cl_ddr_rdata_q),
            .s_axi_rresp(sh_cl_ddr_rresp_q),
            .s_axi_rlast(sh_cl_ddr_rlast_q),
            .s_axi_ruser(),
            .s_axi_rvalid(sh_cl_ddr_rvalid_q),
            .s_axi_rready(cl_sh_ddr_rready_q),

            .m_axi_aclk(ddr_user_clk),
            .m_axi_aresetn(ddr_user_rst_n),

            .m_axi_awid(sync_cl_sh_ddr_awid),
            .m_axi_awaddr(sync_cl_sh_ddr_awaddr),
            .m_axi_awlen(sync_cl_sh_ddr_awlen),
            .m_axi_awuser(),
            .m_axi_awvalid(sync_cl_sh_ddr_awvalid),
            .m_axi_awready(sync_sh_cl_ddr_awready),

            .m_axi_wdata(sync_cl_sh_ddr_wdata),
            .m_axi_wstrb(sync_cl_sh_ddr_wstrb),
            .m_axi_wlast(sync_cl_sh_ddr_wlast),
            .m_axi_wuser(),
            .m_axi_wvalid(sync_cl_sh_ddr_wvalid),
            .m_axi_wready(sync_sh_cl_ddr_wready),

            .m_axi_bid(sync_sh_cl_ddr_bid),
            .m_axi_bresp(sync_sh_cl_ddr_bresp),
            .m_axi_buser(),
            .m_axi_bvalid(sync_sh_cl_ddr_bvalid),
            .m_axi_bready(sync_cl_sh_ddr_bready),

            .m_axi_arid(sync_cl_sh_ddr_arid),
            .m_axi_araddr(sync_cl_sh_ddr_araddr),
            .m_axi_arlen(sync_cl_sh_ddr_arlen),
            .m_axi_aruser(),
            .m_axi_arvalid(sync_cl_sh_ddr_arvalid),
            .m_axi_arready(sync_sh_cl_ddr_arready),

            .m_axi_rid(sync_sh_cl_ddr_rid),
            .m_axi_rdata(sync_sh_cl_ddr_rdata),
            .m_axi_rresp(sync_sh_cl_ddr_rresp),
            .m_axi_ruser(),
            .m_axi_rlast(sync_sh_cl_ddr_rlast),
            .m_axi_rvalid(sync_sh_cl_ddr_rvalid),
            .m_axi_rready(sync_cl_sh_ddr_rready)
         );

      ddr4_core DDR4_3 (
         .sys_rst(~rst_n),
         .c0_sys_clk_p(CLK_300M_DIMM2_DP),
         .c0_sys_clk_n(CLK_300M_DIMM2_DN),
         .c0_ddr4_act_n(M_C_ACT_N),
         .c0_ddr4_adr(M_C_MA),
         .c0_ddr4_ba(M_C_BA),
         .c0_ddr4_bg(M_C_BG),
         .c0_ddr4_cke(M_C_CKE),
         .c0_ddr4_odt(M_C_ODT),
         .c0_ddr4_cs_n(M_C_CS_N),
         .c0_ddr4_ck_t(M_C_CLK_DP),
         .c0_ddr4_ck_c(M_C_CLK_DN),
         .c0_ddr4_reset_n(RST_DIMM_C_N),
         .c0_ddr4_parity(M_C_PAR),
      
         .c0_ddr4_dq({M_C_DQ[63:32], M_C_ECC, M_C_DQ[31:0]}),
         .c0_ddr4_dqs_t({M_C_DQS_DP[16],M_C_DQS_DP[7], M_C_DQS_DP[15],M_C_DQS_DP[6], M_C_DQS_DP[14], M_C_DQS_DP[5], M_C_DQS_DP[13], M_C_DQS_DP[4], M_C_DQS_DP[17], M_C_DQS_DP[8], M_C_DQS_DP[12], M_C_DQS_DP[3], M_C_DQS_DP[11], M_C_DQS_DP[2], M_C_DQS_DP[10], M_C_DQS_DP[1], M_C_DQS_DP[9], M_C_DQS_DP[0]}),
         .c0_ddr4_dqs_c({M_C_DQS_DN[16],M_C_DQS_DN[7], M_C_DQS_DN[15],M_C_DQS_DN[6], M_C_DQS_DN[14], M_C_DQS_DN[5], M_C_DQS_DN[13], M_C_DQS_DN[4], M_C_DQS_DN[17], M_C_DQS_DN[8], M_C_DQS_DN[12], M_C_DQS_DN[3], M_C_DQS_DN[11], M_C_DQS_DN[2], M_C_DQS_DN[10], M_C_DQS_DN[1], M_C_DQS_DN[9], M_C_DQS_DN[0]}),
      
         .c0_init_calib_complete(ddr_is_ready),
         .c0_ddr4_ui_clk(ddr_user_clk),
         .c0_ddr4_ui_clk_sync_rst(ddr_user_rst),
         .dbg_clk(),                               //No connect
         
         .c0_ddr4_s_axi_ctrl_awvalid(ddr_axl_awvalid),
         .c0_ddr4_s_axi_ctrl_awready(ddr_axl_awready),
         .c0_ddr4_s_axi_ctrl_awaddr(ddr_axl_awaddr),
         .c0_ddr4_s_axi_ctrl_wvalid(ddr_axl_wvalid),
         .c0_ddr4_s_axi_ctrl_wready(ddr_axl_wready),
         .c0_ddr4_s_axi_ctrl_wdata(ddr_axl_wdata),
         .c0_ddr4_s_axi_ctrl_bvalid(ddr_axl_bvalid),
         .c0_ddr4_s_axi_ctrl_bready(ddr_axl_bready),
         .c0_ddr4_s_axi_ctrl_bresp(ddr_axl_bresp),
         .c0_ddr4_s_axi_ctrl_arvalid(ddr_axl_arvalid),
         .c0_ddr4_s_axi_ctrl_arready(ddr_axl_arready),
         .c0_ddr4_s_axi_ctrl_araddr(ddr_axl_araddr),
         .c0_ddr4_s_axi_ctrl_rvalid(ddr_axl_rvalid),
         .c0_ddr4_s_axi_ctrl_rready(ddr_axl_rready),
         .c0_ddr4_s_axi_ctrl_rdata(ddr_axl_rdata),
         .c0_ddr4_s_axi_ctrl_rresp(ddr_axl_rresp),
         .c0_ddr4_interrupt(ddr_axl_interrupt),
         
         .c0_ddr4_aresetn(ddr_user_rst_n),
         
         .c0_ddr4_s_axi_awid(sync_cl_sh_ddr_awid),
         .c0_ddr4_s_axi_awaddr(sync_cl_sh_ddr_awaddr[33:0]),
         .c0_ddr4_s_axi_awlen(sync_cl_sh_ddr_awlen),
         .c0_ddr4_s_axi_awsize(3'h6),
         .c0_ddr4_s_axi_awburst(2'b00),
         .c0_ddr4_s_axi_awlock(1'b0),
         .c0_ddr4_s_axi_awcache(4'h0),    
         .c0_ddr4_s_axi_awprot(3'h0),
         .c0_ddr4_s_axi_awqos(4'h0),
         .c0_ddr4_s_axi_awvalid(sync_cl_sh_ddr_awvalid),
         .c0_ddr4_s_axi_awready(sync_sh_cl_ddr_awready),
         
         .c0_ddr4_s_axi_wdata(sync_cl_sh_ddr_wdata),
         .c0_ddr4_s_axi_wstrb(sync_cl_sh_ddr_wstrb),
         .c0_ddr4_s_axi_wlast(sync_cl_sh_ddr_wlast),
         .c0_ddr4_s_axi_wvalid(sync_cl_sh_ddr_wvalid),
         .c0_ddr4_s_axi_wready(sync_sh_cl_ddr_wready),
         
         .c0_ddr4_s_axi_bready(sync_cl_sh_ddr_bready),
         .c0_ddr4_s_axi_bid(sync_sh_cl_ddr_bid),
         .c0_ddr4_s_axi_bresp(sync_sh_cl_ddr_bresp),
         .c0_ddr4_s_axi_bvalid(sync_sh_cl_ddr_bvalid),
         
         .c0_ddr4_s_axi_arid(sync_cl_sh_ddr_arid),
         .c0_ddr4_s_axi_araddr(sync_cl_sh_ddr_araddr[33:0]),
         .c0_ddr4_s_axi_arlen(sync_cl_sh_ddr_arlen),
         .c0_ddr4_s_axi_arsize(3'h6),
         .c0_ddr4_s_axi_arburst(2'b0),
         .c0_ddr4_s_axi_arlock(1'b0),
         .c0_ddr4_s_axi_arcache(4'h0),
         .c0_ddr4_s_axi_arprot(3'h0),
         .c0_ddr4_s_axi_arqos(4'h0),
         .c0_ddr4_s_axi_arvalid(sync_cl_sh_ddr_arvalid),
         .c0_ddr4_s_axi_arready(sync_sh_cl_ddr_arready),
         
         .c0_ddr4_s_axi_rready(sync_cl_sh_ddr_rready),
         .c0_ddr4_s_axi_rid(sync_sh_cl_ddr_rid),
         .c0_ddr4_s_axi_rdata(sync_sh_cl_ddr_rdata),
         .c0_ddr4_s_axi_rresp(sync_sh_cl_ddr_rresp),
         .c0_ddr4_s_axi_rlast(sync_sh_cl_ddr_rlast),
         .c0_ddr4_s_axi_rvalid(sync_sh_cl_ddr_rvalid),
         .dbg_bus()        //No Connect
         );

        always_ff @(negedge sync_rst_n or posedge clk_core)
          if (!sync_rst_n)
            {sh_cl_ddr_is_ready, ddr_is_ready_sync, ddr_is_ready_presync} <= 3'd0;
          else
            {sh_cl_ddr_is_ready, ddr_is_ready_sync, ddr_is_ready_presync} <= {ddr_is_ready_sync, ddr_is_ready_presync, ddr_is_ready};

   task power_up;
      rst_n_i = 1'b0;
      rst_out_n_i = 1'b0;
      rst_xtra_n_i = 1'b0;
      #5000ns;
      rst_n_i = 1'b1;
      rst_out_n_i = 1'b1;
      rst_xtra_n_i = 1'b1;
      #50ns;
   endtask // power_up
   
   task power_down;
      #50ns;
      rst_n_i = 1'b0;
      rst_out_n_i = 1'b0;
      rst_xtra_n_i = 1'b0;
      #50ns;
   endtask // power_down

   task poke(input logic [63:0] addr, logic [31:0] dat, logic [5:0] id);
      AXI_Command cmd;
      AXI_Data data;
      logic [1:0] resp;
      int         byte_idx;
      int         mem_arr_idx;
      
      cmd.addr = addr;
      cmd.len  = 0;
      cmd.id   = id;

      sh_cl_wr_cmds.push_back(cmd);

      byte_idx     = addr[5:0];
      mem_arr_idx  = byte_idx*8;
      
      data.data[mem_arr_idx+:32] = dat;

      data.strb[byte_idx+:4] = 'h0f;
      
      data.id   = 2;
      data.last = 1'b1;

      #20ns sh_cl_wr_data.push_back(data);
      
      while (cl_sh_b_resps.size() == 0)
        #20ns;
      
      resp = cl_sh_b_resps[0].resp;
      cl_sh_b_resps.pop_front();
      
   endtask // poke

   task peek(input logic [63:0] addr, logic [5:0] id, output [31:0] data);
      AXI_Command cmd;
      int   byte_idx;
      int   mem_arr_idx;
      
      cmd.addr = addr;
      cmd.len  = 0;
      cmd.id   = id;

      sh_cl_rd_cmds.push_back(cmd);

      byte_idx     = addr[5:0];
      mem_arr_idx  = byte_idx*8;

//      wait(cl_sh_rd_data.size() > 0);   // TBD: This doesn't work for XSIM
      while (cl_sh_rd_data.size() == 0)
        #20ns;
      
      data = cl_sh_rd_data[0].data[mem_arr_idx+:32];
      cl_sh_rd_data.pop_front();
      
   endtask // peek

`ifndef NEVER
   
   task poke_burst(input logic [63:0] start_addr, logic [7:0] len, logic [31:0] dat[16]);
      AXI_Command cmd;
      AXI_Data data;
      logic [1:0] resp;
      
      int byte_idx;
      int mem_arr_idx;

 
      cmd.addr = start_addr;
      cmd.len  = len;
      cmd.id   = 1;
      
      sh_cl_wr_cmds.push_back(cmd);

      for (int n= 0; n<len;n++) begin
         byte_idx     = (start_addr[5:0]+(n*'h4));
         mem_arr_idx  = byte_idx*8;

         data.data[mem_arr_idx+:32] = dat[n];
         data.strb[byte_idx+:4] = 'h0f;

         if (n==len-1)
           data.last = 1;
         else
           data.last = 0;
      end

      $display("Write data is %x strb is %x len is %x \n", data.data, data.strb, len);
      
      #20ns sh_cl_wr_data.push_back(data);
      
      while (cl_sh_b_resps.size() == 0)
        #20ns;
      
      resp = cl_sh_b_resps[0].resp;
      cl_sh_b_resps.pop_front();
      
   endtask // poke_burst

   task peek_burst(input logic [63:0] start_addr, logic [7:0] len, output logic [31:0] dat[16]);
      AXI_Command cmd;
      AXI_Data data;
      int byte_idx;
      int mem_arr_idx;
//      int len;

      cmd.addr = start_addr;
      cmd.len  = len;
      cmd.id   = 2;

      sh_cl_rd_cmds.push_back(cmd);

      while (cl_sh_rd_data.size() == 0)
        #20ns;
      
      for (int n= 0; n<len; n++) begin
         byte_idx     = (start_addr[5:0]+(n*'h4));
         mem_arr_idx  = byte_idx*8;
         dat[n] = cl_sh_rd_data[0].data[mem_arr_idx+:32];
      end
      cl_sh_rd_data.pop_front();
      
   endtask // peek_burst

`endif

endmodule // sh_bfm
