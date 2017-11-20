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

module fpga(
            //-----------------------------------------------------------------------------------------------
            // DDR-4 Interface 
            //
            //-----------------------------------------------------------------------------------------------
            
            // ------------------- DDR4 x72 RDIMM 2100 Interface A ----------------------------------
            input                CLK_300M_DIMM0_DP,
            input                CLK_300M_DIMM0_DN,
            output               M_A_ACT_N,
            output [16:0]        M_A_MA,
            output [1:0]         M_A_BA,
            output [1:0]         M_A_BG,
            output [0:0]         M_A_CKE,
            output [0:0]         M_A_ODT,
            output [0:0]         M_A_CS_N,
            output [0:0]         M_A_CLK_DN,
            output [0:0]         M_A_CLK_DP,
            output               RST_DIMM_A_N,
            output               M_A_PAR,
            inout  [63:0]        M_A_DQ,
            inout  [7:0]         M_A_ECC,
            inout  [17:0]        M_A_DQS_DP,
            inout  [17:0]        M_A_DQS_DN,
            output               cl_RST_DIMM_A_N,
            
            // ------------------- DDR4 x72 RDIMM 2100 Interface B ----------------------------------
            input                CLK_300M_DIMM1_DP,
            input                CLK_300M_DIMM1_DN,
            output               M_B_ACT_N,
            output [16:0]        M_B_MA,
            output [1:0]         M_B_BA,
            output [1:0]         M_B_BG,
            output [0:0]         M_B_CKE,
            output [0:0]         M_B_ODT,
            output [0:0]         M_B_CS_N,
            output [0:0]         M_B_CLK_DN,
            output [0:0]         M_B_CLK_DP,
            output               RST_DIMM_B_N,
            output               M_B_PAR,
            inout  [63:0]        M_B_DQ,
            inout  [7:0]         M_B_ECC,
            inout  [17:0]        M_B_DQS_DP,
            inout  [17:0]        M_B_DQS_DN,
            output               cl_RST_DIMM_B_N,
            
            // ------------------- DDR4 x72 RDIMM 2100 Interface C ----------------------------------
            
            input                CLK_300M_DIMM2_DP,
            input                CLK_300M_DIMM2_DN,
            output logic         M_C_ACT_N,
            output logic [16:0]  M_C_MA,
            output logic [1:0]   M_C_BA,
            output logic [1:0]   M_C_BG,
            output logic [0:0]   M_C_CKE,
            output logic [0:0]   M_C_ODT,
            output logic [0:0]   M_C_CS_N,
            output logic [0:0]   M_C_CLK_DN,
            output logic [0:0]   M_C_CLK_DP,
            output logic         RST_DIMM_C_N,
            output logic         M_C_PAR,
            inout [63:0]         M_C_DQ,
            inout [7:0]          M_C_ECC,
            inout [17:0]         M_C_DQS_DP,
            inout [17:0]         M_C_DQS_DN,
           
            // ------------------- DDR4 x72 RDIMM 2100 Interface D ----------------------------------
            input                CLK_300M_DIMM3_DP,
            input                CLK_300M_DIMM3_DN,
            output               M_D_ACT_N,
            output [16:0]        M_D_MA,
            output [1:0]         M_D_BA,
            output [1:0]         M_D_BG,
            output [0:0]         M_D_CKE,
            output [0:0]         M_D_ODT,
            output [0:0]         M_D_CS_N,
            output [0:0]         M_D_CLK_DN,
            output [0:0]         M_D_CLK_DP,
            output               RST_DIMM_D_N,
            output               M_D_PAR,
            inout  [63:0]        M_D_DQ,
            inout  [7:0]         M_D_ECC,
            inout  [17:0]        M_D_DQS_DP,
            inout  [17:0]        M_D_DQS_DN,
            output               cl_RST_DIMM_D_N
            
            );

   // PCIe IDs
   logic [31:0] cl_sh_id0;
   logic [31:0] cl_sh_id1;
      
   // General Control/Status
   logic [31:0] cl_sh_status0;
   logic [31:0] cl_sh_status1;
   logic [31:0] sh_cl_ctl0;
   logic [31:0] sh_cl_ctl1;
   logic [1:0]  sh_cl_pwr_state;

   //------------------------------------------------------
   // DDR-4 Interface from CL to SH (AXI-4)
   //------------------------------------------------------
   logic [15:0] cl_sh_ddr_awid;
   logic [63:0] cl_sh_ddr_awaddr;
   logic [7:0]  cl_sh_ddr_awlen;

   logic        cl_sh_ddr_awvalid;
   logic        sh_cl_ddr_awready;
   
   logic [15:0] cl_sh_ddr_wid;
   logic [511:0] cl_sh_ddr_wdata;
   logic [63:0]  cl_sh_ddr_wstrb;
   logic         cl_sh_ddr_wlast;
   logic         cl_sh_ddr_wvalid;
   logic         sh_cl_ddr_wready;
   
   logic [15:0]  sh_cl_ddr_bid;
   logic [1:0]   sh_cl_ddr_bresp;
   logic         sh_cl_ddr_bvalid;
   logic         cl_sh_ddr_bready;
   
   logic [15:0]  cl_sh_ddr_arid;
   logic [63:0]  cl_sh_ddr_araddr;
   logic [7:0]   cl_sh_ddr_arlen;
   
   logic         cl_sh_ddr_arvalid;
   logic         sh_cl_ddr_arready;
   
   logic [15:0]  sh_cl_ddr_rid;
   logic [511:0] sh_cl_ddr_rdata;
   logic [1:0]   sh_cl_ddr_rresp;
   logic         sh_cl_ddr_rlast;
   logic         sh_cl_ddr_rvalid;
   logic         cl_sh_ddr_rready;
   
   logic         clk_main_a0;
   logic         clk_extra_a1;
   logic         clk_extra_a2;
   logic         clk_extra_a3;
   logic         clk_extra_b0;
   logic         clk_extra_b1;
   logic         clk_extra_c0;
   logic         clk_extra_c1;

   logic         rst_main_n;
   logic         kernel_rst_n;
         
   logic         sh_cl_flr_assert;
   logic         cl_sh_flr_done;
   
   logic [1:0]   cfg_max_payload;               //Max payload size - 00:128B, 01:256B, 10:512B
   logic [2:0]   cfg_max_read_req;              //Max read requst size - 000b:128B, 001b:256B, 010b:512B, 011b:1024B
                                                // 100b-2048B, 101b:4096B
   logic [15:0]  sh_cl_status_vdip;             //Virtual DIP switches.  Controlled through FPGA management PF and tools.
   logic [15:0]  cl_sh_status_vled;             //Virtual LEDs, monitored through FPGA management PF and tools


   //-------------------------------------
   // PCIe Master interface from CL
   //-------------------------------------
   logic [15:0]          cl_sh_pcim_awid;
   logic [63:0]         cl_sh_pcim_awaddr;
   logic [7:0]          cl_sh_pcim_awlen;
   logic [2:0]          cl_sh_pcim_awsize;
   logic [18:0]         cl_sh_pcim_awuser;
   logic                cl_sh_pcim_awvalid;
   logic                sh_cl_pcim_awready;
   
   logic [511:0]        cl_sh_pcim_wdata;
   logic [63:0]         cl_sh_pcim_wstrb;
   logic                cl_sh_pcim_wlast;
   logic                cl_sh_pcim_wvalid;
   logic                sh_cl_pcim_wready;
   
   logic [15:0]          sh_cl_pcim_bid;
   logic [1:0]          sh_cl_pcim_bresp;
   logic                sh_cl_pcim_bvalid;
   logic                cl_sh_pcim_bready;
   
   logic [15:0]          cl_sh_pcim_arid ;
   logic [63:0]         cl_sh_pcim_araddr;
   logic [7:0]          cl_sh_pcim_arlen ;
   logic [2:0]          cl_sh_pcim_arsize ;
   logic [18:0]         cl_sh_pcim_aruser;
   logic                cl_sh_pcim_arvalid;
   logic                sh_cl_pcim_arready;
   
   logic [15:0]          sh_cl_pcim_rid ;
   logic [511:0]        sh_cl_pcim_rdata;
   logic [1:0]          sh_cl_pcim_rresp;
   logic                sh_cl_pcim_rlast;
   logic                sh_cl_pcim_rvalid;
   logic                cl_sh_pcim_rready;

   //------------------------------------------------
   // PCI Slave interface to CL
   //------------------------------------------------
   logic [63:0]         sh_cl_dma_pcis_awaddr;
   logic [5:0]          sh_cl_dma_pcis_awid;
   logic [7:0]          sh_cl_dma_pcis_awlen;
   logic [2:0]          sh_cl_dma_pcis_awsize;
   logic                sh_cl_dma_pcis_awvalid;
   logic                cl_sh_dma_pcis_awready;

   logic [511:0]        sh_cl_dma_pcis_wdata;
   logic [63:0]         sh_cl_dma_pcis_wstrb;
   logic                sh_cl_dma_pcis_wlast;
   logic                sh_cl_dma_pcis_wvalid;
   logic                cl_sh_dma_pcis_wready;
   
   logic [1:0]          cl_sh_dma_pcis_bresp;
   logic [5:0]          cl_sh_dma_pcis_bid;
   logic                cl_sh_dma_pcis_bvalid;
   logic                sh_cl_dma_pcis_bready;
   
   logic [63:0]         sh_cl_dma_pcis_araddr;
   logic [5:0]          sh_cl_dma_pcis_arid;
   logic [7:0]          sh_cl_dma_pcis_arlen;
   logic [2:0]          sh_cl_dma_pcis_arsize;
   logic                sh_cl_dma_pcis_arvalid;
   logic                cl_sh_dma_pcis_arready;
   
   logic [5:0]          cl_sh_dma_pcis_rid;
   logic [511:0]        cl_sh_dma_pcis_rdata;
   logic [1:0]          cl_sh_dma_pcis_rresp;
   logic                cl_sh_dma_pcis_rlast;
   logic                cl_sh_dma_pcis_rvalid;
   logic                sh_cl_dma_pcis_rready;

   //--------------------------------------------
   // DDR4 Status Interface
   //--------------------------------------------

   logic                sh_cl_ddr_is_ready;
   logic [7:0]          sh_ddr_stat_addr[2:0];
   logic [2:0]          sh_ddr_stat_wr;
   logic [2:0]          sh_ddr_stat_rd;
   logic [31:0]         sh_ddr_stat_wdata[2:0];
   logic [2:0]          ddr_sh_stat_ack;
   logic [31:0]         ddr_sh_stat_rdata[2:0];
   logic [7:0]          ddr_sh_stat_int[2:0];
  
   //--------------------------------------------
   // SDA
   //--------------------------------------------

   logic               sda_cl_awvalid;
   logic [31:0]        sda_cl_awaddr; 
   logic               cl_sda_awready;

   //Write data
   logic               sda_cl_wvalid;
   logic [31:0]        sda_cl_wdata;
   logic [3:0]         sda_cl_wstrb;
   logic               cl_sda_wready;

   //Write response
   logic               cl_sda_bvalid;
   logic [1:0]         cl_sda_bresp;
   logic               sda_cl_bready;

   //Read address
   logic               sda_cl_arvalid;
   logic [31:0]        sda_cl_araddr;
   logic               cl_sda_arready;

   //Read data/response
   logic               cl_sda_rvalid;
   logic [31:0]        cl_sda_rdata;
   logic [1:0]         cl_sda_rresp;

   logic               sda_cl_rready;


   //--------------------------------------------
   // OCL
   //--------------------------------------------

   logic               sh_ocl_awvalid;
   logic [31:0]        sh_ocl_awaddr; 
   logic               ocl_sh_awready;

   //Write data
   logic               sh_ocl_wvalid;
   logic [31:0]        sh_ocl_wdata;
   logic [3:0]         sh_ocl_wstrb;
   logic               ocl_sh_wready;

   //Write response
   logic               ocl_cl_bvalid;
   logic [1:0]         ocl_cl_bresp;
   logic               sh_ocl_bready;
   logic [1:0]         ocl_sh_bresp;

   //Read address
   logic               sh_ocl_arvalid;
   logic [31:0]        sh_ocl_araddr;
   logic               ocl_sh_arready;

   //Read data/response
   logic               ocl_sh_rvalid;
   logic [31:0]        ocl_sh_rdata;
   logic [1:0]         ocl_sh_rresp;

   logic               sh_ocl_rready;


   //--------------------------------------------
   // BAR1
   //--------------------------------------------

   logic               sh_bar1_awvalid;
   logic [31:0]        sh_bar1_awaddr; 
   logic               bar1_sh_awready;

   //Write data
   logic               sh_bar1_wvalid;
   logic [31:0]        sh_bar1_wdata;
   logic [3:0]         sh_bar1_wstrb;
   logic               bar1_sh_wready;

   //Write response
   logic               bar1_sh_bvalid;
   logic [1:0]         bar1_sh_bresp;
   logic               sh_bar1_bready;

   //Read address
   logic               sh_bar1_arvalid;
   logic [31:0]        sh_bar1_araddr;
   logic               bar1_sh_arready;

   //Read data/response
   logic               bar1_sh_rvalid;
   logic [31:0]        bar1_sh_rdata;
   logic [1:0]         bar1_sh_rresp;

   logic               sh_bar1_rready;

   logic [15:0]        cl_sh_apppf_irq_req;
   logic [15:0]        sh_cl_apppf_irq_ack;

   sh_bfm sh(

             .cl_sh_status0(cl_sh_status0),
             .cl_sh_status1(cl_sh_status1),
             .cl_sh_id0(cl_sh_id0),
             .cl_sh_id1(cl_sh_id1),

             .sh_cl_ctl0(sh_cl_ctl0),
             .sh_cl_ctl1(sh_cl_ctl1),

             .clk_main_a0(clk_main_a0),
             .clk_extra_a1(clk_extra_a1),
             .clk_extra_a2(clk_extra_a2),
             .clk_extra_a3(clk_extra_a3),
             
             .clk_extra_b0(clk_extra_b0),
             .clk_extra_b1(clk_extra_b1),
             
             .clk_extra_c0(clk_extra_c0),
             .clk_extra_c1(clk_extra_c1),
             
             .rst_main_n(rst_main_n),
             .kernel_rst_n(kernel_rst_n),
             
             .sh_cl_pwr_state(sh_cl_pwr_state),
             
             .sh_cl_status_vdip(sh_cl_status_vdip),
             .cl_sh_status_vled(cl_sh_status_vled),
             
             //------------------------
             // PCI Express
             //------------------------
             .sh_cl_flr_assert(sh_cl_flr_assert),
             .cl_sh_flr_done(cl_sh_flr_done),
             
             //-------------------------------   
             // HMC
             //-------------------------------   
      //     .hmc_iic_scl_i(hmc_iic_scl_i),
      //     .hmc_iic_scl_o(hmc_iic_scl_o),
      //     .hmc_iic_scl_t(hmc_iic_scl_t),
      //     .hmc_iic_sda_i(hmc_iic_sda_i),
      //     .hmc_iic_sda_o(hmc_iic_sda_o),
      //     .hmc_iic_sda_t(hmc_iic_sda_t),
      //     
      //     .sh_hmc_stat_addr(sh_hmc_stat_addr),
      //     .sh_hmc_stat_wr(sh_hmc_stat_wr),
      //     .sh_hmc_stat_rd(sh_hmc_stat_rd),
      //     .sh_hmc_stat_wdata(sh_hmc_stat_wdata),
      //     .hmc_sh_stat_ack(hmc_sh_stat_ack),
      //     .hmc_sh_stat_rdata(hmc_sh_stat_rdata),
      //     .hmc_sh_stat_int(hmc_sh_stat_int),  
             
             //-------------------------------------
             // PCIe Interface from CL (AXI-4) (CL is PCI-master)
             //-------------------------------------
             .cl_sh_pcim_awid(cl_sh_pcim_awid),
             .cl_sh_pcim_awaddr(cl_sh_pcim_awaddr),
             .cl_sh_pcim_awlen(cl_sh_pcim_awlen),
             .cl_sh_pcim_awsize(cl_sh_pcim_awsize),
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
             .cl_sh_pcim_arsize(cl_sh_pcim_arsize),
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
             .cfg_max_read_req(cfg_max_read_req),             //Max read requst size - 000b:128B, 001b:256B, 010b:512B, 011b:1024B
                                                              // 100b-2048B, 101b:4096B

             //-------------------------------------
             // PCIe Interface to CL (AXI-4) (CL is PCI-slave)
             //-------------------------------------
             .sh_cl_dma_pcis_awaddr(sh_cl_dma_pcis_awaddr),
             .sh_cl_dma_pcis_awid(sh_cl_dma_pcis_awid),
             .sh_cl_dma_pcis_awlen(sh_cl_dma_pcis_awlen),
             .sh_cl_dma_pcis_awsize(sh_cl_dma_pcis_awsize),
             .sh_cl_dma_pcis_awvalid(sh_cl_dma_pcis_awvalid),
             .cl_sh_dma_pcis_awready(cl_sh_dma_pcis_awready),
             
             .sh_cl_dma_pcis_wdata(sh_cl_dma_pcis_wdata),
             .sh_cl_dma_pcis_wstrb(sh_cl_dma_pcis_wstrb),
             .sh_cl_dma_pcis_wvalid(sh_cl_dma_pcis_wvalid),
             .sh_cl_dma_pcis_wlast(sh_cl_dma_pcis_wlast),
             .cl_sh_dma_pcis_wready(cl_sh_dma_pcis_wready),
             
             .cl_sh_dma_pcis_bresp(cl_sh_dma_pcis_bresp),
             .cl_sh_dma_pcis_bvalid(cl_sh_dma_pcis_bvalid),
             .cl_sh_dma_pcis_bid(cl_sh_dma_pcis_bid),
             .sh_cl_dma_pcis_bready(sh_cl_dma_pcis_bready),
             
             .sh_cl_dma_pcis_araddr(sh_cl_dma_pcis_araddr),
             .sh_cl_dma_pcis_arid(sh_cl_dma_pcis_arid),
             .sh_cl_dma_pcis_arlen(sh_cl_dma_pcis_arlen),
             .sh_cl_dma_pcis_arsize(sh_cl_dma_pcis_arsize),
             .sh_cl_dma_pcis_arvalid(sh_cl_dma_pcis_arvalid),
             .cl_sh_dma_pcis_arready(cl_sh_dma_pcis_arready),
             
             .cl_sh_dma_pcis_rid(cl_sh_dma_pcis_rid),
             .cl_sh_dma_pcis_rdata(cl_sh_dma_pcis_rdata),
             .cl_sh_dma_pcis_rresp(cl_sh_dma_pcis_rresp),
             .cl_sh_dma_pcis_rlast(cl_sh_dma_pcis_rlast),
             .cl_sh_dma_pcis_rvalid(cl_sh_dma_pcis_rvalid),
             .sh_cl_dma_pcis_rready(sh_cl_dma_pcis_rready),

             //-----------------------------------------
             // CL INTERRUPTS
             //-----------------------------------------
             .cl_sh_apppf_irq_req(cl_sh_apppf_irq_req),
             .sh_cl_apppf_irq_ack(sh_cl_apppf_irq_ack),

    `ifdef AURORA
             .cl_sh_aurora_channel_up(),
    `endif

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
             .sh_ddr_stat_addr0(sh_ddr_stat_addr[0]),
             .sh_ddr_stat_wr0(sh_ddr_stat_wr[0]),
             .sh_ddr_stat_rd0(sh_ddr_stat_rd[0]),
             .sh_ddr_stat_wdata0(sh_ddr_stat_wdata[0]),
             
             .ddr_sh_stat_ack0(ddr_sh_stat_ack[0]),
             .ddr_sh_stat_rdata0(ddr_sh_stat_rdata[0]),
             .ddr_sh_stat_int0(ddr_sh_stat_int[0]),
             
             .sh_ddr_stat_addr1(sh_ddr_stat_addr[1]),
             .sh_ddr_stat_wr1(sh_ddr_stat_wr[1]),
             .sh_ddr_stat_rd1(sh_ddr_stat_rd[1]),
             .sh_ddr_stat_wdata1(sh_ddr_stat_wdata[1]),
             
             .ddr_sh_stat_ack1(ddr_sh_stat_ack[1]),
             .ddr_sh_stat_rdata1(ddr_sh_stat_rdata[1]),
             .ddr_sh_stat_int1(ddr_sh_stat_int[1]),
             
             .sh_ddr_stat_addr2(sh_ddr_stat_addr[2]),
             .sh_ddr_stat_wr2(sh_ddr_stat_wr[2]),
             .sh_ddr_stat_rd2(sh_ddr_stat_rd[2]),
             .sh_ddr_stat_wdata2(sh_ddr_stat_wdata[2]),
             
             .ddr_sh_stat_ack2(ddr_sh_stat_ack[2]),
             .ddr_sh_stat_rdata2(ddr_sh_stat_rdata[2]),
             .ddr_sh_stat_int2(ddr_sh_stat_int[2]),
             
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
             
             .sda_cl_awvalid(sda_cl_awvalid),
             .sda_cl_awaddr(sda_cl_awaddr), 
             .cl_sda_awready(cl_sda_awready),
             
             //Write data
             .sda_cl_wvalid(sda_cl_wvalid),
             .sda_cl_wdata(sda_cl_wdata),
             .sda_cl_wstrb(sda_cl_wstrb),
             .cl_sda_wready(cl_sda_wready),
             
             //Write response
             .cl_sda_bvalid(cl_sda_bvalid),
             .cl_sda_bresp(cl_sda_bresp),
             .sda_cl_bready(sda_cl_bready),
             
             //Read address
             .sda_cl_arvalid(sda_cl_arvalid),
             .sda_cl_araddr(sda_cl_araddr),
             .cl_sda_arready(cl_sda_arready),
             
             //Read data/response
             .cl_sda_rvalid(cl_sda_rvalid),
             .cl_sda_rdata(cl_sda_rdata),
             .cl_sda_rresp(cl_sda_rresp),
             
             .sda_cl_rready(sda_cl_rready),
             
             .sh_ocl_awvalid(sh_ocl_awvalid),
             .sh_ocl_awaddr(sh_ocl_awaddr), 
             .ocl_sh_awready(ocl_sh_awready),

             //Write data
             .sh_ocl_wvalid(sh_ocl_wvalid),
             .sh_ocl_wdata(sh_ocl_wdata),
             .sh_ocl_wstrb(sh_ocl_wstrb),
             .ocl_sh_wready(ocl_sh_wready),
             
             //Write response
             .ocl_sh_bvalid(ocl_sh_bvalid),
             .ocl_sh_bresp(ocl_sh_bresp),
             .sh_ocl_bready(sh_ocl_bready),
             
             //Read address
             .sh_ocl_arvalid(sh_ocl_arvalid),
             .sh_ocl_araddr(sh_ocl_araddr),
             .ocl_sh_arready(ocl_sh_arready),
             
             //Read data/response
             .ocl_sh_rvalid(ocl_sh_rvalid),
             .ocl_sh_rdata(ocl_sh_rdata),
             .ocl_sh_rresp(ocl_sh_rresp),
             
             .sh_ocl_rready(sh_ocl_rready),
             
             .sh_bar1_awvalid(sh_bar1_awvalid),
             .sh_bar1_awaddr(sh_bar1_awaddr), 
             .bar1_sh_awready(bar1_sh_awready),
             
             //Write data
             .sh_bar1_wvalid(sh_bar1_wvalid),
             .sh_bar1_wdata(sh_bar1_wdata),
             .sh_bar1_wstrb(sh_bar1_wstrb),
             .bar1_sh_wready(bar1_sh_wready),
             
             //Write response
             .bar1_sh_bvalid(bar1_sh_bvalid),
             .bar1_sh_bresp(bar1_sh_bresp),
             .sh_bar1_bready(sh_bar1_bready),
             
             //Read address
             .sh_bar1_arvalid(sh_bar1_arvalid),
             .sh_bar1_araddr(sh_bar1_araddr),
             .bar1_sh_arready(bar1_sh_arready),
             
             //Read data/response
             .bar1_sh_rvalid(bar1_sh_rvalid),
             .bar1_sh_rdata(bar1_sh_rdata),
             .bar1_sh_rresp(bar1_sh_rresp),
             
             .sh_bar1_rready(sh_bar1_rready)
`ifndef NO_CL_DDR
             ,
             .sh_RST_DIMM_A_N(RST_DIMM_A_N),
             .sh_RST_DIMM_B_N(RST_DIMM_B_N),
             .sh_RST_DIMM_D_N(RST_DIMM_D_N)
`endif
             );

`ifndef CL_NAME
 `define CL_NAME cl_dram_dma
`endif

   //Developer put top level here (replace cl_simple, with top level)
   `CL_NAME CL 
             (
              .clk_main_a0(clk_main_a0),
              .clk_extra_a1(clk_extra_a1),
              .clk_extra_a2(clk_extra_a2),
              .clk_extra_a3(clk_extra_a3),
              
              .clk_extra_b0(clk_extra_b0),
              .clk_extra_b1(clk_extra_b1),
   
              .clk_extra_c0(clk_extra_c0),
              .clk_extra_c1(clk_extra_c1),
          
              .rst_main_n(rst_main_n),
              .kernel_rst_n(kernel_rst_n),

              .sh_cl_pwr_state(sh_cl_pwr_state),

              .sh_cl_status_vdip(sh_cl_status_vdip),
              .cl_sh_status_vled(cl_sh_status_vled),
              
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
              
              .sh_cl_dma_pcis_awaddr(sh_cl_dma_pcis_awaddr),
              .sh_cl_dma_pcis_awid(sh_cl_dma_pcis_awid),
              .sh_cl_dma_pcis_awlen(sh_cl_dma_pcis_awlen),
              .sh_cl_dma_pcis_awsize(sh_cl_dma_pcis_awsize),
              .sh_cl_dma_pcis_awvalid(sh_cl_dma_pcis_awvalid),
              .cl_sh_dma_pcis_awready(cl_sh_dma_pcis_awready),
              
              .sh_cl_dma_pcis_wdata(sh_cl_dma_pcis_wdata),
              .sh_cl_dma_pcis_wstrb(sh_cl_dma_pcis_wstrb),
              .sh_cl_dma_pcis_wlast(sh_cl_dma_pcis_wlast),
              .sh_cl_dma_pcis_wvalid(sh_cl_dma_pcis_wvalid),
              .cl_sh_dma_pcis_wready(cl_sh_dma_pcis_wready),
   
              .cl_sh_dma_pcis_bresp(cl_sh_dma_pcis_bresp),
              .cl_sh_dma_pcis_bid(cl_sh_dma_pcis_bid),
              .cl_sh_dma_pcis_bvalid(cl_sh_dma_pcis_bvalid),
              .sh_cl_dma_pcis_bready(sh_cl_dma_pcis_bready),
              
              .sh_cl_dma_pcis_araddr(sh_cl_dma_pcis_araddr),
              .sh_cl_dma_pcis_arid(sh_cl_dma_pcis_arid),
              .sh_cl_dma_pcis_arlen(sh_cl_dma_pcis_arlen),
              .sh_cl_dma_pcis_arsize(sh_cl_dma_pcis_arsize),
              .sh_cl_dma_pcis_arvalid(sh_cl_dma_pcis_arvalid),
              .cl_sh_dma_pcis_arready(cl_sh_dma_pcis_arready),
   
              .cl_sh_dma_pcis_rid(cl_sh_dma_pcis_rid),
              .cl_sh_dma_pcis_rdata(cl_sh_dma_pcis_rdata),
              .cl_sh_dma_pcis_rresp(cl_sh_dma_pcis_rresp),
              .cl_sh_dma_pcis_rlast(cl_sh_dma_pcis_rlast),
              .cl_sh_dma_pcis_rvalid(cl_sh_dma_pcis_rvalid),
              .sh_cl_dma_pcis_rready(sh_cl_dma_pcis_rready),
   
              .cl_sh_pcim_awid(cl_sh_pcim_awid),
              .cl_sh_pcim_awaddr(cl_sh_pcim_awaddr),
              .cl_sh_pcim_awlen(cl_sh_pcim_awlen),
              .cl_sh_pcim_awsize(cl_sh_pcim_awsize),
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
              .cl_sh_pcim_arsize(cl_sh_pcim_arsize),
              .cl_sh_pcim_aruser(cl_sh_pcim_aruser),
              .cl_sh_pcim_arvalid(cl_sh_pcim_arvalid),
              .sh_cl_pcim_arready(sh_cl_pcim_arready),
   
              .sh_cl_pcim_rid(sh_cl_pcim_rid),
              .sh_cl_pcim_rdata(sh_cl_pcim_rdata),
              .sh_cl_pcim_rresp(sh_cl_pcim_rresp),
              .sh_cl_pcim_rlast(sh_cl_pcim_rlast),
              .sh_cl_pcim_rvalid(sh_cl_pcim_rvalid),
              .cl_sh_pcim_rready(cl_sh_pcim_rready),
                                                                                                
              .sda_cl_awvalid(sda_cl_awvalid),
              .sda_cl_awaddr(sda_cl_awaddr), 
              .cl_sda_awready(cl_sda_awready),

              //Write data
              .sda_cl_wvalid(sda_cl_wvalid),
              .sda_cl_wdata(sda_cl_wdata),
              .sda_cl_wstrb(sda_cl_wstrb),
              .cl_sda_wready(cl_sda_wready),

              //Write response
              .cl_sda_bvalid(cl_sda_bvalid),
              .cl_sda_bresp(cl_sda_bresp),
              .sda_cl_bready(sda_cl_bready),
              
              //Read address
              .sda_cl_arvalid(sda_cl_arvalid),
              .sda_cl_araddr(sda_cl_araddr),
              .cl_sda_arready(cl_sda_arready),

              //Read data/response
              .cl_sda_rvalid(cl_sda_rvalid),
              .cl_sda_rdata(cl_sda_rdata),
              .cl_sda_rresp(cl_sda_rresp),
              .sda_cl_rready(sda_cl_rready),

              .sh_ocl_awvalid(sh_ocl_awvalid),
              .sh_ocl_awaddr(sh_ocl_awaddr), 
              .ocl_sh_awready(ocl_sh_awready),
              
              //Write data
              .sh_ocl_wvalid(sh_ocl_wvalid),
              .sh_ocl_wdata(sh_ocl_wdata),
              .sh_ocl_wstrb(sh_ocl_wstrb),
              .ocl_sh_wready(ocl_sh_wready),
              
              //Write response
              .ocl_sh_bvalid(ocl_sh_bvalid),
              .ocl_sh_bresp(ocl_sh_bresp),
              .sh_ocl_bready(sh_ocl_bready),

              //Read address
              .sh_ocl_arvalid(sh_ocl_arvalid),
              .sh_ocl_araddr(sh_ocl_araddr),
              .ocl_sh_arready(ocl_sh_arready),

              //Read data/response
              .ocl_sh_rvalid(ocl_sh_rvalid),
              .ocl_sh_rdata(ocl_sh_rdata),
              .ocl_sh_rresp(ocl_sh_rresp),
              .sh_ocl_rready(sh_ocl_rready),

              .sh_bar1_awvalid(sh_bar1_awvalid),
              .sh_bar1_awaddr(sh_bar1_awaddr), 
              .bar1_sh_awready(bar1_sh_awready),
              
              //Write data
              .sh_bar1_wvalid(sh_bar1_wvalid),
              .sh_bar1_wdata(sh_bar1_wdata),
              .sh_bar1_wstrb(sh_bar1_wstrb),
              .bar1_sh_wready(bar1_sh_wready),

              //Write response
              .bar1_sh_bvalid(bar1_sh_bvalid),
              .bar1_sh_bresp(bar1_sh_bresp),
              .sh_bar1_bready(sh_bar1_bready),

              //Read address
              .sh_bar1_arvalid(sh_bar1_arvalid),
              .sh_bar1_araddr(sh_bar1_araddr),
              .bar1_sh_arready(bar1_sh_arready),

              //Read data/response
              .bar1_sh_rvalid(bar1_sh_rvalid),
              .bar1_sh_rdata(bar1_sh_rdata),
              .bar1_sh_rresp(bar1_sh_rresp),
              
              .sh_bar1_rready(sh_bar1_rready),
`ifndef NO_CL_DDR              
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
`endif //  `ifndef NO_CL_DDR
              .sh_ddr_stat_addr0(sh_ddr_stat_addr[0]),
              .sh_ddr_stat_wr0(sh_ddr_stat_wr[0]),
              .sh_ddr_stat_rd0(sh_ddr_stat_rd[0]),
              .sh_ddr_stat_wdata0(sh_ddr_stat_wdata[0]),
              
              .ddr_sh_stat_ack0(ddr_sh_stat_ack[0]),
              .ddr_sh_stat_rdata0(ddr_sh_stat_rdata[0]),
              .ddr_sh_stat_int0(ddr_sh_stat_int[0]),
              
              .sh_ddr_stat_addr1(sh_ddr_stat_addr[1]),
              .sh_ddr_stat_wr1(sh_ddr_stat_wr[1]),
              .sh_ddr_stat_rd1(sh_ddr_stat_rd[1]),
              .sh_ddr_stat_wdata1(sh_ddr_stat_wdata[1]),

              .ddr_sh_stat_ack1(ddr_sh_stat_ack[1]),
              .ddr_sh_stat_rdata1(ddr_sh_stat_rdata[1]),
              .ddr_sh_stat_int1(ddr_sh_stat_int[1]),
              
              .sh_ddr_stat_addr2(sh_ddr_stat_addr[2]),
              .sh_ddr_stat_wr2(sh_ddr_stat_wr[2]),
              .sh_ddr_stat_rd2(sh_ddr_stat_rd[2]),
              .sh_ddr_stat_wdata2(sh_ddr_stat_wdata[2]),

              .ddr_sh_stat_ack2(ddr_sh_stat_ack[2]),
              .ddr_sh_stat_rdata2(ddr_sh_stat_rdata[2]),
              .ddr_sh_stat_int2(ddr_sh_stat_int[2]),

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

              .cl_sh_apppf_irq_req(cl_sh_apppf_irq_req),
              .sh_cl_apppf_irq_ack(sh_cl_apppf_irq_ack)

`ifdef ENABLE_CS_DEBUG
              ,
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
              .bscanid(bscanid)
`endif
              );
   
endmodule // fpga
