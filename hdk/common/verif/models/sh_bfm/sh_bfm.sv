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

   output logic [31:0]         sh_cl_ctl0,
   output logic [31:0]         sh_cl_ctl1,
   output logic [1:0]          sh_cl_pwr_state,

   output logic                clk_main_a0,
   output logic                clk_extra_a1,
   output logic                clk_extra_a2,
   output logic                clk_extra_a3,
   
   output logic                clk_extra_b0,
   output logic                clk_extra_b1,
   
   output logic                clk_extra_c0,
   output logic                clk_extra_c1,
    
   output logic                rst_main_n,
   output logic                kernel_rst_n,
    
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

   output logic [7:0]         sh_hmc_stat_addr,
   output logic               sh_hmc_stat_wr,
   output logic               sh_hmc_stat_rd,
   output logic [31:0]        sh_hmc_stat_wdata,

   input                      hmc_sh_stat_ack,
   input [31:0]               hmc_sh_stat_rdata,

   input [7:0]                hmc_sh_stat_int

    
   ,
   //-------------------------------------
   // PCIe Interface from CL (AXI-4) (CL is PCI-master)
   //-------------------------------------
   input [15:0]                 cl_sh_pcim_awid  ,
   input [63:0]                 cl_sh_pcim_awaddr,
   input [7:0]                  cl_sh_pcim_awlen ,
   input [2:0]                  cl_sh_pcim_awsize ,
   input [18:0]                 cl_sh_pcim_awuser, //DW length of transfer
   input [NUM_PCIE-1:0]         cl_sh_pcim_awvalid,
   output logic [NUM_PCIE-1:0]  sh_cl_pcim_awready,

   input [511:0]                cl_sh_pcim_wdata,
   input [63:0]                 cl_sh_pcim_wstrb,
   input [NUM_PCIE-1:0]         cl_sh_pcim_wlast,
   input [NUM_PCIE-1:0]         cl_sh_pcim_wvalid,
   output logic [NUM_PCIE-1:0]  sh_cl_pcim_wready,

   output logic [15:0]          sh_cl_pcim_bid,
   output logic [1:0]           sh_cl_pcim_bresp,
   output logic [NUM_PCIE-1:0]  sh_cl_pcim_bvalid,
   input [NUM_PCIE-1:0]         cl_sh_pcim_bready,
                               
   input [15:0]                 cl_sh_pcim_arid,
   input [63:0]                 cl_sh_pcim_araddr,
   input [7:0]                  cl_sh_pcim_arlen ,
   input [2:0]                  cl_sh_pcim_arsize ,
   input [18:0]                 cl_sh_pcim_aruser, //DW length of transfer
   input [NUM_PCIE-1:0]         cl_sh_pcim_arvalid,
   output logic [NUM_PCIE-1:0]  sh_cl_pcim_arready,

   output logic [15:0]          sh_cl_pcim_rid,
   output logic [511:0]         sh_cl_pcim_rdata,
   output logic [1:0]           sh_cl_pcim_rresp,
   output logic [NUM_PCIE-1:0]  sh_cl_pcim_rlast,
   output logic [NUM_PCIE-1:0]  sh_cl_pcim_rvalid,
   input [NUM_PCIE-1:0]         cl_sh_pcim_rready,

   output logic[1:0]            cfg_max_payload ,       //Max payload size - 00:128B, 01:256B, 10:512B
   output logic[2:0]            cfg_max_read_req,      //Max read requst size - 000b:128B, 001b:256B, 010b:512B, 011b:1024B
                                                                  // 100b-2048B, 101b:4096B


   //-------------------------------------
   // PCIe Interface to CL (AXI-4) (CL is PCI-slave)
   //-------------------------------------
   output logic [63:0]               sh_cl_dma_pcis_awaddr,
   output logic [5:0]                sh_cl_dma_pcis_awid  ,
   output logic [7:0]                sh_cl_dma_pcis_awlen ,
   output logic [2:0]                sh_cl_dma_pcis_awsize,
   output logic [NUM_PCIE-1:0]       sh_cl_dma_pcis_awvalid,
   input [NUM_PCIE-1:0]              cl_sh_dma_pcis_awready,

   output logic [511:0]              sh_cl_dma_pcis_wdata,
   output logic [63:0]               sh_cl_dma_pcis_wstrb,
   output logic [NUM_PCIE-1:0]       sh_cl_dma_pcis_wvalid,
   output logic [NUM_PCIE-1:0]       sh_cl_dma_pcis_wlast,
   input [NUM_PCIE-1:0]              cl_sh_dma_pcis_wready,

   input [1:0]                       cl_sh_dma_pcis_bresp,
   input [NUM_PCIE-1:0]              cl_sh_dma_pcis_bvalid,
   input [5:0]                       cl_sh_dma_pcis_bid,
   output logic [NUM_PCIE-1:0]       sh_cl_dma_pcis_bready,

   output logic [63:0]               sh_cl_dma_pcis_araddr,
   output logic [5:0]                sh_cl_dma_pcis_arid,
   output logic [7:0]                sh_cl_dma_pcis_arlen,
   output logic [2:0]                sh_cl_dma_pcis_arsize,
   output logic [NUM_PCIE-1:0]       sh_cl_dma_pcis_arvalid,
   input [NUM_PCIE-1:0]              cl_sh_dma_pcis_arready,
                                     
   input [5:0]                       cl_sh_dma_pcis_rid,
   input [511:0]                     cl_sh_dma_pcis_rdata,
   input [1:0]                       cl_sh_dma_pcis_rresp,
   input [NUM_PCIE-1:0]              cl_sh_dma_pcis_rlast,
   input [NUM_PCIE-1:0]              cl_sh_dma_pcis_rvalid,
   output logic [NUM_PCIE-1:0]       sh_cl_dma_pcis_rready,

`ifndef NO_XDMA
   input [15:0]         cl_sh_irq_req,
   output logic [15:0]  sh_cl_irq_ack,
`endif   
   
`ifndef VU190   
   //-----------------------------------------
   // CL MSIX
   //-----------------------------------------
    input                     cl_sh_msix_int,
    input [7:0]               cl_sh_msix_vec,
    output logic              sh_cl_msix_int_sent,
    output logic              sh_cl_msix_int_ack
`endif
    
   ,
   input [NUM_GTY-1:0]        cl_sh_aurora_channel_up,
   output logic [7:0]         sh_aurora_stat_addr,
   output logic               sh_aurora_stat_wr,
   output logic               sh_aurora_stat_rd,
   output logic [31:0]        sh_aurora_stat_wdata,

   input                      aurora_sh_stat_ack,
   input [31:0]               aurora_sh_stat_rdata,
   input [7:0]                aurora_sh_stat_int

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
   input [7:0]                 ddr_sh_stat_int[2:0],

   //-----------------------------------------------------------------------------
   // DDR Stats interfaces for DDR controllers in the CL.  This must be hooked up
   // to the sh_ddr.sv for the DDR interfaces to function.
   //-----------------------------------------------------------------------------
   output logic [7:0]          sh_ddr_stat_addr0,
   output logic                sh_ddr_stat_wr0, 
   output logic                sh_ddr_stat_rd0, 
   output logic [31:0]         sh_ddr_stat_wdata0,
   input                       ddr_sh_stat_ack0,
   input [31:0]                ddr_sh_stat_rdata0,
   input [7:0]                 ddr_sh_stat_int0,

   output logic [7:0]          sh_ddr_stat_addr1,
   output logic                sh_ddr_stat_wr1, 
   output logic                sh_ddr_stat_rd1, 
   output logic [31:0]         sh_ddr_stat_wdata1,
   input                       ddr_sh_stat_ack1,
   input [31:0]                ddr_sh_stat_rdata1,
   input [7:0]                 ddr_sh_stat_int1,

   output logic [7:0]          sh_ddr_stat_addr2,
   output logic                sh_ddr_stat_wr2, 
   output logic                sh_ddr_stat_rd2, 
   output logic [31:0]         sh_ddr_stat_wdata2,
   input                       ddr_sh_stat_ack2,
   input [31:0]                ddr_sh_stat_rdata2,
   input [7:0]                 ddr_sh_stat_int2,
    
   input [15:0]                cl_sh_ddr_awid,
   input [63:0]                cl_sh_ddr_awaddr,
   input [7:0]                 cl_sh_ddr_awlen,
   input                       cl_sh_ddr_awvalid,
   output logic                sh_cl_ddr_awready,

   input [15:0]                cl_sh_ddr_wid,
   input [511:0]               cl_sh_ddr_wdata,
   input [63:0]                cl_sh_ddr_wstrb,
   input                       cl_sh_ddr_wlast,
   input                       cl_sh_ddr_wvalid,
   output logic                sh_cl_ddr_wready,

   output logic [15:0]         sh_cl_ddr_bid,
   output logic [1:0]          sh_cl_ddr_bresp,
   output logic                sh_cl_ddr_bvalid,
   input                       cl_sh_ddr_bready,

   input [15:0]                cl_sh_ddr_arid,
   input [63:0]                cl_sh_ddr_araddr,
   input [7:0]                 cl_sh_ddr_arlen,
   input                       cl_sh_ddr_arvalid,
   output logic                sh_cl_ddr_arready,

   output logic [15:0]         sh_cl_ddr_rid,
   output logic [511:0]        sh_cl_ddr_rdata,
   output logic [1:0]          sh_cl_ddr_rresp,
   output logic                sh_cl_ddr_rlast,
   output logic                sh_cl_ddr_rvalid,
   input                       cl_sh_ddr_rready,

   output logic                sh_cl_ddr_is_ready,

   inout                       SYSMON_SCL,
   inout                       SYSMON_SDA,

   inout[3:0]                 fpga_uctrl_gpio


   //------------------------------------------------------------------------------------------
   // AXI-L maps to any inbound PCIe access through ManagementPF BAR4 for developer's use
   // If the CL is created through  Xilinx’s SDAccel, then this configuration bus
   // would be connected automatically to SDAccel generic logic (SmartConnect, APM etc)
   //------------------------------------------------------------------------------------------
    ,
    output logic        sda_cl_awvalid,
    output logic [31:0] sda_cl_awaddr, 
    input               cl_sda_awready,

   //Write data
   output logic         sda_cl_wvalid,
   output logic [31:0]  sda_cl_wdata,
   output logic [3:0]   sda_cl_wstrb,
   input                cl_sda_wready,

   //Write response
   input                cl_sda_bvalid,
   input [1:0]          cl_sda_bresp,
   output logic         sda_cl_bready,

   //Read address
   output logic         sda_cl_arvalid,
   output logic [31:0]  sda_cl_araddr,
   input                cl_sda_arready,

   //Read data/response
   input                cl_sda_rvalid,
   input [31:0]         cl_sda_rdata,
   input [1:0]          cl_sda_rresp,

   output logic         sda_cl_rready,

   //------------------------------------------------------------------------------------------
   // AXI-L maps to any inbound PCIe access through AppPF BAR0
   // For example, this AXI-L interface can connect to OpenCL Kernels
   // This would connect automatically to the required logic 
   // if the CL is created through SDAccel flow   
   //------------------------------------------------------------------------------------------
   output logic         sh_ocl_awvalid,
   output logic [31:0]  sh_ocl_awaddr,
   input                ocl_sh_awready,
                                                                                                                            
   //Write data             
   output logic         sh_ocl_wvalid,
   output logic [31:0]  sh_ocl_wdata,
   output logic [3:0]   sh_ocl_wstrb,
   input                ocl_sh_wready,

   //Write response
   input                ocl_sh_bvalid,
   input [1:0]          ocl_sh_bresp,
   output               sh_ocl_bready,

   //Read address                                                                       
   output logic         sh_ocl_arvalid,
   output logic [31:0]  sh_ocl_araddr,
   input                ocl_sh_arready,
                                                                                                                            
   //Read data/response
   input                ocl_sh_rvalid,
   input [31:0]         ocl_sh_rdata,
   input [1:0]          ocl_sh_rresp,
                                                                                                                            
   output logic         sh_ocl_rready,

   //------------------------------------------------------------------------------------------
   // AXI-L maps to any inbound PCIe access through AppPF BAR1
   // For example,
   //------------------------------------------------------------------------------------------
   output logic         sh_bar1_awvalid,
   output logic [31:0]  sh_bar1_awaddr,
   input                bar1_sh_awready,

   //Write data
   output logic         sh_bar1_wvalid,
   output logic [31:0]  sh_bar1_wdata,
   output logic [3:0]   sh_bar1_wstrb,
   input                bar1_sh_wready,
                                                                                                                     
   //Write response      
   input                bar1_sh_bvalid,
   input [1:0]          bar1_sh_bresp,
   output logic         sh_bar1_bready,
                                                                                                                          
   //Read address                                                                                                     
   output logic         sh_bar1_arvalid,
   output logic [31:0]  sh_bar1_araddr,
   input                bar1_sh_arready,
                                                                                                                            
   //Read data/response      
   input                bar1_sh_rvalid,
   input [31:0]         bar1_sh_rdata,
   input [1:0]          bar1_sh_rresp,
                                                                                                                            
   output logic [15:0]  sh_cl_status_vdip,
   input [15:0]         cl_sh_status_vled,
 
   output logic         sh_bar1_rready           

`ifndef NO_CL_DDR
   ,
   output logic        sh_RST_DIMM_A_N,
   output logic        sh_RST_DIMM_B_N,
   output logic        sh_RST_DIMM_D_N
`endif  
                               

    
  
   );

`include "axi_bfm_defines.svh"
   
   import tb_type_defines_pkg::*;

   
   AXI_Command sh_cl_wr_cmds[$];
   AXI_Data    sh_cl_wr_data[$];
   AXI_Command sh_cl_rd_cmds[$];
   AXI_Data    cl_sh_rd_data[$];
   AXI_Command sh_cl_b_resps[$];
   
   AXI_Command cl_sh_wr_cmds[$];
   AXI_Data    cl_sh_wr_data[$];
   AXI_Command cl_sh_rd_cmds[$];
   AXI_Command sh_cl_rd_data[$];
   AXI_Command cl_sh_b_resps[$];
   
   logic         clk_core;
   logic         rst_n;
   logic         pre_sync0_rst_n;
   logic         pre_sync1_rst_n;
   logic         pre_sync2_rst_n;
   logic         pre_sync3_rst_n;
   logic         sync_rst_n;
   logic         intf_sync_rst_n;
   logic         ddr_user_clk;
   logic         ddr_user_rst;
   logic         ddr_user_rst_n;
   logic         ddr_is_ready;
   logic         ddr_is_ready_presync;
   logic         ddr_is_ready_sync;

   logic [15:0]  cl_sh_ddr_awid_q;
   logic [63:0]  cl_sh_ddr_awaddr_q;
   logic [7:0]   cl_sh_ddr_awlen_q;
   logic         cl_sh_ddr_awvalid_q;
   logic         sh_cl_ddr_awready_q;

   logic [511:0] cl_sh_ddr_wdata_q;
   logic [63:0]  cl_sh_ddr_wstrb_q;
   logic         cl_sh_ddr_wlast_q;
   logic         cl_sh_ddr_wvalid_q;
   logic         sh_cl_ddr_wready_q;

   logic [15:0]  sh_cl_ddr_bid_q;
   logic [1:0]   sh_cl_ddr_bresp_q;
   logic         sh_cl_ddr_bvalid_q;
   logic         cl_sh_ddr_bready_q;
   
   logic [15:0]  cl_sh_ddr_arid_q;
   logic [63:0]  cl_sh_ddr_araddr_q;
   logic [7:0]   cl_sh_ddr_arlen_q;
   logic         cl_sh_ddr_arvalid_q;
   logic         sh_cl_ddr_arready_q;

   logic [15:0]  sh_cl_ddr_rid_q;
   logic [511:0] sh_cl_ddr_rdata_q;
   logic [1:0]   sh_cl_ddr_rresp_q;
   logic         sh_cl_ddr_rlast_q;
   logic         sh_cl_ddr_rvalid_q;
   logic         cl_sh_ddr_rready_q;

   logic [15:0]  sync_cl_sh_ddr_awid;
   logic [63:0]  sync_cl_sh_ddr_awaddr;
   logic [7:0]   sync_cl_sh_ddr_awlen;
   logic         sync_cl_sh_ddr_awvalid;
   logic         sync_sh_cl_ddr_awready;

   logic [511:0] sync_cl_sh_ddr_wdata;
   logic [63:0]  sync_cl_sh_ddr_wstrb;
   logic         sync_cl_sh_ddr_wlast;
   logic         sync_cl_sh_ddr_wvalid;
   logic         sync_sh_cl_ddr_wready;

   logic [15:0]  sync_sh_cl_ddr_bid;
   logic [1:0]   sync_sh_cl_ddr_bresp;
   logic         sync_sh_cl_ddr_bvalid;
   logic         sync_cl_sh_ddr_bready;

   logic [15:0]  sync_cl_sh_ddr_arid;
   logic [63:0]  sync_cl_sh_ddr_araddr;
   logic [7:0]   sync_cl_sh_ddr_arlen;
   logic         sync_cl_sh_ddr_arvalid;
   logic         sync_sh_cl_ddr_arready;

   logic [15:0]  sync_sh_cl_ddr_rid;
   logic [511:0] sync_sh_cl_ddr_rdata;
   logic [1:0]   sync_sh_cl_ddr_rresp;
   logic         sync_sh_cl_ddr_rlast;
   logic         sync_sh_cl_ddr_rvalid;
   logic         sync_cl_sh_ddr_rready;

   bit           debug;

   typedef struct {
      logic [63:0] buffer;
      logic [27:0] len;
      logic [63:0] cl_addr;
   } DMA_OP;

   DMA_OP h2c_dma_list[0:3][$];
   DMA_OP c2h_dma_list[0:3][$];
   DMA_OP c2h_data_dma_list[0:3][$];
   
   logic [3:0]     h2c_dma_started;
   logic [3:0]     c2h_dma_started;
   logic [3:0]     c2h_dma_done;
   logic [3:0]     h2c_dma_done;

   logic [7:0] read_data_buffer[];
  
   real MAIN_A0_DLY  = 4ns;
   real CORE_DLY     = 4ns;
   real EXTRA_A1_DLY = 8ns;
   real EXTRA_A2_DLY = 2.66ns;
   real EXTRA_A3_DLY = 2ns;
   real EXTRA_B0_DLY = 2ns;
   real EXTRA_B1_DLY = 4ns;
   real EXTRA_C0_DLY = 1.66ns;
   real EXTRA_C1_DLY = 1.25ns;


   initial begin
      debug = 1'b0;
/* TODO: Use the code below once plusarg support is enabled
      if ($test$plusargs("DEBUG")) begin
         debug = 1'b1;
      end else begin
         debug = 1'b0;
      end
*/
   end

   initial begin
      clk_core = 1'b0;
      forever #CORE_DLY clk_core = ~clk_core;
   end
   
   initial begin
      clk_main_a0 = 1'b0;
      forever #MAIN_A0_DLY clk_main_a0 = ~clk_main_a0;
   end
   
   initial begin
      clk_extra_a1 = 1'b0;
      forever #EXTRA_A1_DLY clk_extra_a1 = ~clk_extra_a1;
   end
   
   initial begin
      clk_extra_a2 = 1'b0;
      forever #EXTRA_A2_DLY clk_extra_a2 = ~clk_extra_a2;
   end
   
   initial begin
      clk_extra_a3 = 1'b0;
      forever #EXTRA_A3_DLY clk_extra_a3 = ~clk_extra_a3;
   end
   
   initial begin
      clk_extra_b0 = 1'b0;
      forever #EXTRA_B0_DLY clk_extra_b0 = ~clk_extra_b0;
   end
   
   initial begin
      clk_extra_b1 = 1'b0;
      forever #EXTRA_B1_DLY clk_extra_b1 = ~clk_extra_b1;
   end      
   
   initial begin
      clk_extra_c0 = 1'b0;
      forever #EXTRA_C0_DLY clk_extra_c0 = ~clk_extra_c0;
   end
   
   initial begin
      clk_extra_c1 = 1'b0;
      forever #EXTRA_C1_DLY clk_extra_c1 = ~clk_extra_c1;
   end
   
   logic rst_n_i;
   logic rst_main_n_i;
   logic rst_xtra_n_i;

   always @(posedge clk_core)
     rst_n <= rst_n_i;

   always @(posedge clk_main_a0)
     rst_main_n <= rst_main_n_i;

   initial begin
      kernel_rst_n = 1'b0;  // kernel reset is not used for non-SDAccel simulations.
   end

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

   assign sh_cl_pwr_state = 2'b00;

   initial begin
      sh_cl_ctl0 <= 32'h0;
      sh_cl_ctl1 <= 32'h0;
   end

   initial begin
      sh_cl_flr_assert <= 1'b0;
   end

   initial begin
      sh_cl_status_vdip <= 32'h0;
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

   // TODO: Connect up HMC I2C interface once supported
   initial begin
      hmc_iic_scl_i <= 1'b0;
      hmc_iic_sda_i <= 1'b0;
   end

   // TODO: Connect up HMC stats interface once supported
   initial begin
      sh_hmc_stat_addr <= 8'h00;
      sh_hmc_stat_wr <= 1'b0;
      sh_hmc_stat_rd <= 1'b0;
      sh_hmc_stat_wdata <= 32'h0;
   end

   // TODO: Connect up Aurora stats interface once supported
   initial begin
      sh_aurora_stat_addr <= 8'h00;
      sh_aurora_stat_wr <= 1'b0;
      sh_aurora_stat_rd <= 1'b0;
      sh_aurora_stat_wdata <= 32'h0;
   end

   // TODO: Connect up DDR stats interfaces if needed
   initial begin
      sh_ddr_stat_addr0  = 8'h00;
      sh_ddr_stat_wr0    = 1'b0;
      sh_ddr_stat_rd0    = 1'b0;
      sh_ddr_stat_wdata0 = 32'h0;

      sh_ddr_stat_addr1  = 8'h00;
      sh_ddr_stat_wr1    = 1'b0;
      sh_ddr_stat_rd1    = 1'b0;
      sh_ddr_stat_wdata1 = 32'h0;

      sh_ddr_stat_addr2  = 8'h00;
      sh_ddr_stat_wr2    = 1'b0;
      sh_ddr_stat_rd2    = 1'b0;
      sh_ddr_stat_wdata2 = 32'h0;
   end

   //=================================================
   //
   // sh->cl PCIeS Interface
   //
   //=================================================

   //
   // sh->cl Address Write Channel
   //

   always @(posedge clk_core) begin
      if (sh_cl_wr_cmds.size() != 0) begin

         sh_cl_dma_pcis_awaddr  <= sh_cl_wr_cmds[0].addr;
         sh_cl_dma_pcis_awid    <= sh_cl_wr_cmds[0].id;
         sh_cl_dma_pcis_awlen   <= sh_cl_wr_cmds[0].len;
         sh_cl_dma_pcis_awsize  <= /*sh_cl_wr_cmds[0].size*/3'h6;
         
         sh_cl_dma_pcis_awvalid <= !sh_cl_dma_pcis_awvalid ? 1'b1 :
                               !cl_sh_dma_pcis_awready ? 1'b1 : 1'b0;
         
         if (cl_sh_dma_pcis_awready && sh_cl_dma_pcis_awvalid) begin
            if (debug) begin
               $display("[%t] : DEBUG popping cmd fifo - %d", $realtime, sh_cl_wr_cmds.size());
            end
            sh_cl_wr_cmds.pop_front();
         end

      end
      else
         sh_cl_dma_pcis_awvalid <= 1'b0;
   end


   //
   // write Data Channel
   //

   //
   // sh->cl data Write Channel
   //

   always @(posedge clk_core) begin
      if (sh_cl_wr_data.size() != 0) begin

         sh_cl_dma_pcis_wdata <= sh_cl_wr_data[0].data;
         sh_cl_dma_pcis_wstrb <= sh_cl_wr_data[0].strb;
         sh_cl_dma_pcis_wlast <= sh_cl_wr_data[0].last;
         
         sh_cl_dma_pcis_wvalid <= !sh_cl_dma_pcis_wvalid ? 1'b1 :
                              !cl_sh_dma_pcis_wready ? 1'b1 : 1'b0;
         
         if (cl_sh_dma_pcis_wready && sh_cl_dma_pcis_wvalid) begin
            if (debug) begin
               $display("[%t] : DEBUG popping wr data fifo - %d", $realtime, sh_cl_wr_data.size());
            end
            h2c_dma_done[sh_cl_wr_data[0].id] = 1'b1; 
            sh_cl_wr_data.pop_front();
         end
         
      end
      else
         sh_cl_dma_pcis_wvalid <= 1'b0;
   end

   //
   // cl->sh B Response Channel
   //
   always @(posedge clk_core) begin
      sh_cl_dma_pcis_bready <= 1'b1;
   end

   always @(posedge clk_core) begin
      AXI_Command resp;

      if (cl_sh_dma_pcis_bvalid & sh_cl_dma_pcis_bready) begin
         resp.resp     = cl_sh_dma_pcis_bresp[0];
         resp.id       = cl_sh_dma_pcis_bid[0];

         cl_sh_b_resps.push_back(resp);
      end

   end


   //
   // sh->cl Address Read Channel
   //

   always @(posedge clk_core) begin
      if (sh_cl_rd_cmds.size() != 0) begin

         sh_cl_dma_pcis_araddr  <= sh_cl_rd_cmds[0].addr;
         sh_cl_dma_pcis_arid    <= sh_cl_rd_cmds[0].id;
         sh_cl_dma_pcis_arlen   <= sh_cl_rd_cmds[0].len;
         sh_cl_dma_pcis_arsize  <= /*sh_cl_rd_cmds[0].size*/3'h6;
         
         sh_cl_dma_pcis_arvalid <= !sh_cl_dma_pcis_arvalid ? 1'b1 :
                               !cl_sh_dma_pcis_arready ? 1'b1 : 1'b0;
         
         if (cl_sh_dma_pcis_arready && sh_cl_dma_pcis_arvalid) begin
            if (debug) begin
               $display("[%t] : DEBUG popping cmd fifo - %d", $realtime, sh_cl_rd_cmds.size());
            end
            sh_cl_rd_cmds.pop_front();
         end

      end
      else
         sh_cl_dma_pcis_arvalid <= 1'b0;
   end

   //
   // cl->sh Read Data Channel
   //
   always @(posedge clk_core) begin
      sh_cl_dma_pcis_rready <= (cl_sh_rd_data.size() < 16) ? 1'b1 : 1'b0;
   end

   always @(posedge clk_core) begin
      AXI_Data data;

      if (cl_sh_dma_pcis_rvalid & sh_cl_dma_pcis_rready) begin
         data.data     = cl_sh_dma_pcis_rdata;
         data.id       = cl_sh_dma_pcis_rid;
         data.last     = cl_sh_dma_pcis_rlast;

         if (debug) begin
            for (int i=0; i<16; i++) begin
               $display("[%t] - DEBUG read data [%2d]: 0x%08h", $realtime, i, cl_sh_dma_pcis_rdata[(i*32)+:32]);
            end
         end
         
         cl_sh_rd_data.push_back(data);
      end

   end

   //=================================================
   //
   // cl->sh PCIeM Interface
   //
   //=================================================
   logic [63:0] host_memory_addr = 0;
   AXI_Command  host_mem_wr_que[$];
   logic        first_wr_beat = 1;
   int          wr_last_cnt = 0;
   logic [63:0] wr_addr;
   
   always @(posedge clk_core) begin

      if (host_mem_wr_que.size() > 0) begin
         if (first_wr_beat == 1) begin
            wr_addr = host_mem_wr_que[0].addr;
            first_wr_beat = 1'b0;
         end

         if (cl_sh_wr_data.size() > 0) begin
            if (debug) begin
               $display("[%t] - DEBUG fb:  %1d  0x%0128x  0x%016x", $realtime, first_wr_beat, cl_sh_wr_data[0].data, cl_sh_wr_data[0].strb);
            end
            for(int i=wr_addr[5:2]; i<16; i++) begin
               logic [31:0] word;

               if (!tb.use_c_host_memory)
                 if (tb.sv_host_memory.exists(wr_addr))
                   word = tb.sv_host_memory[wr_addr];
                 else
                   word = 32'hffff_ffff;   // return a default value
               else begin
                  for(int k=0; k<4; k++) begin
                     byte t;
                     t = tb.host_memory_getc(wr_addr + k);
                     word = {t, word[31:8]};
                  end                  
               end
               
               for(int j=0; j<4; j++) begin
                  logic [7:0] c;
                  int         index;
                  index = j + (i * 4);
                  
                  if (cl_sh_wr_data[0].strb[index]) begin
                     c = cl_sh_wr_data[0].data >> (index * 8);
                     word = {c, word[31:8]};
                  end
               end // for (int j=0; j<4; j++)

               if (!tb.use_c_host_memory)
                 tb.sv_host_memory[wr_addr] = word;
               else begin
                  for(int k=0; k<4; k++) begin
                     byte t;
                     t = word[7:0];                     

                     tb.host_memory_putc(wr_addr + k, t);
                     word = word >> 8;
                  end                  
               end
               
               wr_addr += 4;
            end
            if (cl_sh_wr_data[0].last == 1) begin
               first_wr_beat = 1'b1;
               host_mem_wr_que.pop_front();
               if (debug) begin
                  $display("[%t] - DEBUG reseting...", $realtime);
               end
               
            end
            
            cl_sh_wr_data.pop_front();
         end // if (cl_sh_wr_data.size() > 0)
      end // if (host_mem_wr_que.size() > 0)
   end
  
   //
   // cl->sh Write Address Channel
   //

   always @(posedge clk_core) begin
      AXI_Command cmd;

      if (cl_sh_pcim_awvalid[0] && sh_cl_pcim_awready[0]) begin
         cmd.addr = cl_sh_pcim_awaddr;
         cmd.id   = cl_sh_pcim_awid;
         cmd.len  = cl_sh_pcim_awlen;
         cmd.size  = cl_sh_pcim_awsize;
         cmd.last = 0;
         
         cl_sh_wr_cmds.push_back(cmd);         
         sh_cl_b_resps.push_back(cmd);
         host_mem_wr_que.push_back(cmd);
      end

      if (cl_sh_wr_cmds.size() < 4)
        sh_cl_pcim_awready[0] <= 1'b1;
      else
        sh_cl_pcim_awready[0] <= 1'b0;
        
   end


   //
   // cl-sh write Data Channel
   //

   always @(posedge clk_core) begin
      AXI_Data wr_data;
      
      if (sh_cl_pcim_wready[0] && cl_sh_pcim_wvalid[0]) begin
         wr_data.data = cl_sh_pcim_wdata;
         wr_data.strb = cl_sh_pcim_wstrb;
         wr_data.last = cl_sh_pcim_wlast;

         cl_sh_wr_data.push_back(wr_data);

         if (wr_data.last == 1)
           wr_last_cnt += 1;
         
      end
      if (cl_sh_wr_data.size() > 64)
        sh_cl_pcim_wready[0] <= 1'b0;
      else
        sh_cl_pcim_wready[0] <= 1'b1;
        
   end

   //
   // cl->sh B Response Channel
   //

   always @(posedge clk_core) begin
      if (sh_cl_b_resps.size() != 0) begin
         if (debug) begin
            $display("[%t] : DEBUG resp.size  %2d ", $realtime, sh_cl_b_resps.size());
         end
         if (wr_last_cnt != 0) begin
            sh_cl_pcim_bid     <= sh_cl_b_resps[0].id;
            sh_cl_pcim_bresp   <= 2'b00;

            sh_cl_pcim_bvalid   <= !sh_cl_pcim_bvalid ? 1'b1 :
                                   !cl_sh_pcim_bready ? 1'b1 : 1'b0;

            if (cl_sh_pcim_bready && sh_cl_pcim_bvalid) begin
               wr_last_cnt -= 1;
               sh_cl_b_resps.pop_front();
               cl_sh_wr_cmds.pop_front();
            end
         end
      end
      else
        sh_cl_pcim_bvalid <= 1'b0;
      
   end
   
   //
   // sh->cl Address Read Channel
   //

   always @(posedge clk_core) begin
      AXI_Command cmd;
      
      if (cl_sh_pcim_arvalid[0] && sh_cl_pcim_arready[0]) begin
         cmd.addr = cl_sh_pcim_araddr;
         cmd.id   = cl_sh_pcim_arid;
         cmd.len  = cl_sh_pcim_arlen;
         cmd.size = cl_sh_pcim_arsize;
         cmd.last = 0;
         
         cl_sh_rd_cmds.push_back(cmd);
         sh_cl_rd_data.push_back(cmd);
      end

      if (cl_sh_rd_cmds.size() < 4)
        sh_cl_pcim_arready[0] <= 1'b1;
      else
        sh_cl_pcim_arready[0] <= 1'b0;
   end

   //
   // sh->cl Read Data Channel
   //

   logic first_rd_beat;
   logic [63:0] rd_addr;
   
   always @(posedge clk_core) begin
      AXI_Command rd_cmd;
      logic [511:0] beat;

      if (sh_cl_rd_data.size() != 0) begin
         sh_cl_pcim_rid    <= sh_cl_rd_data[0].id;
         sh_cl_pcim_rresp  <= 2'b00;
         sh_cl_pcim_rvalid[0] <= !sh_cl_pcim_rvalid[0] ? 1'b1 :
                                 !cl_sh_pcim_rready[0] ? 1'b1 :
                                 !sh_cl_pcim_rlast[0]  ? 1'b1 : 1'b0;

         sh_cl_pcim_rlast[0] <= (sh_cl_rd_data[0].len == 0) ? 1'b1 :
                                (sh_cl_rd_data[0].len == 1) && sh_cl_pcim_rvalid && cl_sh_pcim_rready ? 1'b1 : 1'b0;
         
         if (first_rd_beat == 1'b1) begin
            rd_addr = sh_cl_rd_data[0].addr;
            first_rd_beat = 1'b0;
         end
         
         for(int i=rd_addr[5:2]; i<16; i++) begin
            logic [31:0] c;

            if (debug) begin
               $display("[%t] : DEBUG reading addr 0x%016x", $realtime, rd_addr);
            end
            
            if (!tb.use_c_host_memory)
              if (tb.sv_host_memory.exists(rd_addr))
                c = tb.sv_host_memory[rd_addr];
              else
                c = 32'hffffffff;
            else begin
               for(int k=0; k<4; k++) begin
                  byte t;
                  t = tb.host_memory_getc(rd_addr + k);
                  c = {t, c[31:8]};
               end
            end
            beat = {c, beat[511:32]};
            rd_addr +=4;
         end

         if (debug) begin
            $display("[%t] : DEBUG beat 0x%0128x", $realtime, beat);
         end
         sh_cl_pcim_rdata <= beat;

      end
      else begin
         sh_cl_pcim_rvalid[0] <= 1'b0;
         sh_cl_pcim_rlast[0]  <= 1'b0;         
         first_rd_beat = 1'b1;
      end

      if (cl_sh_pcim_rready[0] && sh_cl_pcim_rvalid && (sh_cl_rd_data.size() != 0)) begin
         if (sh_cl_rd_data[0].len == 0) begin
            sh_cl_rd_data.pop_front();
            cl_sh_rd_cmds.pop_front();
            first_rd_beat = 1'b1;
         end
         else
           sh_cl_rd_data[0].len--;         

      end
      
   end

   //=================================================
   //
   // Interrupt handling
   //
   //=================================================
   logic [15:0]  int_ack;
   logic [15:0]  int_pend;

   initial begin
      int_ack = 16'h0000;
      int_pend = 16'h0000;
   end

   always @(posedge clk_core) begin
      for (int idx=0; idx<16; idx++) begin
         if (cl_sh_irq_req[idx] == 1'b1) begin
            int_pend |= 1'b1 << idx;
         end
      end

      if (|int_ack) begin
        for (int idx=0; idx<16; idx++) begin
           if (int_ack[idx] == 1'b1) begin
              $display("[%t] : Sending ack for interrupt %2d", $realtime, idx);
           end
        end
      end

      sh_cl_irq_ack <= int_ack;
      int_ack = 16'h0000;
   end

   always @(posedge clk_core) begin
      for (int idx=0; idx<16; idx++) begin
         if (int_pend[idx] == 1'b1) begin
            tb.int_handler(idx);
         end
      end
   end

   //==========================================================

   // DDR Controller
   axi_register_slice DDR_3_AXI4_REG_SLC (
     .aclk           (clk_core),
     .aresetn        (intf_sync_rst_n),

     .s_axi_awid     (cl_sh_ddr_awid),
     .s_axi_awaddr   (cl_sh_ddr_awaddr),
     .s_axi_awlen    (cl_sh_ddr_awlen),
     .s_axi_awvalid  (cl_sh_ddr_awvalid),
     .s_axi_awready  (sh_cl_ddr_awready),
     .s_axi_wdata    (cl_sh_ddr_wdata),
     .s_axi_wstrb    (cl_sh_ddr_wstrb),
     .s_axi_wlast    (cl_sh_ddr_wlast),
     .s_axi_wvalid   (cl_sh_ddr_wvalid),
     .s_axi_wready   (sh_cl_ddr_wready),
     .s_axi_bid      (sh_cl_ddr_bid),
     .s_axi_bresp    (sh_cl_ddr_bresp),
     .s_axi_bvalid   (sh_cl_ddr_bvalid),
     .s_axi_bready   (cl_sh_ddr_bready),
     .s_axi_arid     (cl_sh_ddr_arid),
     .s_axi_araddr   (cl_sh_ddr_araddr),
     .s_axi_arlen    (cl_sh_ddr_arlen),
     .s_axi_arvalid  (cl_sh_ddr_arvalid),
     .s_axi_arready  (sh_cl_ddr_arready),
     .s_axi_rid      (sh_cl_ddr_rid),
     .s_axi_rdata    (sh_cl_ddr_rdata),
     .s_axi_rresp    (sh_cl_ddr_rresp),
     .s_axi_rlast    (sh_cl_ddr_rlast),
     .s_axi_rvalid   (sh_cl_ddr_rvalid),
     .s_axi_rready   (cl_sh_ddr_rready),
  
     .m_axi_awid     (cl_sh_ddr_awid_q),   
     .m_axi_awaddr   (cl_sh_ddr_awaddr_q), 
     .m_axi_awlen    (cl_sh_ddr_awlen_q),  
     .m_axi_awvalid  (cl_sh_ddr_awvalid_q),
     .m_axi_awready  (sh_cl_ddr_awready_q),
     .m_axi_wdata    (cl_sh_ddr_wdata_q),  
     .m_axi_wstrb    (cl_sh_ddr_wstrb_q),  
     .m_axi_wlast    (cl_sh_ddr_wlast_q),  
     .m_axi_wvalid   (cl_sh_ddr_wvalid_q), 
     .m_axi_wready   (sh_cl_ddr_wready_q), 
     .m_axi_bid      (sh_cl_ddr_bid_q),    
     .m_axi_bresp    (sh_cl_ddr_bresp_q),  
     .m_axi_bvalid   (sh_cl_ddr_bvalid_q), 
     .m_axi_bready   (cl_sh_ddr_bready_q), 
     .m_axi_arid     (cl_sh_ddr_arid_q),   
     .m_axi_araddr   (cl_sh_ddr_araddr_q), 
     .m_axi_arlen    (cl_sh_ddr_arlen_q),  
     .m_axi_arvalid  (cl_sh_ddr_arvalid_q),
     .m_axi_arready  (sh_cl_ddr_arready_q),
     .m_axi_rid      (sh_cl_ddr_rid_q),    
     .m_axi_rdata    (sh_cl_ddr_rdata_q),  
     .m_axi_rresp    (sh_cl_ddr_rresp_q),  
     .m_axi_rlast    (sh_cl_ddr_rlast_q),  
     .m_axi_rvalid   (sh_cl_ddr_rvalid_q), 
     .m_axi_rready   (cl_sh_ddr_rready_q)
     );

    axi_clock_converter_0 DDR4_3_AXI_CCF (
     .s_axi_aclk(clk_core),
     .s_axi_aresetn(rst_n),

     .s_axi_awid(cl_sh_ddr_awid_q),
     .s_axi_awaddr(cl_sh_ddr_awaddr_q),
     .s_axi_awlen(cl_sh_ddr_awlen_q),
     .s_axi_awuser(19'b0),
     .s_axi_awvalid(cl_sh_ddr_awvalid_q),
     .s_axi_awready(sh_cl_ddr_awready_q),

     .s_axi_wdata(cl_sh_ddr_wdata_q),
     .s_axi_wstrb(cl_sh_ddr_wstrb_q),
     .s_axi_wlast(cl_sh_ddr_wlast_q),
     .s_axi_wvalid(cl_sh_ddr_wvalid_q),
     .s_axi_wready(sh_cl_ddr_wready_q),

     .s_axi_bid(sh_cl_ddr_bid_q),
     .s_axi_bresp(sh_cl_ddr_bresp_q),
     .s_axi_bvalid(sh_cl_ddr_bvalid_q),
     .s_axi_bready(cl_sh_ddr_bready_q),

     .s_axi_arid(cl_sh_ddr_arid_q),
     .s_axi_araddr(cl_sh_ddr_araddr_q),
     .s_axi_arlen(cl_sh_ddr_arlen_q),
     .s_axi_aruser(19'b0),
     .s_axi_arvalid(cl_sh_ddr_arvalid_q),
     .s_axi_arready(sh_cl_ddr_arready_q),

     .s_axi_rid(sh_cl_ddr_rid_q),
     .s_axi_rdata(sh_cl_ddr_rdata_q),
     .s_axi_rresp(sh_cl_ddr_rresp_q),
     .s_axi_rlast(sh_cl_ddr_rlast_q),
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
     .m_axi_wvalid(sync_cl_sh_ddr_wvalid),
     .m_axi_wready(sync_sh_cl_ddr_wready),

     .m_axi_bid(sync_sh_cl_ddr_bid),
     .m_axi_bresp(sync_sh_cl_ddr_bresp),
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

     .c0_ddr4_s_axi_ctrl_awvalid(1'b0),
     .c0_ddr4_s_axi_ctrl_awready(),
     .c0_ddr4_s_axi_ctrl_awaddr(32'h0),
     .c0_ddr4_s_axi_ctrl_wvalid(1'b0),
     .c0_ddr4_s_axi_ctrl_wready(),
     .c0_ddr4_s_axi_ctrl_wdata(32'h0),
     .c0_ddr4_s_axi_ctrl_bvalid(),
     .c0_ddr4_s_axi_ctrl_bready(1'b0),
     .c0_ddr4_s_axi_ctrl_bresp(),
     .c0_ddr4_s_axi_ctrl_arvalid(1'b0),
     .c0_ddr4_s_axi_ctrl_arready(),
     .c0_ddr4_s_axi_ctrl_araddr(32'h0),
     .c0_ddr4_s_axi_ctrl_rvalid(),
     .c0_ddr4_s_axi_ctrl_rready(1'b0),
     .c0_ddr4_s_axi_ctrl_rdata(),
     .c0_ddr4_s_axi_ctrl_rresp(),
     .c0_ddr4_interrupt(),

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


   axil_bfm sda_axil_bfm(
                         .axil_clk(clk_core),
                         .axil_rst_n(sync_rst_n),
                         .axil_awvalid(sda_cl_awvalid),
                         .axil_awaddr(sda_cl_awaddr),
                         .axil_awready(cl_sda_awready),
                         .axil_wvalid(sda_cl_wvalid),
                         .axil_wdata(sda_cl_wdata),
                         .axil_wstrb(sda_cl_wstrb),
                         .axil_wready(cl_sda_wready),
                         .axil_bvalid(cl_sda_bvalid),
                         .axil_bresp(cl_sda_bresp),
                         .axil_bready(sda_cl_bready),
                         .axil_arvalid(sda_cl_arvalid),
                         .axil_araddr(sda_cl_araddr),
                         .axil_arready(cl_sda_arready),
                         .axil_rvalid(cl_sda_rvalid),
                         .axil_rdata(cl_sda_rdata),
                         .axil_rresp(cl_sda_rresp),
                         .axil_rready(sda_cl_rready));

   axil_bfm ocl_axil_bfm(
                         .axil_clk(clk_core),
                         .axil_rst_n(sync_rst_n),
                         .axil_awvalid(sh_ocl_awvalid),
                         .axil_awaddr(sh_ocl_awaddr),
                         .axil_awready(ocl_sh_awready),
                         .axil_wvalid(sh_ocl_wvalid),
                         .axil_wdata(sh_ocl_wdata),
                         .axil_wstrb(sh_ocl_wstrb),
                         .axil_wready(ocl_sh_wready),
                         .axil_bvalid(ocl_sh_bvalid),
                         .axil_bresp(ocl_sh_bresp),
                         .axil_bready(sh_ocl_bready),
                         .axil_arvalid(sh_ocl_arvalid),
                         .axil_araddr(sh_ocl_araddr),
                         .axil_arready(ocl_sh_arready),
                         .axil_rvalid(ocl_sh_rvalid),
                         .axil_rdata(ocl_sh_rdata),
                         .axil_rresp(ocl_sh_rresp),
                         .axil_rready(sh_ocl_rready));

   axil_bfm bar1_axil_bfm(
                         .axil_clk(clk_core),
                         .axil_rst_n(sync_rst_n),
                         .axil_awvalid(sh_bar1_awvalid),
                         .axil_awaddr(sh_bar1_awaddr),
                         .axil_awready(bar1_sh_awready),
                         .axil_wvalid(sh_bar1_wvalid),
                         .axil_wdata(sh_bar1_wdata),
                         .axil_wstrb(sh_bar1_wstrb),
                         .axil_wready(bar1_sh_wready),
                         .axil_bvalid(bar1_sh_bvalid),
                         .axil_bresp(bar1_sh_bresp),
                         .axil_bready(sh_bar1_bready),
                         .axil_arvalid(sh_bar1_arvalid),
                         .axil_araddr(sh_bar1_araddr),
                         .axil_arready(bar1_sh_arready),
                         .axil_rvalid(bar1_sh_rvalid),
                         .axil_rdata(bar1_sh_rdata),
                         .axil_rresp(bar1_sh_rresp),
                         .axil_rready(sh_bar1_rready));



   
   //=================================================
   //
   // power_up
   //
   //   Description: asserts and deasserts various resets
   //   Outputs: None
   //
   //=================================================
   task power_up(input ClockRecipe::A_RECIPE clk_recipe_a = ClockRecipe::A0, 
                       ClockRecipe::B_RECIPE clk_recipe_b = ClockRecipe::B0, 
                       ClockRecipe::C_RECIPE clk_recipe_c = ClockRecipe::C0);
      case (clk_recipe_a)
         ClockRecipe::A0: begin
            MAIN_A0_DLY  = 4ns;
            CORE_DLY     = 4ns;
            EXTRA_A1_DLY = 8ns;
            EXTRA_A2_DLY = 2.66ns;
            EXTRA_A3_DLY = 2ns;
         end
         ClockRecipe::A1: begin
            MAIN_A0_DLY  = 2ns;
            CORE_DLY     = 2ns;
            EXTRA_A1_DLY = 4ns;
            EXTRA_A2_DLY = 1.33ns;
            EXTRA_A3_DLY = 1ns;
         end
         ClockRecipe::A2: begin
            MAIN_A0_DLY  = 32ns;
            CORE_DLY     = 32ns;
            EXTRA_A1_DLY = 64ns;
            EXTRA_A2_DLY = 4ns;
            EXTRA_A3_DLY = 8ns;
         end
         default: begin
            $display("Error - Invalid Clock Profile Selected.");
            $finish;
         end
      endcase 
      case (clk_recipe_b)
         ClockRecipe::B0: begin
            EXTRA_B0_DLY = 2ns;
            EXTRA_B1_DLY = 4ns;
         end
         ClockRecipe::B1: begin
            EXTRA_B0_DLY = 4ns;
            EXTRA_B1_DLY = 8ns;
         end
         default: begin
            $display("Error - Invalid Clock Profile Selected.");
            $finish;
         end
      endcase
      case (clk_recipe_c)
         ClockRecipe::C0: begin
            EXTRA_C0_DLY = 1.66ns;
            EXTRA_C1_DLY = 1.25ns;
         end
         ClockRecipe::C1: begin
            EXTRA_C0_DLY = 3.33ns;
            EXTRA_C1_DLY = 2.5ns;
         end
         default: begin
            $display("Error - Invalid Clock Profile Selected.");
            $finish;
         end
      endcase
      rst_n_i = 1'b0;
      rst_main_n_i = 1'b0;
      rst_xtra_n_i = 1'b0;
      #5000ns;
      rst_n_i = 1'b1;
      rst_main_n_i = 1'b1;
      rst_xtra_n_i = 1'b1;
      #50ns;
   endtask // power_up
  
   //=================================================
   //
   // nsec_delay
   //
   //   Description: sets a delay in nsec
   //   Outputs: None
   //
   //=================================================
   task nsec_delay(int dly = 10000);
      #dly;
   endtask

   //=================================================
   //
   // set_virtual_dip_switch
   //
   //   Description: writes virtual dip switches
   //   Outputs: None
   //
   //=================================================
   function void set_virtual_dip_switch(int dip_switch);
      sh_cl_status_vdip = dip_switch[15:0];
   endfunction

   //=================================================
   //
   // get_virtual_dip_switch
   //
   //   Description: reads virtual dip switch status
   //   Outputs: dip_status
   //
   //=================================================
   function logic[15:0] get_virtual_dip_switch();
      return sh_cl_status_vdip;
   endfunction

   //=================================================
   //
   // get_virtual_led
   //
   //   Description: reads virtual led status
   //   Outputs: led status
   //
   //=================================================
   function logic[15:0] get_virtual_led();
      return cl_sh_status_vled;
   endfunction

   //=================================================
   //
   // Kernel_reset
   //
   //   Description: sets kernel_reset
   //   Outputs: None
   //
   //=================================================
   function void kernel_reset(input logic d = 1);
      kernel_rst_n = d;
   endfunction

   //=================================================
   //
   // power_down
   //
   //   Description: deasserts various resets
   //   Outputs: None
   //
   //=================================================
   task power_down;
      #50ns;
      rst_n_i = 1'b0;
      rst_main_n_i = 1'b0;
      #50ns;
   endtask // power_down

   //=================================================
   //
   // issue_flr
   //
   //   Description: issue a FLR command
   //   Outputs: None
   //
   //=================================================
   task issue_flr();
      sh_cl_flr_assert = 1'b1;
      wait(cl_sh_flr_done == 1);
      sh_cl_flr_assert = 1'b0;
   endtask

   //=================================================
   //
   // map_host_memory
   //
   //   Description: used to connect C host memory to simulation memory.
   //   Outputs: None
   //
   //=================================================
   task map_host_memory(input logic [63:0] addr);
      if (debug) begin
         $display("[%t] : DEBUG mapping host memory to 0x%16x", $realtime, addr);
      end
      host_memory_addr = addr;
      tb.use_c_host_memory = 1'b1;      
   endtask // map_host_memory
  
   //=================================================
   //
   // set_ack_bit
   //
   //   Description: used to acknowledge an interrupt and clear pending bit
   //   Outputs: None
   //
   //=================================================
   function void set_ack_bit(input int int_num);
      int_ack[int_num] = 1'b1;
      int_pend[int_num] = 1'b0;
   endfunction

   //=================================================
   //
   // poke
   //
   //   Description: used to write a single beat of data at addr into one of the four CL AXI ports specified by intf.
   //        Intf
   //         0 = PCIS
   //         1 = SDA
   //         2 = OCL
   //         3 = BAR1
   //
   //        id - AXI bus ID
   //
   //        Size
   //         0 = 1 byte, 1 = 2 bytes, 2 = 4 bytes (32 bits), 3 = 8 bytes (64 bits)
   //
   //   Outputs: None
   //
   //=================================================
   task poke(input logic [63:0] addr, 
             logic [511:0] data, 
             logic [5:0] id = 6'h0, 
             DataSize::DATA_SIZE size = DataSize::UINT32, 
             AxiPort::AXI_PORT intf = AxiPort::PORT_DMA_PCIS); 

      logic [63:0] strb;

      case (size)
        DataSize::UINT8  : strb = 64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0001;
        DataSize::UINT16 : strb = 64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0011;
        DataSize::UINT32 : strb = 64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_1111;
        DataSize::UINT64 : strb = 64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_1111_1111;
        DataSize::UINT128: strb = 64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_1111_1111_1111_1111;
        DataSize::UINT256: strb = 64'b0000_0000_0000_0000_0000_0000_0000_0000_1111_1111_1111_1111_1111_1111_1111_1111;
        DataSize::UINT512: strb = 64'b1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111;
        default: begin
           $display("FATAL ERROR - Invalid size specified");
           $finish;
        end
      endcase // case (size)
      
      case (intf)
        AxiPort::PORT_DMA_PCIS: begin
           AXI_Command axi_cmd;
           AXI_Data    axi_data;

           logic [1:0] resp;
           
           axi_cmd.addr = addr;
           axi_cmd.len  = 0;
           axi_cmd.size = size;
           axi_cmd.id   = id;
    
           sh_cl_wr_cmds.push_back(axi_cmd);

           axi_data.data = data << (addr[5:0] * 8);
           axi_data.strb = strb << addr[5:0];
           
           axi_data.id   = id;
           axi_data.last = 1'b1;
           
           #20ns sh_cl_wr_data.push_back(axi_data);
      
           while (cl_sh_b_resps.size() == 0)
             #20ns;
      
           resp = cl_sh_b_resps[0].resp;
           cl_sh_b_resps.pop_front();
        end
        AxiPort::PORT_SDA: begin
           sda_axil_bfm.poke(addr, data);
        end        
        AxiPort::PORT_OCL: begin
           ocl_axil_bfm.poke(addr, data);
        end
        AxiPort::PORT_BAR1: begin
           bar1_axil_bfm.poke(addr, data);
        end
        default: begin
          $display("FATAL ERROR - Invalid CL port specified");
          $finish;
        end
      endcase // case (intf)
      
   endtask // poke

   task poke_pcis(input logic [63:0] addr, 
                  logic [511:0] data, 
                  logic [63:0] strb, 
                  logic [5:0] id = 6'h0);
      
      AXI_Command axi_cmd;
      AXI_Data    axi_data;

      logic [1:0]             resp;
           
      axi_cmd.addr = addr;
      axi_cmd.len  = 0;
      axi_cmd.id   = id;

      sh_cl_wr_cmds.push_back(axi_cmd);

      axi_data.data = data;
      axi_data.strb = strb;
           
      axi_data.id   = id;
      axi_data.last = 1'b1;
           
      #20ns sh_cl_wr_data.push_back(axi_data);
      
      while (cl_sh_b_resps.size() == 0)
        #20ns;
      
      resp = cl_sh_b_resps[0].resp;
      cl_sh_b_resps.pop_front();
      
   endtask // poke

   //=================================================
   //
   // peek
   //
   //   Description: used to read a single beat of data at addr from one of the four CL AXI ports specified by intf.
   //        Intf
   //         0 = PCIS
   //         1 = SDA
   //         2 = OCL
   //         3 = BAR1
   //
   //        id - AXI bus ID
   //
   //        Size
   //         0 = 1 byte, 1 = 2 bytes, 2 = 4 bytes (32 bits), 3 = 8 bytes (64 bits)
   //
   //   Outputs: Read Data Value
   //
   //=================================================
   task peek(input logic [63:0] addr, 
             output logic [511:0] data, 
             input logic [5:0] id = 6'h0, 
             DataSize::DATA_SIZE size = DataSize::UINT32, 
             AxiPort::AXI_PORT intf = AxiPort::PORT_DMA_PCIS); 
      data = 0;
      case (intf)
        AxiPort::PORT_DMA_PCIS : begin
           AXI_Command axi_cmd;
           int         byte_idx;
           int         mem_arr_idx;
           
           axi_cmd.addr = addr;
           axi_cmd.len  = 0;
           axi_cmd.size = size;
           axi_cmd.id   = id;
           
           sh_cl_rd_cmds.push_back(axi_cmd);
           
           byte_idx     = addr[5:0];
           mem_arr_idx  = byte_idx*8;
           
           while (cl_sh_rd_data.size() == 0)
             #20ns;
           for (int num_bytes =0; num_bytes < 2**size; num_bytes++) begin
              data[(num_bytes*8)+:8] = cl_sh_rd_data[0].data[(mem_arr_idx+(num_bytes*8))+:8];
           end
           cl_sh_rd_data.pop_front();
        end // case: 0
        AxiPort::PORT_SDA : begin
           sda_axil_bfm.peek(addr, data);
        end
        AxiPort::PORT_OCL : begin
           ocl_axil_bfm.peek(addr, data);
        end
        AxiPort::PORT_BAR1 : begin
           bar1_axil_bfm.peek(addr, data);
        end
      endcase // case (intf)
      
   endtask // peek

   task peek_pcis(input logic [63:0] addr, 
             output logic [511:0] data, 
             input logic [5:0] id = 6'h0);
      
      AXI_Command axi_cmd;
           
      axi_cmd.addr = addr;
      axi_cmd.len  = 0;
      axi_cmd.id   = id;
      
      sh_cl_rd_cmds.push_back(axi_cmd);
      
      while (cl_sh_rd_data.size() == 0)
        #20ns;
      
      data = cl_sh_rd_data[0].data;
      cl_sh_rd_data.pop_front();
      
   endtask // peek_pcis

   //=================================================
   //
   // dma_buffer_to_cl
   //
   //   Description: used to move a data buffer to the CL via the PCIS AXI interface using one of four channels.
   //        The size of the transfer is determined by the number of bytes in the buffer.
   //        
   //        chan    = 0-3 channel number
   //        buffer  = AXI bus ID
   //        cl_addr = starting CL AXI addr
   //
   //
   //   Outputs: Read Data Value
   //
   //=================================================
   function void dma_buffer_to_cl(input logic [1:0] chan, logic [63:0] src_addr, logic [63:0] cl_addr, logic [27:0] len);
      DMA_OP dop;
      
      dop.buffer = src_addr;
      dop.cl_addr = cl_addr;
      dop.len = len;
      
      h2c_dma_list[chan].push_back(dop);
      
   endfunction // dma_buffer_to_cl

   function automatic void dma_cl_to_buffer(input logic [1:0] chan, logic [63:0] dst_addr, input [63:0] cl_addr, logic [27:0] len);
      DMA_OP dop;
      dop.buffer = dst_addr;
      dop.cl_addr = cl_addr;
      dop.len = len;
      c2h_dma_list[chan].push_back(dop);
   endfunction // dma_cl_to_buffer

   function void start_dma_to_cl(input int chan);
      h2c_dma_started[chan] = 1'b1;
      h2c_dma_done[chan] = 1'b0;
   endfunction // start_dma_to_cl
   
   function void start_dma_to_buffer(input int chan);
      c2h_dma_started[chan] = 1'b1;
      c2h_dma_done[chan] = 1'b0;
   endfunction // start_dma_to_buffer

   function bit is_dma_to_cl_done(input int chan);  // 1 = done
      return h2c_dma_done[chan];
   endfunction // is_dma_to_cl_done
   
   function bit is_dma_to_buffer_done(input int chan); // 1 = done
      return c2h_dma_done[chan];
   endfunction // is_dma_to_buffer_done
   
   //=================================================
   //
   // sh->cl xdma Interface
   //
   //=================================================

   always @(negedge rst_n or posedge clk_core) begin
      if (!rst_n) begin
         h2c_dma_started <= 4'b0;
         c2h_dma_started <= 4'b0;
      end
      else begin
         AXI_Command axi_cmd;
         AXI_Data    axi_data;
         DMA_OP      dop;
         logic [63:0] host_memory;
         int num_of_data_beats;
         int byte_cnt;
         int num_bytes;
         logic [63:0] aligned_addr;
         bit last_beat;
         logic [5:0] start_addr;
         bit aligned;
         bit last_data_beat;
         
         num_of_data_beats = 0;
         last_data_beat    = 0;
         byte_cnt          = 0;
         num_bytes         = 0;
         aligned_addr      = 0;
         last_beat         = 0;
         start_addr        = 0;
         aligned           = 0;
         
         for (int chan = 0; chan < 4; chan++) begin
           if ((h2c_dma_started[chan] != 1'b0) && (h2c_dma_list[chan].size() > 0)) begin
              dop = h2c_dma_list[chan].pop_front();                          
         
              aligned_addr =  {dop.cl_addr[63:6], 6'h00};
              num_of_data_beats = ((dop.len + dop.cl_addr[5:0] - 1)/64) + 1;
              byte_cnt = 0;
              last_beat = ((dop.len + dop.cl_addr[5:0])%64 > 0);
              start_addr = dop.cl_addr[5:0];
              aligned = (aligned_addr == dop.cl_addr);

              for(int burst_cnt=0; burst_cnt < num_of_data_beats; ) begin
                if(burst_cnt == 0) begin   // if first data beat
                  axi_cmd.addr = dop.cl_addr;
                  axi_cmd.len  = aligned ? (num_of_data_beats - 1 - last_beat) : 0;
                  // handle the condition if addr is crossing 4k page boundry
                  if(aligned  && (dop.cl_addr[11:0] + ((axi_cmd.len + 1) * 64) > 4095)) begin 
                    axi_cmd.len = ((4096 - dop.cl_addr[11:0])/64) - 1;
                  end
                end
                else if((num_of_data_beats - 1) - burst_cnt == 0) begin  // last data beat
                  axi_cmd.addr = (aligned_addr + (burst_cnt * 64));
                  axi_cmd.len  = 0;
                end
                else begin                                              // intermediate data beats
                  axi_cmd.addr = (aligned_addr + (burst_cnt * 64));
                  axi_cmd.len  = num_of_data_beats - last_beat - burst_cnt - 1;
                  // handle the condition if addr is crossing 4k page boundry
                  if( (aligned_addr[11:0] + ((axi_cmd.len + 1) * 64)) > 4095) begin
                    axi_cmd.len = ((4096 - aligned_addr[11:0])/64) - 1;
                  end
                end
                axi_cmd.id   = chan;
                axi_cmd.size = 6;
                sh_cl_wr_cmds.push_back(axi_cmd);

                // loop to do multiple data beats
                for(int j = 0; j <= axi_cmd.len; j++) begin
                  axi_data.data = 0;
                  axi_data.strb = 64'b0;
                  axi_data.id   = chan;
                  last_data_beat = (((num_of_data_beats - 1) - burst_cnt) == 0) ? 1 : 0;              
                  num_bytes = last_beat ? (dop.len + dop.cl_addr[5:0])%64 : 64;
                  axi_data.last = (j == axi_cmd.len) ? 1 : 0;
                  if(last_data_beat)  begin
                    for(int i=0; i < num_bytes; i++) begin
                      axi_data.data = axi_data.data | tb.hm_get_byte(.addr(dop.buffer + byte_cnt)) << 8*i;
                      axi_data.strb = axi_data.strb | 1 << i;
                      byte_cnt++;
                    end
                  end
                  else begin
                    for(int i=start_addr[5:0]; i < 64; i++) begin
                      axi_data.data = {tb.hm_get_byte(.addr(dop.buffer + byte_cnt)), axi_data.data[511:8]};
                      axi_data.strb = {1'b1, axi_data.strb[63:1]};
                      byte_cnt++;
                    end
                  end
                  sh_cl_wr_data.push_back(axi_data);
                  start_addr = 0;
                  burst_cnt++;
                end // for(int j = 0; j <= axi_cmd.len; j++) begin
              end // for(int burst_cnt=0; burst_cnt < num_of_data_beats; )
           end // if ((h2c_dma_started[chan] != 1'b0) && (h2c_dma_list[chan].size() > 0))
         end // for (int chan = 0; chan < 4; chan++)
      end // else
   end // always

   //=================================================
   //
   // cl->sh xdma data Interface
   //
   //=================================================

   always @(negedge rst_n or posedge clk_core) begin
      if (!rst_n) begin
        c2h_dma_done <= 1'b0;
      end
      else begin
        DMA_OP dop;
        static int byte_cnt[4];
        
        for (int chan = 0; chan < 4; chan++) begin
          if((cl_sh_rd_data.size() > 0) && (c2h_dma_started[chan] != 1'b0)) begin
            if(chan == cl_sh_rd_data[0].id) begin
              dop = c2h_data_dma_list[chan].pop_front();            
              
              for (int i = dop.cl_addr[5:0]; i < 64 ; i++) begin
                tb.hm_put_byte(.addr(dop.buffer + byte_cnt[chan]), .d(cl_sh_rd_data[0].data[(i*8)+:8]));
                if (debug) begin
                  $display("[%t] - DEBUG read data  dop.buffer[%2d]: %0x  read_que data: %0x", 
                                            $realtime, i, dop.buffer[i], cl_sh_rd_data[0].data[(i*8)+:8]);
                end
                byte_cnt[chan]++;
              end
              c2h_dma_done[chan] = 1'b1;
              cl_sh_rd_data.pop_front();
            end
          end
        end
      end
   end
  
   //=================================================
   //
   // cl->sh xdma Interface
   //
   //=================================================

   always @(negedge rst_n or posedge clk_core) begin
      if (!rst_n) begin
         h2c_dma_started <= 4'b0;
         c2h_dma_started <= 4'b0;
      end
      else begin
         AXI_Command axi_cmd;
         AXI_Data    axi_data;
         DMA_OP      dop;
         DMA_OP      data_dop;
         int num_of_data_beats;
         bit aligned;
         logic [63:0] aligned_addr;
         bit last_beat;

         num_of_data_beats = 0;
         aligned = 0;
         aligned_addr = 0;
         last_beat = 0;

         for (int chan = 0; chan < 4; chan++) begin
           if ((c2h_dma_started[chan] != 1'b0) && (c2h_dma_list[chan].size() > 0)) begin
              dop = c2h_dma_list[chan].pop_front();
              num_of_data_beats = ((dop.len + dop.cl_addr[5:0] - 1)/64) + 1;
              aligned_addr =  {dop.cl_addr[63:6], 6'h00};
              aligned = (aligned_addr == dop.cl_addr);
              last_beat = ((dop.len + dop.cl_addr[5:0])%64 > 0);

              for(int burst_cnt=0; burst_cnt < num_of_data_beats; ) begin
                if(burst_cnt == 0) begin   // if first data beat
                  axi_cmd.addr = dop.cl_addr;
                  axi_cmd.len  = aligned ? (num_of_data_beats - 1 - last_beat) : 0;
                  // handle the condition if addr is crossing 4k page boundry
                  if(aligned  && (dop.cl_addr[11:0] + ((axi_cmd.len + 1) * 64) > 4095)) begin
                    axi_cmd.len = ((4096 - dop.cl_addr[11:0])/64) - 1;
                  end
                  axi_cmd.id   = chan;
                end
                else if((num_of_data_beats - 1) - burst_cnt == 0) begin  // last data beat
                  axi_cmd.addr = (aligned_addr + (burst_cnt * 64));
                  axi_cmd.len  = 0;
                  axi_cmd.id   = chan;
                end
                else begin                                              // intermediate data beats
                  axi_cmd.addr = (aligned_addr + (burst_cnt * 64));
                  axi_cmd.len  = num_of_data_beats - last_beat - burst_cnt - 1;
                  // handle the condition if addr is crossing 4k page boundry
                  if( (aligned_addr[11:0] + ((axi_cmd.len + 1) * 64)) > 4095) begin
                    axi_cmd.len = ((4096 - aligned_addr[11:0])/64) - 1;
                  end
                  axi_cmd.id   = chan;
                end
                axi_cmd.size = 6;
                sh_cl_rd_cmds.push_back(axi_cmd);
                for(int i = 0; i <= axi_cmd.len; i++) begin
                  data_dop.buffer = dop.buffer;
                  data_dop.cl_addr = (axi_cmd.addr + (i*64));
                  data_dop.len = dop.len;
                  c2h_data_dma_list[chan].push_back(data_dop);
                  burst_cnt++;
                end // for(int i = 0; i <= axi_cmd.len; i++)
              end // for(int burst_cnt=0; burst_cnt < num_of_data_beats; )
           end // if ((c2h_dma_started[chan] != 1'b0) && (c2h_dma_list[chan].size() > 0))
         end // for (int chan = 0; chan < 4; chan++)
      end // else begin
   end // always

  task poke_stat(input logic [7:0] addr, logic [1:0] ddr_idx, logic[31:0] data);
     case (ddr_idx)
       0: begin
          sh_ddr_stat_wr0    = 1;
          sh_ddr_stat_addr0  = addr;
          sh_ddr_stat_wdata0 = data;
          sh_ddr_stat_rd0    = 0;
          #8ns;
          sh_ddr_stat_wr0    = 0;
       end
       1: begin
          sh_ddr_stat_wr1    = 1;
          sh_ddr_stat_addr1  = addr;
          sh_ddr_stat_wdata1 = data;
          sh_ddr_stat_rd1    = 0;
          #8ns;
          sh_ddr_stat_wr1    = 0;
       end
       2: begin
          sh_ddr_stat_wr2    = 1;
          sh_ddr_stat_addr2  = addr;
          sh_ddr_stat_wdata2 = data;
          sh_ddr_stat_rd2    = 0;
          #8ns;
          sh_ddr_stat_wr2    = 0;
       end
     endcase // case (ddr_idx)
     
  endtask

endmodule // sh_bfm
