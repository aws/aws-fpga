// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// =============================================================================

module tb();

   parameter NUM_DDR = 4;
   parameter NUM_HMC = 4;
   parameter NUM_PCIE = 1;
   parameter NUM_GTY = 4;
   parameter NUM_I2C = 2;
   parameter NUM_POWER = 4;

   logic clk_main_a0;
   logic clk_extra_a1;
   logic clk_extra_a2;
   logic clk_extra_a3;
   logic clk_extra_b0;
   logic clk_extra_b1;
   logic clk_extra_c0;
   logic clk_extra_c1;
   
   logic rst_out_n; 
   logic clk_xtra;
   logic rst_xtra_n;

   logic [1:0] cfg_max_payload ;               //Max payload size - 00:128B, 01:256B, 10:512B
   logic [2:0] cfg_max_read_req;              //Max read requst size - 000b:128B, 001b:256B, 010b:512B, 011b:1024B

   logic       sh_cl_flr_assert;
   logic       cl_sh_flr_done;
   
   //-------------------------------------
   // PCIe Master interface from CL
   //-------------------------------------
   logic [15:0]          cl_sh_pcim_awid;
   logic [63:0]         cl_sh_pcim_awaddr;
   logic [7:0]          cl_sh_pcim_awlen;
   logic [18:0]         cl_sh_pcim_awuser;
   logic [NUM_PCIE-1:0] cl_sh_pcim_awvalid;
   logic [NUM_PCIE-1:0] sh_cl_pcim_awready;
   
   logic [511:0]        cl_sh_pcim_wdata;
   logic [63:0]         cl_sh_pcim_wstrb;
   logic [NUM_PCIE-1:0] cl_sh_pcim_wlast;
   logic [NUM_PCIE-1:0] cl_sh_pcim_wvalid;
   logic [NUM_PCIE-1:0] sh_cl_pcim_wready;
   
   logic [15:0]          sh_cl_pcim_bid;
   logic [1:0]          sh_cl_pcim_bresp;
   logic [NUM_PCIE-1:0] sh_cl_pcim_bvalid;
   logic [NUM_PCIE-1:0] cl_sh_pcim_bready;
   
   logic [15:0]          cl_sh_pcim_arid ;
   logic [63:0]         cl_sh_pcim_araddr;
   logic [7:0]          cl_sh_pcim_arlen ;
   logic [18:0]         cl_sh_pcim_aruser;
   logic [NUM_PCIE-1:0] cl_sh_pcim_arvalid;
   logic [NUM_PCIE-1:0] sh_cl_pcim_arready;
   
   logic [15:0]          sh_cl_pcim_rid ;
   logic [511:0]        sh_cl_pcim_rdata;
   logic [1:0]          sh_cl_pcim_rresp;
   logic [NUM_PCIE-1:0] sh_cl_pcim_rlast;
   logic [NUM_PCIE-1:0] sh_cl_pcim_rvalid;
   logic [NUM_PCIE-1:0] cl_sh_pcim_rready;

   //------------------------------------------------
   // PCI Slave interface to CL
   //------------------------------------------------
   logic [63:0]         sh_cl_dma_pcis_awaddr;
   logic [5:0]          sh_cl_dma_pcis_awid;
   logic [7:0]          sh_cl_dma_pcis_awlen;
   logic [NUM_PCIE-1:0] sh_cl_dma_pcis_awvalid;
   logic [NUM_PCIE-1:0] cl_sh_dma_pcis_awready;

   logic [511:0]        sh_cl_dma_pcis_wdata;
   logic [63:0]         sh_cl_dma_pcis_wstrb;
   logic [NUM_PCIE-1:0] sh_cl_dma_pcis_wlast;
   logic [NUM_PCIE-1:0] sh_cl_dma_pcis_wvalid;
   logic [NUM_PCIE-1:0] cl_sh_dma_pcis_wready;
   
   logic [1:0]          cl_sh_dma_pcis_bresp;
   logic [5:0]          cl_sh_dma_pcis_bid;
   logic [NUM_PCIE-1:0] cl_sh_dma_pcis_bvalid;
   logic [NUM_PCIE-1:0] sh_cl_dma_pcis_bready;
   
   logic [63:0]         sh_cl_dma_pcis_araddr;
   logic [5:0]          sh_cl_dma_pcis_arid;
   logic [7:0]          sh_cl_dma_pcis_arlen;
   logic [NUM_PCIE-1:0] sh_cl_dma_pcis_arvalid;
   logic [NUM_PCIE-1:0] cl_sh_dma_pcis_arready;
   
   logic [5:0]          cl_sh_dma_pcis_rid;
   logic [511:0]        cl_sh_dma_pcis_rdata;
   logic [1:0]          cl_sh_dma_pcis_rresp;
   logic [NUM_PCIE-1:0] cl_sh_dma_pcis_rlast;
   logic [NUM_PCIE-1:0] cl_sh_dma_pcis_rvalid;
   logic [NUM_PCIE-1:0] sh_cl_dma_pcis_rready;

   
   logic                sh_cl_ddr_is_ready;
   logic [7:0]          sh_ddr_stat_addr[2:0];
   logic [2:0]          sh_ddr_stat_wr;
   logic [2:0]          sh_ddr_stat_rd;
   logic [31:0]         sh_ddr_stat_wdata[2:0];
   logic [2:0]          ddr_sh_stat_ack;
   logic [31:0]         ddr_sh_stat_rdata[2:0];
   logic [7:0]          ddr_sh_stat_int[2:0];
  
   logic [15:0]         cl_sh_irq_req;
   logic [15:0]         sh_cl_irq_ack;
`include "tb_ddr.svh"
   

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




   //------------------------------------------------------
   // HMC Stat Interface from CL
   //------------------------------------------------------
   
   logic [7:0]          sh_hmc_stat_addr;
   logic                sh_hmc_stat_wr;
   logic                sh_hmc_stat_rd;
   logic [31:0]         sh_hmc_stat_wdata;   
   logic                hmc_sh_stat_ack;
   logic [31:0]         hmc_sh_stat_rdata;
   logic [7:0]          hmc_sh_stat_int;
   
   //------------------------------------------------------
   // HMC Stat Interface from CL
   //------------------------------------------------------
   
   logic                hmc_iic_scl_i;
   logic                hmc_iic_scl_o;
   logic                hmc_iic_scl_t;
   logic                hmc_iic_sda_i;
   logic                hmc_iic_sda_o;
   logic                hmc_iic_sda_t;
                              
   //------------------------------------------------------
   // Aurora Stat Interface from CL
   //------------------------------------------------------
   
   logic [7:0]          sh_aurora_stat_addr;
   logic                sh_aurora_stat_wr; 
   logic                sh_aurora_stat_rd; 
   logic [31:0]         sh_aurora_stat_wdata; 
   logic                aurora_sh_stat_ack;
   logic [31:0]         aurora_sh_stat_rdata;
   logic [7:0]          aurora_sh_stat_int;
   
   logic [31:0]         sv_host_memory[*];
   logic                use_c_host_memory = 1'b0;
   
`ifdef VCS
initial begin
   if (!$test$plusargs("NO_WAVES")) begin
      $vcdpluson;
      $vcdplusmemon;
   end
end
`endif

`include "sh_dpi_tasks.svh"
   

   
endmodule // tb

`ifdef XILINX_SIMULATOR
  module short(in1, in1);
    inout in1;
  endmodule
`endif

