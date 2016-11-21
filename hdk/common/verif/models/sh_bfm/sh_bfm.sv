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
   
   initial begin
      clk_out = 1'b0;      
      forever #2ns clk_out = ~clk_out;
   end
   
   initial begin
      clk_xtra = 1'b0;      
      forever #4ns clk_xtra = ~clk_xtra;
   end

   logic rst_out_n_i;
   logic rst_xtra_n_i;

   always @(posedge clk_out)
     rst_out_n <= rst_out_n_i;
   
   always @(posedge clk_xtra)
     rst_xtra_n <= rst_xtra_n_i;

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

   
   task power_up;
      rst_out_n_i = 1'b0;
      rst_xtra_n_i = 1'b0;
      #5000ns;
      rst_out_n_i = 1'b1;
      rst_xtra_n_i = 1'b1;
      #50ns;
   endtask // power_up
   
   task power_down;
      #50ns;
      rst_out_n_i = 1'b0;
      rst_xtra_n_i = 1'b0;
      #50ns;
   endtask // power_down

   task poke(input logic [63:0] addr, logic [31:0] dat);
      AXI_Command cmd;
      AXI_Data data;
      logic [1:0] resp;
      
      cmd.addr = addr;
      cmd.len  = 0;
      cmd.id   = 2;

      sh_cl_wr_cmds.push_back(cmd);

      data.data = dat;
      data.strb = 'h0f;
      data.id   = 2;
      data.last = 1'b1;

      #20ns sh_cl_wr_data.push_back(data);
      
      while (cl_sh_b_resps.size() == 0)
        #20ns;
      
      resp = cl_sh_b_resps[0].resp;
      cl_sh_b_resps.pop_front();
      
   endtask // poke

   task peek(input logic [63:0] addr, output [31:0] data);
      AXI_Command cmd;

      cmd.addr = addr;
      cmd.len  = 0;
      cmd.id   = 1;

      sh_cl_rd_cmds.push_back(cmd);

//      wait(cl_sh_rd_data.size() > 0);   // TBD: This doesn't work for XSIM
      while (cl_sh_rd_data.size() == 0)
        #20ns;
      
      data = cl_sh_rd_data[0].data;
      cl_sh_rd_data.pop_front();
      
   endtask // peek
   
endmodule // sh_bfm
