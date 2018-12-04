// Amazon FPGA Hardware Development Kit
//
// Copyright 2016-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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


// CL Streaming


module  cl_sde

  (
`include "cl_ports.vh"
   );

   logic clk;
   assign clk = clk_main_a0;
   assign rst_n = rst_main_n;

`ifndef CL_VERSION
   `define CL_VERSION 32'h10df_f002
`endif

`include "cl_id_defines.vh"

   assign cl_sh_id0 = `CL_SH_ID0;
   assign cl_sh_id1 = `CL_SH_ID1;

   logic h2c_axis_valid;
   logic [511:0] h2c_axis_data;
   logic [63:0]  h2c_axis_keep;
   logic         h2c_axis_last;
   logic         h2c_axis_ready;
   logic [63:0]  h2c_axis_user;

   logic         c2h_axis_valid;
   logic [511:0] c2h_axis_data;
   logic [63:0]  c2h_axis_keep;
   logic         c2h_axis_last;
   logic         c2h_axis_ready;
   logic [63:0]  c2h_axis_user;

   logic         sh_ocl_awvalid_q;
   logic [31:0]  sh_ocl_awaddr_q;
   logic         ocl_sh_awready_q;
   logic         sh_ocl_wvalid_q;
   logic [31:0]  sh_ocl_wdata_q;
   logic [ 3:0]  sh_ocl_wstrb_q;
   logic         ocl_sh_wready_q;
   logic         ocl_sh_bvalid_q;
   logic [ 1:0]  ocl_sh_bresp_q;
   logic         sh_ocl_bready_q;
   logic         sh_ocl_arvalid_q;
   logic [31:0]  sh_ocl_araddr_q;
   logic         ocl_sh_arready_q;
   logic         ocl_sh_rvalid_q;
   logic [31:0]  ocl_sh_rdata_q;
   logic [ 1:0]  ocl_sh_rresp_q;
   logic         sh_ocl_rready_q;

   logic         sh_ocl_awvalid_q2;
   logic [31:0]  sh_ocl_awaddr_q2;
   logic         ocl_sh_awready_q2;
   logic         sh_ocl_wvalid_q2;
   logic [31:0]  sh_ocl_wdata_q2;
   logic [ 3:0]  sh_ocl_wstrb_q2;
   logic         ocl_sh_wready_q2;
   logic         ocl_sh_bvalid_q2;
   logic [ 1:0]  ocl_sh_bresp_q2;
   logic         sh_ocl_bready_q2;
   logic         sh_ocl_arvalid_q2;
   logic [31:0]  sh_ocl_araddr_q2;
   logic         ocl_sh_arready_q2;
   logic         ocl_sh_rvalid_q2;
   logic [31:0]  ocl_sh_rdata_q2;
   logic [ 1:0]  ocl_sh_rresp_q2;
   logic         sh_ocl_rready_q2;

   logic [11:0]  cfg_srm_addr;
   logic         cfg_srm_wr;
   logic         cfg_srm_rd;
   logic [31:0]  cfg_srm_wdata;
   logic         srm_cfg_ack;
   logic [31:0]  srm_cfg_rdata;

   logic [15:0]   sh_cl_dma_pcis_awid_q   ;
   logic [63:0]  sh_cl_dma_pcis_awaddr_q ;
   logic [7:0]   sh_cl_dma_pcis_awlen_q  ;
   logic [2:0]   sh_cl_dma_pcis_awsize_q ;
   logic         sh_cl_dma_pcis_awvalid_q;
   logic         cl_sh_dma_pcis_awready_q;
   logic [511:0] sh_cl_dma_pcis_wdata_q  ;
   logic [63:0]  sh_cl_dma_pcis_wstrb_q  ;
   logic         sh_cl_dma_pcis_wlast_q  ;
   logic         sh_cl_dma_pcis_wvalid_q ;
   logic         cl_sh_dma_pcis_wready_q ;
   logic [15:0]   cl_sh_dma_pcis_bid_q    ;
   logic [1:0]   cl_sh_dma_pcis_bresp_q  ;
   logic         cl_sh_dma_pcis_bvalid_q ;
   logic         sh_cl_dma_pcis_bready_q ;
   logic [15:0]   sh_cl_dma_pcis_arid_q   ;
   logic [63:0]  sh_cl_dma_pcis_araddr_q ;
   logic [7:0]   sh_cl_dma_pcis_arlen_q  ;
   logic [2:0]   sh_cl_dma_pcis_arsize_q ;
   logic         sh_cl_dma_pcis_arvalid_q;
   logic         cl_sh_dma_pcis_arready_q;
   logic [15:0]   cl_sh_dma_pcis_rid_q    ;
   logic [511:0] cl_sh_dma_pcis_rdata_q  ;
   logic [1:0]   cl_sh_dma_pcis_rresp_q  ;
   logic         cl_sh_dma_pcis_rlast_q  ;
   logic         cl_sh_dma_pcis_rvalid_q ;
   logic         sh_cl_dma_pcis_rready_q ;

   logic [15:0] sh_cl_dma_pcis_awid_q2   ;
   logic [63:0] sh_cl_dma_pcis_awaddr_q2 ;
   logic [7:0]  sh_cl_dma_pcis_awlen_q2  ;
   logic [2:0]  sh_cl_dma_pcis_awsize_q2 ;
   logic        sh_cl_dma_pcis_awvalid_q2;
   logic        cl_sh_dma_pcis_awready_q2;
   logic [511:0] sh_cl_dma_pcis_wdata_q2  ;
   logic [63:0]  sh_cl_dma_pcis_wstrb_q2  ;
   logic         sh_cl_dma_pcis_wlast_q2  ;
   logic         sh_cl_dma_pcis_wvalid_q2 ;
   logic         cl_sh_dma_pcis_wready_q2 ;
   logic [15:0]   cl_sh_dma_pcis_bid_q2    ;
   logic [1:0]   cl_sh_dma_pcis_bresp_q2  ;
   logic         cl_sh_dma_pcis_bvalid_q2 ;
   logic         sh_cl_dma_pcis_bready_q2 ;
   logic [15:0]   sh_cl_dma_pcis_arid_q2   ;
   logic [63:0]  sh_cl_dma_pcis_araddr_q2 ;
   logic [7:0]   sh_cl_dma_pcis_arlen_q2  ;
   logic [2:0]   sh_cl_dma_pcis_arsize_q2 ;
   logic         sh_cl_dma_pcis_arvalid_q2;
   logic         cl_sh_dma_pcis_arready_q2;
   logic [15:0]   cl_sh_dma_pcis_rid_q2    ;
   logic [511:0] cl_sh_dma_pcis_rdata_q2  ;
   logic [1:0]   cl_sh_dma_pcis_rresp_q2  ;
   logic         cl_sh_dma_pcis_rlast_q2  ;
   logic         cl_sh_dma_pcis_rvalid_q2 ;
   logic         sh_cl_dma_pcis_rready_q2 ;

   logic         cl_sh_pcim_awvalid_q ;
   logic [15:0]  cl_sh_pcim_awid_q    ;
   logic [63:0]  cl_sh_pcim_awaddr_q  ;
   logic [7:0]   cl_sh_pcim_awlen_q   ;
   logic [2:0]   cl_sh_pcim_awsize_q  ;
   logic         sh_cl_pcim_awready_q ;
   logic         cl_sh_pcim_wvalid_q  ;
   logic [511:0] cl_sh_pcim_wdata_q   ;
   logic [63:0]  cl_sh_pcim_wstrb_q   ;
   logic         cl_sh_pcim_wlast_q   ;
   logic         sh_cl_pcim_wready_q  ;
   logic         sh_cl_pcim_bvalid_q  ;
   logic [15:0]  sh_cl_pcim_bid_q     ;
   logic [1:0]   sh_cl_pcim_bresp_q   ;
   logic         cl_sh_pcim_bready_q  ;
   logic         cl_sh_pcim_arvalid_q ;
   logic [15:0]  cl_sh_pcim_arid_q    ;
   logic [63:0]  cl_sh_pcim_araddr_q  ;
   logic [7:0]   cl_sh_pcim_arlen_q   ;
   logic [2:0]   cl_sh_pcim_arsize_q  ;
   logic         sh_cl_pcim_arready_q ;
   logic         sh_cl_pcim_rvalid_q  ;
   logic [15:0]  sh_cl_pcim_rid_q     ;
   logic [511:0] sh_cl_pcim_rdata_q   ;
   logic [1:0]   sh_cl_pcim_rresp_q   ;
   logic         sh_cl_pcim_rlast_q   ;
   logic         cl_sh_pcim_rready_q  ;

   logic         rst_main_n_sync;

   logic         sde_awvalid_q ;
   logic [15:0]  sde_awid_q    ;
   logic [63:0]  sde_awaddr_q  ;
   logic [7:0]   sde_awlen_q   ;
   logic [2:0]   sde_awsize_q  ;
   logic         sde_awready_q ;
   logic         sde_wvalid_q  ;
   logic [511:0] sde_wdata_q   ;
   logic [63:0]  sde_wstrb_q   ;
   logic         sde_wlast_q   ;
   logic         sde_wready_q  ;
   logic         sde_bvalid_q  ;
   logic [2:0]   sde_bid_q     ;
   logic [1:0]   sde_bresp_q   ;
   logic         sde_bready_q  ;
   logic         sde_arvalid_q ;
   logic [15:0]  sde_arid_q    ;
   logic [63:0]  sde_araddr_q  ;
   logic [7:0]   sde_arlen_q   ;
   logic [2:0]   sde_arsize_q  ;
   logic         sde_arready_q ;
   logic         sde_rvalid_q  ;
   logic [2:0]   sde_rid_q     ;
   logic [511:0] sde_rdata_q   ;
   logic [1:0]   sde_rresp_q   ;
   logic         sde_rlast_q   ;
   logic         sde_rready_q  ;

   logic [2:0]   pre_sde_arid_q;
   logic [2:0]   pre_sde_rid_q;

`include "unused_flr_template.inc"
`include "unused_ddr_a_b_d_template.inc"
`include "unused_ddr_c_template.inc"
`include "unused_cl_sda_template.inc"
`include "unused_sh_bar1_template.inc"
`include "unused_apppf_irq_template.inc"

//-------------------------------------------------
// Reset Synchronization
//-------------------------------------------------

logic pre_sync_rst_n;

always @(posedge clk_main_a0)
   if (!rst_main_n)
   begin
      pre_sync_rst_n  <= 0;
      rst_main_n_sync <= 0;
   end
   else
   begin
      pre_sync_rst_n  <= 1;
      rst_main_n_sync <= pre_sync_rst_n;
   end

(* dont_touch = "true" *)    logic         rst_main_n_sync_bot_slr;
   lib_pipe #(.WIDTH(1), .STAGES(2)) PIPE_RST_N_BOT_SLR (.clk(clk_main_a0), .rst_n(1'b1), .in_bus(rst_main_n_sync), .out_bus(rst_main_n_sync_bot_slr));

(* dont_touch = "true" *)    logic         rst_main_n_sync_mid_slr;
   lib_pipe #(.WIDTH(1), .STAGES(4)) PIPE_RST_N_MID_SLR (.clk(clk_main_a0), .rst_n(1'b1), .in_bus(rst_main_n_sync), .out_bus(rst_main_n_sync_mid_slr));

 axi_register_slice_light AXIL_OCL_REG_SLC_BOT_SLR (
   .aclk          (clk_main_a0),
   .aresetn       (rst_main_n_sync_bot_slr),
   .s_axi_awaddr  (sh_ocl_awaddr),
   .s_axi_awprot   (2'h0),
   .s_axi_awvalid (sh_ocl_awvalid),
   .s_axi_awready (ocl_sh_awready),
   .s_axi_wdata   (sh_ocl_wdata),
   .s_axi_wstrb   (sh_ocl_wstrb),
   .s_axi_wvalid  (sh_ocl_wvalid),
   .s_axi_wready  (ocl_sh_wready),
   .s_axi_bresp   (ocl_sh_bresp),
   .s_axi_bvalid  (ocl_sh_bvalid),
   .s_axi_bready  (sh_ocl_bready),
   .s_axi_araddr  (sh_ocl_araddr),
   .s_axi_arvalid (sh_ocl_arvalid),
   .s_axi_arready (ocl_sh_arready),
   .s_axi_rdata   (ocl_sh_rdata),
   .s_axi_rresp   (ocl_sh_rresp),
   .s_axi_rvalid  (ocl_sh_rvalid),
   .s_axi_rready  (sh_ocl_rready),
   .m_axi_awaddr  (sh_ocl_awaddr_q),
   .m_axi_awprot  (),
   .m_axi_awvalid (sh_ocl_awvalid_q),
   .m_axi_awready (ocl_sh_awready_q),
   .m_axi_wdata   (sh_ocl_wdata_q),
   .m_axi_wstrb   (sh_ocl_wstrb_q),
   .m_axi_wvalid  (sh_ocl_wvalid_q),
   .m_axi_wready  (ocl_sh_wready_q),
   .m_axi_bresp   (ocl_sh_bresp_q),
   .m_axi_bvalid  (ocl_sh_bvalid_q),
   .m_axi_bready  (sh_ocl_bready_q),
   .m_axi_araddr  (sh_ocl_araddr_q),
   .m_axi_arvalid (sh_ocl_arvalid_q),
   .m_axi_arready (ocl_sh_arready_q),
   .m_axi_rdata   (ocl_sh_rdata_q),
   .m_axi_rresp   (ocl_sh_rresp_q),
   .m_axi_rvalid  (ocl_sh_rvalid_q),
   .m_axi_rready  (sh_ocl_rready_q)
  );

 axi_register_slice_light AXIL_OCL_REG_SLC_MID_SLR (
   .aclk          (clk_main_a0),
   .aresetn       (rst_main_n_sync_mid_slr),
   .s_axi_awaddr  (sh_ocl_awaddr_q),
   .s_axi_awprot   (2'h0),
   .s_axi_awvalid (sh_ocl_awvalid_q),
   .s_axi_awready (ocl_sh_awready_q),
   .s_axi_wdata   (sh_ocl_wdata_q),
   .s_axi_wstrb   (sh_ocl_wstrb_q),
   .s_axi_wvalid  (sh_ocl_wvalid_q),
   .s_axi_wready  (ocl_sh_wready_q),
   .s_axi_bresp   (ocl_sh_bresp_q),
   .s_axi_bvalid  (ocl_sh_bvalid_q),
   .s_axi_bready  (sh_ocl_bready_q),
   .s_axi_araddr  (sh_ocl_araddr_q),
   .s_axi_arvalid (sh_ocl_arvalid_q),
   .s_axi_arready (ocl_sh_arready_q),
   .s_axi_rdata   (ocl_sh_rdata_q),
   .s_axi_rresp   (ocl_sh_rresp_q),
   .s_axi_rvalid  (ocl_sh_rvalid_q),
   .s_axi_rready  (sh_ocl_rready_q),
   .m_axi_awaddr  (sh_ocl_awaddr_q2),
   .m_axi_awprot  (),
   .m_axi_awvalid (sh_ocl_awvalid_q2),
   .m_axi_awready (ocl_sh_awready_q2),
   .m_axi_wdata   (sh_ocl_wdata_q2),
   .m_axi_wstrb   (sh_ocl_wstrb_q2),
   .m_axi_wvalid  (sh_ocl_wvalid_q2),
   .m_axi_wready  (ocl_sh_wready_q2),
   .m_axi_bresp   (ocl_sh_bresp_q2),
   .m_axi_bvalid  (ocl_sh_bvalid_q2),
   .m_axi_bready  (sh_ocl_bready_q2),
   .m_axi_araddr  (sh_ocl_araddr_q2),
   .m_axi_arvalid (sh_ocl_arvalid_q2),
   .m_axi_arready (ocl_sh_arready_q2),
   .m_axi_rdata   (ocl_sh_rdata_q2),
   .m_axi_rresp   (ocl_sh_rresp_q2),
   .m_axi_rvalid  (ocl_sh_rvalid_q2),
   .m_axi_rready  (sh_ocl_rready_q2)
  );


//-------------------------------------
// flop the output of ATG
//-------------------------------------
   // AXI4 register slice - For signals between CL and HL
   axi_register_slice PCIM_REG_SLC_MID_SLR (
     .aclk           (clk_main_a0),
     .aresetn        (rst_main_n_sync_mid_slr),

     .s_axi_awid     (cl_sh_pcim_awid_q    ),
     .s_axi_awaddr   (cl_sh_pcim_awaddr_q  ),
     .s_axi_awlen    (cl_sh_pcim_awlen_q   ),
     .s_axi_awsize   (cl_sh_pcim_awsize_q  ),
     .s_axi_awvalid  (cl_sh_pcim_awvalid_q ),
     .s_axi_awready  (sh_cl_pcim_awready_q ),
     .s_axi_wdata    (cl_sh_pcim_wdata_q   ),
     .s_axi_wstrb    (cl_sh_pcim_wstrb_q   ),
     .s_axi_wlast    (cl_sh_pcim_wlast_q   ),
     .s_axi_wvalid   (cl_sh_pcim_wvalid_q  ),
     .s_axi_wready   (sh_cl_pcim_wready_q  ),
     .s_axi_bid      (sh_cl_pcim_bid_q     ),
     .s_axi_bresp    (sh_cl_pcim_bresp_q   ),
     .s_axi_bvalid   (sh_cl_pcim_bvalid_q  ),
     .s_axi_bready   (cl_sh_pcim_bready_q  ),
     .s_axi_arid     (cl_sh_pcim_arid_q    ),
     .s_axi_araddr   (cl_sh_pcim_araddr_q  ),
     .s_axi_arlen    (cl_sh_pcim_arlen_q   ),
     .s_axi_arsize   (cl_sh_pcim_arsize_q  ),
     .s_axi_arvalid  (cl_sh_pcim_arvalid_q ),
     .s_axi_arready  (sh_cl_pcim_arready_q ),
     .s_axi_rid      (sh_cl_pcim_rid_q     ),
     .s_axi_rdata    (sh_cl_pcim_rdata_q   ),
     .s_axi_rresp    (sh_cl_pcim_rresp_q   ),
     .s_axi_rlast    (sh_cl_pcim_rlast_q   ),
     .s_axi_rvalid   (sh_cl_pcim_rvalid_q  ),
     .s_axi_rready   (cl_sh_pcim_rready_q  ),

     .m_axi_awid     (cl_sh_pcim_awid    ),
     .m_axi_awaddr   (cl_sh_pcim_awaddr  ),
     .m_axi_awlen    (cl_sh_pcim_awlen   ),
     .m_axi_awsize   (cl_sh_pcim_awsize  ),
     .m_axi_awvalid  (cl_sh_pcim_awvalid ),
     .m_axi_awready  (sh_cl_pcim_awready ),
     .m_axi_wdata    (cl_sh_pcim_wdata   ),
     .m_axi_wstrb    (cl_sh_pcim_wstrb   ),
     .m_axi_wlast    (cl_sh_pcim_wlast   ),
     .m_axi_wvalid   (cl_sh_pcim_wvalid  ),
     .m_axi_wready   (sh_cl_pcim_wready  ),
     .m_axi_bid      (sh_cl_pcim_bid     ),
     .m_axi_bresp    (sh_cl_pcim_bresp   ),
     .m_axi_bvalid   (sh_cl_pcim_bvalid  ),
     .m_axi_bready   (cl_sh_pcim_bready  ),
     .m_axi_arid     (cl_sh_pcim_arid    ),
     .m_axi_araddr   (cl_sh_pcim_araddr  ),
     .m_axi_arlen    (cl_sh_pcim_arlen   ),
     .m_axi_arsize   (cl_sh_pcim_arsize  ),
     .m_axi_arvalid  (cl_sh_pcim_arvalid ),
     .m_axi_arready  (sh_cl_pcim_arready ),
     .m_axi_rid      (sh_cl_pcim_rid     ),
     .m_axi_rdata    (sh_cl_pcim_rdata   ),
     .m_axi_rresp    (sh_cl_pcim_rresp   ),
     .m_axi_rlast    (sh_cl_pcim_rlast   ),
     .m_axi_rvalid   (sh_cl_pcim_rvalid  ),
     .m_axi_rready   (cl_sh_pcim_rready  )
     );

   axi_register_slice PCIS_REG_SLC_BOT_SLR (
     .aclk           (clk_main_a0),
     .aresetn        (rst_main_n_sync_bot_slr),

     .s_axi_awid     (sh_cl_dma_pcis_awid    ),
     .s_axi_awaddr   (sh_cl_dma_pcis_awaddr  ),
     .s_axi_awlen    (sh_cl_dma_pcis_awlen   ),
     .s_axi_awsize   (sh_cl_dma_pcis_awsize  ),
     .s_axi_awvalid  (sh_cl_dma_pcis_awvalid ),
     .s_axi_awready  (cl_sh_dma_pcis_awready ),
     .s_axi_wdata    (sh_cl_dma_pcis_wdata   ),
     .s_axi_wstrb    (sh_cl_dma_pcis_wstrb   ),
     .s_axi_wlast    (sh_cl_dma_pcis_wlast   ),
     .s_axi_wvalid   (sh_cl_dma_pcis_wvalid  ),
     .s_axi_wready   (cl_sh_dma_pcis_wready  ),
     .s_axi_bid      (cl_sh_dma_pcis_bid     ),
     .s_axi_bresp    (cl_sh_dma_pcis_bresp   ),
     .s_axi_bvalid   (cl_sh_dma_pcis_bvalid  ),
     .s_axi_bready   (sh_cl_dma_pcis_bready  ),
     .s_axi_arid     (sh_cl_dma_pcis_arid    ),
     .s_axi_araddr   (sh_cl_dma_pcis_araddr  ),
     .s_axi_arlen    (sh_cl_dma_pcis_arlen   ),
     .s_axi_arsize   (sh_cl_dma_pcis_arsize  ),
     .s_axi_arvalid  (sh_cl_dma_pcis_arvalid ),
     .s_axi_arready  (cl_sh_dma_pcis_arready ),
     .s_axi_rid      (cl_sh_dma_pcis_rid     ),
     .s_axi_rdata    (cl_sh_dma_pcis_rdata   ),
     .s_axi_rresp    (cl_sh_dma_pcis_rresp   ),
     .s_axi_rlast    (cl_sh_dma_pcis_rlast   ),
     .s_axi_rvalid   (cl_sh_dma_pcis_rvalid  ),
     .s_axi_rready   (sh_cl_dma_pcis_rready  ),

     .m_axi_awid     (sh_cl_dma_pcis_awid_q    ),
     .m_axi_awaddr   (sh_cl_dma_pcis_awaddr_q  ),
     .m_axi_awlen    (sh_cl_dma_pcis_awlen_q   ),
     .m_axi_awsize   (sh_cl_dma_pcis_awsize_q  ),
     .m_axi_awvalid  (sh_cl_dma_pcis_awvalid_q ),
     .m_axi_awready  (cl_sh_dma_pcis_awready_q ),
     .m_axi_wdata    (sh_cl_dma_pcis_wdata_q   ),
     .m_axi_wstrb    (sh_cl_dma_pcis_wstrb_q   ),
     .m_axi_wlast    (sh_cl_dma_pcis_wlast_q   ),
     .m_axi_wvalid   (sh_cl_dma_pcis_wvalid_q  ),
     .m_axi_wready   (cl_sh_dma_pcis_wready_q  ),
     .m_axi_bid      (cl_sh_dma_pcis_bid_q     ),
     .m_axi_bresp    (cl_sh_dma_pcis_bresp_q   ),
     .m_axi_bvalid   (cl_sh_dma_pcis_bvalid_q  ),
     .m_axi_bready   (sh_cl_dma_pcis_bready_q  ),
     .m_axi_arid     (sh_cl_dma_pcis_arid_q    ),
     .m_axi_araddr   (sh_cl_dma_pcis_araddr_q  ),
     .m_axi_arlen    (sh_cl_dma_pcis_arlen_q   ),
     .m_axi_arsize   (sh_cl_dma_pcis_arsize_q  ),
     .m_axi_arvalid  (sh_cl_dma_pcis_arvalid_q ),
     .m_axi_arready  (cl_sh_dma_pcis_arready_q ),
     .m_axi_rid      (cl_sh_dma_pcis_rid_q     ),
     .m_axi_rdata    (cl_sh_dma_pcis_rdata_q   ),
     .m_axi_rresp    (cl_sh_dma_pcis_rresp_q   ),
     .m_axi_rlast    (cl_sh_dma_pcis_rlast_q   ),
     .m_axi_rvalid   (cl_sh_dma_pcis_rvalid_q  ),
     .m_axi_rready   (sh_cl_dma_pcis_rready_q  )

     );

   axi_register_slice PCIS_REG_SLC_MID_SLR (
     .aclk           (clk_main_a0),
     .aresetn        (rst_main_n_sync_mid_slr),

     .s_axi_awid     (sh_cl_dma_pcis_awid_q    ),
     .s_axi_awaddr   (sh_cl_dma_pcis_awaddr_q  ),
     .s_axi_awlen    (sh_cl_dma_pcis_awlen_q   ),
     .s_axi_awsize   (sh_cl_dma_pcis_awsize_q  ),
     .s_axi_awvalid  (sh_cl_dma_pcis_awvalid_q ),
     .s_axi_awready  (cl_sh_dma_pcis_awready_q ),
     .s_axi_wdata    (sh_cl_dma_pcis_wdata_q   ),
     .s_axi_wstrb    (sh_cl_dma_pcis_wstrb_q   ),
     .s_axi_wlast    (sh_cl_dma_pcis_wlast_q   ),
     .s_axi_wvalid   (sh_cl_dma_pcis_wvalid_q  ),
     .s_axi_wready   (cl_sh_dma_pcis_wready_q  ),
     .s_axi_bid      (cl_sh_dma_pcis_bid_q     ),
     .s_axi_bresp    (cl_sh_dma_pcis_bresp_q   ),
     .s_axi_bvalid   (cl_sh_dma_pcis_bvalid_q  ),
     .s_axi_bready   (sh_cl_dma_pcis_bready_q  ),
     .s_axi_arid     (sh_cl_dma_pcis_arid_q    ),
     .s_axi_araddr   (sh_cl_dma_pcis_araddr_q  ),
     .s_axi_arlen    (sh_cl_dma_pcis_arlen_q   ),
     .s_axi_arsize   (sh_cl_dma_pcis_arsize_q  ),
     .s_axi_arvalid  (sh_cl_dma_pcis_arvalid_q ),
     .s_axi_arready  (cl_sh_dma_pcis_arready_q ),
     .s_axi_rid      (cl_sh_dma_pcis_rid_q     ),
     .s_axi_rdata    (cl_sh_dma_pcis_rdata_q   ),
     .s_axi_rresp    (cl_sh_dma_pcis_rresp_q   ),
     .s_axi_rlast    (cl_sh_dma_pcis_rlast_q   ),
     .s_axi_rvalid   (cl_sh_dma_pcis_rvalid_q  ),
     .s_axi_rready   (sh_cl_dma_pcis_rready_q  ),

     .m_axi_awid     (sh_cl_dma_pcis_awid_q2    ),
     .m_axi_awaddr   (sh_cl_dma_pcis_awaddr_q2  ),
     .m_axi_awlen    (sh_cl_dma_pcis_awlen_q2   ),
     .m_axi_awsize   (sh_cl_dma_pcis_awsize_q2  ),
     .m_axi_awvalid  (sh_cl_dma_pcis_awvalid_q2 ),
     .m_axi_awready  (cl_sh_dma_pcis_awready_q2 ),
     .m_axi_wdata    (sh_cl_dma_pcis_wdata_q2   ),
     .m_axi_wstrb    (sh_cl_dma_pcis_wstrb_q2   ),
     .m_axi_wlast    (sh_cl_dma_pcis_wlast_q2   ),
     .m_axi_wvalid   (sh_cl_dma_pcis_wvalid_q2  ),
     .m_axi_wready   (cl_sh_dma_pcis_wready_q2  ),
     .m_axi_bid      (cl_sh_dma_pcis_bid_q2     ),
     .m_axi_bresp    (cl_sh_dma_pcis_bresp_q2   ),
     .m_axi_bvalid   (cl_sh_dma_pcis_bvalid_q2  ),
     .m_axi_bready   (sh_cl_dma_pcis_bready_q2  ),
     .m_axi_arid     (sh_cl_dma_pcis_arid_q2    ),
     .m_axi_araddr   (sh_cl_dma_pcis_araddr_q2  ),
     .m_axi_arlen    (sh_cl_dma_pcis_arlen_q2   ),
     .m_axi_arsize   (sh_cl_dma_pcis_arsize_q2  ),
     .m_axi_arvalid  (sh_cl_dma_pcis_arvalid_q2 ),
     .m_axi_arready  (cl_sh_dma_pcis_arready_q2 ),
     .m_axi_rid      (cl_sh_dma_pcis_rid_q2     ),
     .m_axi_rdata    (cl_sh_dma_pcis_rdata_q2   ),
     .m_axi_rresp    (cl_sh_dma_pcis_rresp_q2   ),
     .m_axi_rlast    (cl_sh_dma_pcis_rlast_q2   ),
     .m_axi_rvalid   (cl_sh_dma_pcis_rvalid_q2  ),
     .m_axi_rready   (sh_cl_dma_pcis_rready_q2  )

     );

   logic cfg_sde_rst;
   logic sde_rst_n_d;
   logic sde_rst_n;
   logic cfg_sde_wire_loopback;

   assign sde_rst_n_d = ~cfg_sde_rst & rst_main_n_sync_mid_slr;

   lib_pipe #(.WIDTH(1), .STAGES(1)) SDE_RST_LIB_PIPE
     (.clk (clk_main_a0), .rst_n(1'b1), .in_bus(sde_rst_n_d), .out_bus(sde_rst_n));

   logic pcim_wr_incomplete_error;
   logic pcim_wr_last_error;
   always @(posedge clk_main_a0)
     if (!sde_rst_n)
       pcim_wr_incomplete_error <= 0;
     else
       pcim_wr_incomplete_error <= pcim_wr_last_error; /*sh_cl_ctl1[8];*/

`ifndef C2H_BUF_DEPTH
 `define C2H_BUF_DEPTH 512
`endif

`ifndef H2C_BUF_DEPTH
`define H2C_BUF_DEPTH 512
`endif

sde #(.C2H_BUF_DEPTH(`C2H_BUF_DEPTH),
      .H2C_BUF_DEPTH(`H2C_BUF_DEPTH)) SDE
  (.clk                (clk_main_a0),
   .rst_n              (sde_rst_n  ),

   .pcis_awid          (sh_cl_dma_pcis_awid_q2   ),
   .pcis_awaddr        (sh_cl_dma_pcis_awaddr_q2 ),
   .pcis_awlen         (sh_cl_dma_pcis_awlen_q2  ),
   .pcis_awsize        (sh_cl_dma_pcis_awsize_q2 ),
   .pcis_awvalid       (sh_cl_dma_pcis_awvalid_q2),
   .pcis_awready       (cl_sh_dma_pcis_awready_q2),
   .pcis_wdata         (sh_cl_dma_pcis_wdata_q2  ),
   .pcis_wstrb         (sh_cl_dma_pcis_wstrb_q2  ),
   .pcis_wlast         (sh_cl_dma_pcis_wlast_q2  ),
   .pcis_wvalid        (sh_cl_dma_pcis_wvalid_q2 ),
   .pcis_wready        (cl_sh_dma_pcis_wready_q2 ),
   .pcis_bid           (cl_sh_dma_pcis_bid_q2    ),
   .pcis_bresp         (cl_sh_dma_pcis_bresp_q2  ),
   .pcis_bvalid        (cl_sh_dma_pcis_bvalid_q2 ),
   .pcis_bready        (sh_cl_dma_pcis_bready_q2 ),
   .pcis_arid          (sh_cl_dma_pcis_arid_q2   ),
   .pcis_araddr        (sh_cl_dma_pcis_araddr_q2 ),
   .pcis_arlen         (sh_cl_dma_pcis_arlen_q2  ),
   .pcis_arsize        (sh_cl_dma_pcis_arsize_q2 ),
   .pcis_arvalid       (sh_cl_dma_pcis_arvalid_q2),
   .pcis_arready       (cl_sh_dma_pcis_arready_q2),
   .pcis_rid           (cl_sh_dma_pcis_rid_q2    ),
   .pcis_rdata         (cl_sh_dma_pcis_rdata_q2  ),
   .pcis_rresp         (cl_sh_dma_pcis_rresp_q2  ),
   .pcis_rlast         (cl_sh_dma_pcis_rlast_q2  ),
   .pcis_rvalid        (cl_sh_dma_pcis_rvalid_q2 ),
   .pcis_rready        (sh_cl_dma_pcis_rready_q2 ),

   .pcim_awvalid        (sde_awvalid_q ),
   .pcim_awid           (sde_awid_q    ),
   .pcim_awaddr         (sde_awaddr_q  ),
   .pcim_awlen          (sde_awlen_q   ),
   .pcim_awsize         (sde_awsize_q  ),
   .pcim_awready        (sde_awready_q ),
   .pcim_wvalid         (sde_wvalid_q  ),
   .pcim_wdata          (sde_wdata_q   ),
   .pcim_wstrb          (sde_wstrb_q   ),
   .pcim_wlast          (sde_wlast_q   ),
   .pcim_wready         (sde_wready_q  ),
   .pcim_bvalid         (sde_bvalid_q  ),
   .pcim_bid            (sde_bid_q     ),
   .pcim_bresp          (sde_bresp_q   ),
   .pcim_bready         (sde_bready_q  ),
   .pcim_arvalid        (sde_arvalid_q ),
   .pcim_arid           (pre_sde_arid_q),
   .pcim_araddr         (sde_araddr_q  ),
   .pcim_arlen          (sde_arlen_q   ),
   .pcim_arsize         (sde_arsize_q  ),
   .pcim_arready        (sde_arready_q ),
   .pcim_rvalid         (sde_rvalid_q  ),
   .pcim_rid            (pre_sde_rid_q ),
   .pcim_rdata          (sde_rdata_q   ),
   .pcim_rresp          (sde_rresp_q   ),
   .pcim_rlast          (sde_rlast_q   ),
   .pcim_rready         (sde_rready_q  ),

   .c2h_axis_valid      (c2h_axis_valid ),
   .c2h_axis_data       (c2h_axis_data  ),
   .c2h_axis_keep       (c2h_axis_keep  ),
   .c2h_axis_user       (c2h_axis_user  ),
   .c2h_axis_last       (c2h_axis_last  ),
   .c2h_axis_ready      (c2h_axis_ready ),

   .h2c_axis_valid      (h2c_axis_valid ),
   .h2c_axis_data       (h2c_axis_data  ),
   .h2c_axis_keep       (h2c_axis_keep  ),
   .h2c_axis_user       (h2c_axis_user  ),
   .h2c_axis_last       (h2c_axis_last  ),
   .h2c_axis_ready      (h2c_axis_ready )

   );


   // Increment ID
   logic [5:0] pcim_arid;
   logic       cfg_arid_inc_mode;

   always @(posedge clk_main_a0)
     if (!sde_rst_n)
       pcim_arid <= 2;
     else
       pcim_arid <= (sde_arvalid_q & sde_arready_q) ? pcim_arid + 1 :
                    pcim_arid;

   assign sde_arid_q = cfg_arid_inc_mode ? pcim_arid : pre_sde_arid_q;
   assign pre_sde_rid_q = cfg_arid_inc_mode ? pre_sde_arid_q : sde_rid_q;


// Stream BFM
   logic         bfm_h2c_axis_ready;

   logic         bfm_c2h_axis_valid;
   logic [511:0] bfm_c2h_axis_data;
   logic [63:0]  bfm_c2h_axis_keep;
   logic         bfm_c2h_axis_last;
   logic [63:0]  bfm_c2h_axis_user;

   logic         srm_h2c_axis_ready;

   logic         srm_c2h_axis_valid;
   logic [511:0] srm_c2h_axis_data;
   logic [63:0]  srm_c2h_axis_keep;
   logic         srm_c2h_axis_last;
   logic [63:0]  srm_c2h_axis_user;

   logic use_stream_bfm = 0;

//If simulation instantiate the Stream BFM
`ifdef SIMULATION
      stream_bfm STREAM_BFM
        (.clk         (clk_main_a0),
         .rst_n       (rst_main_n_sync),

         .ins_valid   (h2c_axis_valid),
         .ins_data    (h2c_axis_data),
         .ins_keep    (h2c_axis_keep),
         .ins_user    (h2c_axis_user),
         .ins_last    (h2c_axis_last),
         .ins_ready   (bfm_h2c_axis_ready),

         .ots_valid   (bfm_c2h_axis_valid),
         .ots_data    (bfm_c2h_axis_data),
         .ots_keep    (bfm_c2h_axis_keep),
         .ots_user    (bfm_c2h_axis_user),
         .ots_last    (bfm_c2h_axis_last),
         .ots_ready   (c2h_axis_ready)

         );
`else
   logic         bfm_h2c_axis_ready = 0;

   logic         bfm_c2h_axis_valid = 0;
   logic [511:0] bfm_c2h_axis_data = 0;
   logic [63:0]  bfm_c2h_axis_keep = 0;
   logic         bfm_c2h_axis_last = 0;
   logic [63:0]  bfm_c2h_axis_user = 0;
`endif

//Instantiate the RTL Stream block
cl_sde_srm CL_SDE_SRM (
   .clk         (clk_main_a0),
   .rst_n       (sde_rst_n), //(rst_main_n_sync_mid_slr),

   .cfg_srm_addr(cfg_srm_addr),
   .cfg_srm_wr(cfg_srm_wr),
   .cfg_srm_rd(cfg_srm_rd),
   .cfg_srm_wdata(cfg_srm_wdata),

   .srm_cfg_ack(srm_cfg_ack),
   .srm_cfg_rdata(srm_cfg_rdata),

   .ins_valid   (h2c_axis_valid),
   .ins_data    (h2c_axis_data),
   .ins_keep    (h2c_axis_keep),
   .ins_user    (h2c_axis_user),
   .ins_last    (h2c_axis_last),
   .ins_ready   (srm_h2c_axis_ready),

   .ots_valid   (srm_c2h_axis_valid),
   .ots_data    (srm_c2h_axis_data),
   .ots_keep    (srm_c2h_axis_keep),
   .ots_user    (srm_c2h_axis_user),
   .ots_last    (srm_c2h_axis_last),
   .ots_ready   (c2h_axis_ready)

   );

//Mux between RTL and BFM stream blocks
   assign h2c_axis_ready = cfg_sde_wire_loopback ? c2h_axis_ready : (use_stream_bfm)? bfm_h2c_axis_ready: srm_h2c_axis_ready;

assign c2h_axis_valid = cfg_sde_wire_loopback ? h2c_axis_valid : (use_stream_bfm)? bfm_c2h_axis_valid: srm_c2h_axis_valid;
assign c2h_axis_data =  cfg_sde_wire_loopback ? h2c_axis_data  : (use_stream_bfm)? bfm_c2h_axis_data: srm_c2h_axis_data;
assign c2h_axis_keep =  cfg_sde_wire_loopback ? h2c_axis_keep  : (use_stream_bfm)? bfm_c2h_axis_keep: srm_c2h_axis_keep;
assign c2h_axis_user =  cfg_sde_wire_loopback ? h2c_axis_user  : (use_stream_bfm)? bfm_c2h_axis_user: srm_c2h_axis_user;
assign c2h_axis_last =  cfg_sde_wire_loopback ? h2c_axis_last  : (use_stream_bfm)? bfm_c2h_axis_last: srm_c2h_axis_last;


//-------------------------------------
// OCL AXI-L Handling (CSRs)
//-------------------------------------
//--------------------------------------------------------------
// PCIe OCL AXI-L Slave Accesses (accesses from PCIe AppPF BAR0)
//--------------------------------------------------------------
// Only supports single-beat accesses.

   // Address Range
   // 0x0000 - 0x0ffc : CL_SDE_SRM
   // 0x2000 - General Purpose Config Reg  0
   //          Bit 0 - Reset SDE
   //
   // 0x2004 - General Purpose Config Reg  1
   // 0x2008 - General Purpose Config Reg  2
   // 0x200c - General Purpose Config Reg  3

   // Reset Unused

   logic        awvalid;
   logic [31:0] awaddr;
   logic        wvalid;
   logic [31:0] wdata;
   logic [3:0]  wstrb;
   logic        bready;
   logic        arvalid;
   logic [31:0] araddr;
   logic        rready;

   logic        awready;
   logic        wready;
   logic        bvalid;
   logic [1:0]  bresp;
   logic        arready;
   logic        rvalid;
   logic [31:0] rdata;
   logic [1:0]  rresp;

   // Inputs
   assign awvalid         = sh_ocl_awvalid_q2;
   assign awaddr[31:0]    = sh_ocl_awaddr_q2;
   assign wvalid          = sh_ocl_wvalid_q2;
   assign wdata[31:0]     = sh_ocl_wdata_q2;
   assign wstrb[3:0]      = sh_ocl_wstrb_q2;
   assign bready          = sh_ocl_bready_q2;
   assign arvalid         = sh_ocl_arvalid_q2;
   assign araddr[31:0]    = sh_ocl_araddr_q2;
   assign rready          = sh_ocl_rready_q2;

   // Outputs
   assign ocl_sh_awready_q2 = awready;
   assign ocl_sh_wready_q2  = wready;
   assign ocl_sh_bvalid_q2  = bvalid;
   assign ocl_sh_bresp_q2   = bresp[1:0];
   assign ocl_sh_arready_q2 = arready;
   assign ocl_sh_rvalid_q2  = rvalid;
   assign ocl_sh_rdata_q2   = rdata;
   assign ocl_sh_rresp_q2   = rresp[1:0];

// Write Request
logic        wr_active;
logic [31:0] wr_addr;
logic wr_req;              //Note these are pulses
logic rd_req;              //Note these are pulses
logic[31:0] wdata_q;

logic wr_req_lvl;          //Level versions of the requests
logic rd_req_lvl;

logic        arvalid_q;
logic [31:0] araddr_q;


logic wr_done;
logic rd_done;


logic cfg_srm_dec;

   logic cfg_chk_dec;
   logic [7:0]  cfg_chk_addr;
   logic         cfg_chk_wr;
   logic         cfg_chk_rd;
   logic [31:0]  cfg_chk_wdata;
   logic         chk_cfg_ack;
   logic [31:0]  chk_cfg_rdata;

   logic cfg_tst_dec;
   logic [7:0]  cfg_tst_addr;
   logic         cfg_tst_wr;
   logic         cfg_tst_rd;
   logic [31:0]  cfg_tst_wdata;
   logic         tst_cfg_ack;
   logic [31:0]  tst_cfg_rdata;


logic[31:0] cfg_ctl_reg[3:0] = '{default:'0};

always @(posedge clk_main_a0)
  if (!rst_main_n_sync_mid_slr) begin
     wr_active <= 0;
     wr_addr   <= 0;
     wr_req <= 0;
     wdata_q <= 0;
     wr_req_lvl <= 0;
  end
  else begin
     wr_active <=  wr_active && bvalid  && bready ? 1'b0     :
                  ~wr_active && awvalid           ? 1'b1     :
                                                    wr_active;
     wr_addr <= awvalid && ~wr_active ? awaddr : wr_addr     ;

     //Request is a pulse
     wr_req <= (wr_active && wvalid && wready);

     wdata_q <= (wvalid && wready)? wdata: wdata_q;

      wr_req_lvl <= (wr_active && wvalid && wready) || (wr_req_lvl && !wr_done);


  end

assign awready = ~wr_active;
assign wready  =  wr_active && wvalid;

// Write Response
always @(posedge clk_main_a0)
  if (!rst_main_n_sync_mid_slr)
    bvalid <= 0;
  else
    bvalid <=  bvalid &&  bready            ? 1'b0  :
                         ~bvalid && wr_done ? 1'b1  :
                                             bvalid;
assign bresp = 0;

assign cfg_srm_dec = (rd_req_lvl  && (araddr_q[15:0] >= 0) && (araddr_q[15:0]<='hffc)) ||
                        (wr_req_lvl && (wr_addr[15:0] >= 0) && (wr_addr[15:0]<='hffc));

assign cfg_chk_dec = (rd_req_lvl  && (araddr_q[15:0] >= 16'h1000) && (araddr_q[15:0] <='h10fc)) ||
                     (wr_req_lvl  && (wr_addr[15:0]  >= 16'h1000) && (wr_addr[15:0]  <='h10fc));

assign cfg_tst_dec = (rd_req_lvl  && (araddr_q[15:0] >= 16'h1100) && (araddr_q[15:0] <='h11fc)) ||
                     (wr_req_lvl  && (wr_addr[15:0]  >= 16'h1100) && (wr_addr[15:0]  <='h11fc));


// Read Request
always @(posedge clk_main_a0)
   if (!rst_main_n_sync_mid_slr) begin
      arvalid_q <= 0;
      araddr_q  <= 0;
      rd_req <= 0;
      rd_req_lvl <= 0;
   end
   else begin
      arvalid_q <= arvalid;
      araddr_q  <= arvalid ? araddr : araddr_q;
      rd_req <= (arvalid && arready);
      rd_req_lvl <= (arvalid && arready) || (rd_req_lvl && !rd_done);
   end

assign arready = !arvalid_q && !rvalid;
// Read Response
always @(posedge clk_main_a0)
   if (!rst_main_n_sync_mid_slr)
   begin
      rvalid <= 0;
      rdata  <= 0;
      rresp  <= 0;
   end
   else if (rvalid && rready)
   begin
      rvalid <= 0;
      rdata  <= 0;
      rresp  <= 0;
   end
   else if (rd_done)
   begin
      rvalid <= 1;
      rdata  <= (cfg_srm_dec)?   srm_cfg_rdata:
                cfg_chk_dec ? chk_cfg_rdata :
                cfg_tst_dec ? tst_cfg_rdata :
                cfg_ctl_reg[araddr_q[3:2]];
   end

// assign rd_done = (rd_req && !cfg_srm_dec) || (rd_req_lvl && srm_cfg_ack);
// assign wr_done = (wr_req && !cfg_srm_dec) || (wr_req_lvl && srm_cfg_ack);

   assign rd_done = cfg_srm_dec ? (rd_req_lvl && srm_cfg_ack) :
                    cfg_chk_dec ? (rd_req_lvl && chk_cfg_ack) :
                    cfg_tst_dec ? (rd_req_lvl && tst_cfg_ack) :
                    rd_req;
   assign wr_done = cfg_srm_dec ? (wr_req_lvl && srm_cfg_ack) :
                    cfg_chk_dec ? (wr_req_lvl && chk_cfg_ack) :
                    cfg_tst_dec ? (wr_req_lvl && tst_cfg_ack) :
                    wr_req;

assign cfg_srm_addr = (wr_active)? wr_addr: araddr_q;
assign cfg_srm_wr = wr_req && cfg_srm_dec;
assign cfg_srm_rd = rd_req && cfg_srm_dec;
assign cfg_srm_wdata = wdata_q;

assign cfg_chk_addr = (wr_active)? wr_addr: araddr_q;
assign cfg_chk_wr = wr_req && cfg_chk_dec;
assign cfg_chk_rd = rd_req && cfg_chk_dec;
assign cfg_chk_wdata = wdata_q;

assign cfg_tst_addr = (wr_active)? wr_addr: araddr_q;
assign cfg_tst_wr = wr_req && cfg_tst_dec;
assign cfg_tst_rd = rd_req && cfg_tst_dec;
assign cfg_tst_wdata = wdata_q;

//4 general purpose control registers
always @(posedge clk_main_a0)
   if (wr_req && (wr_addr[15:0] >= 16'h2000) && (wr_addr[15:0]<=16'h2ffc))
      cfg_ctl_reg[wr_addr[3:2]] <= wdata_q;

   logic cfg_atg_en;

   assign cfg_sde_rst = cfg_ctl_reg[0][0];
   assign cfg_sde_wire_loopback = cfg_ctl_reg[0][1];
   assign cfg_arid_inc_mode = cfg_ctl_reg[0][2];
   assign cfg_atg_en = cfg_ctl_reg[0][3];

`ifdef CL_SDE_AXI_PROT_CHK

   axi_prot_chk AXI_PROT_CHK
     (.clk                (clk_main_a0),
      .rst_n              (sde_rst_n  ),

      .cfg_chk_addr  (cfg_chk_addr  ),
      .cfg_chk_wr    (cfg_chk_wr    ),
      .cfg_chk_rd    (cfg_chk_rd    ),
      .cfg_chk_wdata (cfg_chk_wdata ),
      .chk_cfg_ack   (chk_cfg_ack   ),
      .chk_cfg_rdata (chk_cfg_rdata ),

      .wr_last_error (pcim_wr_last_error),

      .awvalid        (cl_sh_pcim_awvalid_q ),
      .awid           (cl_sh_pcim_awid_q    ),
      .awaddr         (cl_sh_pcim_awaddr_q  ),
      .awlen          (cl_sh_pcim_awlen_q   ),
      .awsize         (cl_sh_pcim_awsize_q  ),
      .awready        (sh_cl_pcim_awready_q ),
      .wvalid         (cl_sh_pcim_wvalid_q  ),
      .wdata          (cl_sh_pcim_wdata_q   ),
      .wstrb          (cl_sh_pcim_wstrb_q   ),
      .wlast          (cl_sh_pcim_wlast_q   ),
      .wready         (sh_cl_pcim_wready_q  ),
      .bvalid         (sh_cl_pcim_bvalid_q  ),
      .bid            (sh_cl_pcim_bid_q     ),
      .bresp          (sh_cl_pcim_bresp_q   ),
      .bready         (cl_sh_pcim_bready_q  ),
      .arvalid        (cl_sh_pcim_arvalid_q ),
      .arid           (cl_sh_pcim_arid_q    ),
      .araddr         (cl_sh_pcim_araddr_q  ),
      .arlen          (cl_sh_pcim_arlen_q   ),
      .arsize         (cl_sh_pcim_arsize_q  ),
      .arready        (sh_cl_pcim_arready_q ),
      .rvalid         (sh_cl_pcim_rvalid_q  ),
      .rid            (sh_cl_pcim_rid_q     ),
      .rdata          (sh_cl_pcim_rdata_q   ),
      .rresp          (sh_cl_pcim_rresp_q   ),
      .rlast          (sh_cl_pcim_rlast_q   ),
      .rready         (cl_sh_pcim_rready_q  )

      );
`else
   assign chk_cfg_ack = 1;
   assign chk_cfg_rdata = 0;
`endif // !`ifdef CL_SDE_AXI_PROT_CHK

`define CL_SDE_PCIM_ATG

`ifdef CL_SDE_PCIM_ATG

   logic         atg_awvalid_q ;
   logic [8:0]   atg_awid_q    ;
   logic [63:0]  atg_awaddr_q  ;
   logic [7:0]   atg_awlen_q   ;
   logic [2:0]   atg_awsize_q  ;
   logic         atg_awready_q ;
   logic         atg_wvalid_q  ;
   logic [511:0] atg_wdata_q   ;
   logic [63:0]  atg_wstrb_q   ;
   logic         atg_wlast_q   ;
   logic         atg_wready_q  ;
   logic         atg_bvalid_q  ;
   logic [8:0]   atg_bid_q     ;
   logic [1:0]   atg_bresp_q   ;
   logic         atg_bready_q  ;
   logic         atg_arvalid_q ;
   logic [8:0]   atg_arid_q    ;
   logic [63:0]  atg_araddr_q  ;
   logic [7:0]   atg_arlen_q   ;
   logic [2:0]   atg_arsize_q  ;
   logic         atg_arready_q ;
   logic         atg_rvalid_q  ;
   logic [8:0]   atg_rid_q     ;
   logic [511:0] atg_rdata_q   ;
   logic [1:0]   atg_rresp_q   ;
   logic         atg_rlast_q   ;
   logic         atg_rready_q  ;

   cl_tst #(.DATA_WIDTH(512))
   CL_TST_PCIM

     (.clk          (clk_main_a0),
      .rst_n        (sde_rst_n  ),

      .cfg_addr     (cfg_tst_addr[7:0]  ),
      .cfg_wdata    (cfg_tst_wdata ),
      .cfg_wr       (cfg_tst_wr    ),
      .cfg_rd       (cfg_tst_rd    ),
      .tst_cfg_ack  (tst_cfg_ack   ),
      .tst_cfg_rdata(tst_cfg_rdata ),

      .awid    (atg_awid_q    ),
      .awaddr  (atg_awaddr_q  ),
      .awlen   (atg_awlen_q   ),
      .awvalid (atg_awvalid_q ),
      .awuser  (            ),
      .awready (atg_awready_q ),

      .wdata   (atg_wdata_q   ),
      .wstrb   (atg_wstrb_q   ),
      .wlast   (atg_wlast_q   ),
      .wvalid  (atg_wvalid_q  ),
      .wready  (atg_wready_q  ),

      .bid     (atg_bid_q     ),
      .bresp   (atg_bresp_q   ),
      .bvalid  (atg_bvalid_q  ),
      .buser   (18'h0       ),
      .bready  (atg_bready_q  ),

      .arid    (atg_arid_q    ),
      .araddr  (atg_araddr_q  ),
      .arlen   (atg_arlen_q   ),
      .arvalid (atg_arvalid_q ),
      .arready (atg_arready_q ),

      .rid     (atg_rid_q     ),
      .rdata   (atg_rdata_q   ),
      .rresp   (atg_rresp_q   ),
      .rlast   (atg_rlast_q   ),
      .ruser   (18'h0       ),
      .rvalid  (atg_rvalid_q  ),
      .rready  (atg_rready_q  )
      );

   assign atg_arsize_q = 6;
   assign atg_awsize_q = 6;

   // Mux
   assign cl_sh_pcim_awvalid_q = cfg_atg_en ? atg_awvalid_q : sde_awvalid_q ;
   assign cl_sh_pcim_awid_q    = cfg_atg_en ? atg_awid_q    : sde_awid_q    ;
   assign cl_sh_pcim_awaddr_q  = cfg_atg_en ? atg_awaddr_q  : sde_awaddr_q  ;
   assign cl_sh_pcim_awlen_q   = cfg_atg_en ? atg_awlen_q   : sde_awlen_q   ;
   assign cl_sh_pcim_awsize_q  = cfg_atg_en ? atg_awsize_q  : sde_awsize_q  ;
   assign atg_awready_q =  cfg_atg_en & sh_cl_pcim_awready_q;
   assign sde_awready_q = ~cfg_atg_en & sh_cl_pcim_awready_q;

   assign cl_sh_pcim_wvalid_q  = cfg_atg_en ? atg_wvalid_q : sde_wvalid_q;
   assign cl_sh_pcim_wdata_q   = cfg_atg_en ? atg_wdata_q  : sde_wdata_q ;
   assign cl_sh_pcim_wstrb_q   = cfg_atg_en ? atg_wstrb_q  : sde_wstrb_q ;
   assign cl_sh_pcim_wlast_q   = cfg_atg_en ? atg_wlast_q  : sde_wlast_q ;
   assign atg_wready_q  = cfg_atg_en  & sh_cl_pcim_wready_q;
   assign sde_wready_q  = ~cfg_atg_en & sh_cl_pcim_wready_q;

   assign atg_bvalid_q  = cfg_atg_en  & sh_cl_pcim_bvalid_q;
   assign atg_bid_q     = sh_cl_pcim_bid_q;
   assign atg_bresp_q   = sh_cl_pcim_bresp_q;
   assign sde_bvalid_q  = ~cfg_atg_en & sh_cl_pcim_bvalid_q;
   assign sde_bid_q     = sh_cl_pcim_bid_q;
   assign sde_bresp_q   = sh_cl_pcim_bresp_q;
   assign cl_sh_pcim_bready_q  = cfg_atg_en ? atg_bready_q : sde_bready_q;

   assign cl_sh_pcim_arvalid_q = cfg_atg_en ? atg_arvalid_q : sde_arvalid_q ;
   assign cl_sh_pcim_arid_q    = cfg_atg_en ? atg_arid_q    : sde_arid_q    ;
   assign cl_sh_pcim_araddr_q  = cfg_atg_en ? atg_araddr_q  : sde_araddr_q  ;
   assign cl_sh_pcim_arlen_q   = cfg_atg_en ? atg_arlen_q   : sde_arlen_q   ;
   assign cl_sh_pcim_arsize_q  = cfg_atg_en ? atg_arsize_q  : sde_arsize_q  ;
   assign atg_arready_q =  cfg_atg_en & sh_cl_pcim_arready_q;
   assign sde_arready_q = ~cfg_atg_en & sh_cl_pcim_arready_q;

   assign atg_rvalid_q  = cfg_atg_en  & sh_cl_pcim_rvalid_q;
   assign atg_rid_q     = sh_cl_pcim_rid_q;
   assign atg_rdata_q   = sh_cl_pcim_rdata_q;
   assign atg_rlast_q   = sh_cl_pcim_rlast_q;
   assign atg_rresp_q   = sh_cl_pcim_rresp_q;
   assign sde_rvalid_q  = ~cfg_atg_en & sh_cl_pcim_rvalid_q;
   assign sde_rid_q     = sh_cl_pcim_rid_q;
   assign sde_rdata_q   = sh_cl_pcim_rdata_q;
   assign sde_rlast_q   = sh_cl_pcim_rlast_q;
   assign sde_rresp_q   = sh_cl_pcim_rresp_q;
   assign cl_sh_pcim_rready_q  = cfg_atg_en ? atg_rready_q : sde_rready_q;

`else // !`ifdef CL_SDE_PCIM_ATG

   assign tst_cfg_ack = 1;
   assign tst_cfg_rdata = 0;

   assign cl_sh_pcim_awvalid_q = sde_awvalid_q ;
   assign cl_sh_pcim_awid_q    = sde_awid_q    ;
   assign cl_sh_pcim_awaddr_q  = sde_awaddr_q  ;
   assign cl_sh_pcim_awlen_q   = sde_awlen_q   ;
   assign cl_sh_pcim_awsize_q  = sde_awsize_q  ;
   assign sde_awready_q = sh_cl_pcim_awready_q;

   assign cl_sh_pcim_wvalid_q  = sde_wvalid_q;
   assign cl_sh_pcim_wdata_q   = sde_wdata_q ;
   assign cl_sh_pcim_wstrb_q   = sde_wstrb_q ;
   assign cl_sh_pcim_wlast_q   = sde_wlast_q ;
   assign sde_wready_q  = sh_cl_pcim_wready_q;

   assign sde_bvalid_q  = sh_cl_pcim_bvalid_q;
   assign sde_bid_q     = sh_cl_pcim_bid_q;
   assign sde_bresp_q   = sh_cl_pcim_bresp_q;
   assign cl_sh_pcim_bready_q  = sde_bready_q;

   assign cl_sh_pcim_arvalid_q = sde_arvalid_q ;
   assign cl_sh_pcim_arid_q    = sde_arid_q    ;
   assign cl_sh_pcim_araddr_q  = sde_araddr_q  ;
   assign cl_sh_pcim_arlen_q   = sde_arlen_q   ;
   assign cl_sh_pcim_arsize_q  = sde_arsize_q  ;
   assign sde_arready_q = sh_cl_pcim_arready_q;

   assign sde_rvalid_q  = sh_cl_pcim_rvalid_q;
   assign sde_rid_q     = sh_cl_pcim_rid_q;
   assign sde_rdata_q   = sh_cl_pcim_rdata_q;
   assign sde_rlast_q   = sh_cl_pcim_rlast_q;
   assign sde_rresp_q   = sh_cl_pcim_rresp_q;
   assign cl_sh_pcim_rready_q  = sde_rready_q;

`endif // !`ifdef CL_SDE_PCIM_ATG



// Debug Bridge
 cl_debug_bridge CL_DEBUG_BRIDGE (
      .clk(clk_main_a0),
      .S_BSCAN_drck(drck),
      .S_BSCAN_shift(shift),
      .S_BSCAN_tdi(tdi),
      .S_BSCAN_update(update),
      .S_BSCAN_sel(sel),
      .S_BSCAN_tdo(tdo),
      .S_BSCAN_tms(tms),
      .S_BSCAN_tck(tck),
      .S_BSCAN_runtest(runtest),
      .S_BSCAN_reset(reset),
      .S_BSCAN_capture(capture),
      .S_BSCAN_bscanid_en(bscanid_en)
   );


`ifndef NO_SDE_DEBUG_ILA

   ila_axi4_wrapper #(.AXI_DATA_WIDTH(32)) PCIS_AXI4_SH_CL_BOUNDARY_ILA
     (.aclk         (clk),
      .trig_disable (1'b0),
     .ila_awid     (sh_cl_dma_pcis_awid    ),
     .ila_awaddr   (sh_cl_dma_pcis_awaddr  ),
     .ila_awlen    (sh_cl_dma_pcis_awlen   ),
     .ila_awsize   (sh_cl_dma_pcis_awsize  ),
     .ila_awvalid  (sh_cl_dma_pcis_awvalid ),
     .ila_awready  (cl_sh_dma_pcis_awready ),
     .ila_wdata    (sh_cl_dma_pcis_wdata   ),
     .ila_wstrb    (sh_cl_dma_pcis_wstrb   ),
     .ila_wlast    (sh_cl_dma_pcis_wlast   ),
     .ila_wvalid   (sh_cl_dma_pcis_wvalid  ),
     .ila_wready   (cl_sh_dma_pcis_wready  ),
     .ila_bid      (cl_sh_dma_pcis_bid     ),
     .ila_bresp    (cl_sh_dma_pcis_bresp   ),
     .ila_bvalid   (cl_sh_dma_pcis_bvalid  ),
     .ila_bready   (sh_cl_dma_pcis_bready  ),
     .ila_arid     (sh_cl_dma_pcis_arid    ),
     .ila_araddr   (sh_cl_dma_pcis_araddr  ),
     .ila_arlen    (sh_cl_dma_pcis_arlen   ),
     .ila_arsize   (sh_cl_dma_pcis_arsize  ),
     .ila_arvalid  (sh_cl_dma_pcis_arvalid ),
     .ila_arready  (cl_sh_dma_pcis_arready ),
     .ila_rid      (cl_sh_dma_pcis_rid     ),
     .ila_rdata    (cl_sh_dma_pcis_rdata   ),
     .ila_rresp    (cl_sh_dma_pcis_rresp   ),
     .ila_rlast    (cl_sh_dma_pcis_rlast   ),
     .ila_rvalid   (cl_sh_dma_pcis_rvalid  ),
     .ila_rready   (sh_cl_dma_pcis_rready  )
      );

   ila_axi4_wrapper #(.AXI_DATA_WIDTH(32)) PCIM_AXI4_SH_CL_BOUNDARY_ILA
     (.aclk         (clk),
      .trig_disable (1'b0),
     .ila_awid     (cl_sh_pcim_awid    ),
     .ila_awaddr   (cl_sh_pcim_awaddr  ),
     .ila_awlen    (cl_sh_pcim_awlen   ),
     .ila_awsize   (cl_sh_pcim_awsize  ),
     .ila_awvalid  (cl_sh_pcim_awvalid ),
     .ila_awready  (sh_cl_pcim_awready ),
     .ila_wdata    (cl_sh_pcim_wdata   ),
     .ila_wstrb    (cl_sh_pcim_wstrb   ),
     .ila_wlast    (cl_sh_pcim_wlast   ),
     .ila_wvalid   (cl_sh_pcim_wvalid  ),
     .ila_wready   (sh_cl_pcim_wready  ),
     .ila_bid      (sh_cl_pcim_bid     ),
     .ila_bresp    (sh_cl_pcim_bresp   ),
     .ila_bvalid   (sh_cl_pcim_bvalid  ),
     .ila_bready   (cl_sh_pcim_bready  ),
     .ila_arid     (cl_sh_pcim_arid    ),
     .ila_araddr   (cl_sh_pcim_araddr  ),
     .ila_arlen    (cl_sh_pcim_arlen   ),
     .ila_arsize   (cl_sh_pcim_arsize  ),
     .ila_arvalid  (cl_sh_pcim_arvalid ),
     .ila_arready  (sh_cl_pcim_arready ),
     .ila_rid      (sh_cl_pcim_rid     ),
     .ila_rdata    (sh_cl_pcim_rdata   ),
     .ila_rresp    (sh_cl_pcim_rresp   ),
     .ila_rlast    (sh_cl_pcim_rlast   ),
     .ila_rvalid   (sh_cl_pcim_rvalid  ),
     .ila_rready   (cl_sh_pcim_rready  )
     );

`endif //  `ifndef NO_SDE_DEBUG_ILA



//Needed for board_tb simulation
logic[3:0] all_ddr_is_ready;

endmodule // cl_sde
