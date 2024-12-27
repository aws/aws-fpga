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


module cl_dma_pcis_slv
#(
  parameter           SCRB_MAX_ADDR         = 64'h3FFFFFFFF,
  parameter           SCRB_BURST_LEN_MINUS1 = 15,
  parameter           NO_SCRB_INST          = 1
)
(
  input logic         aclk,
  input logic         aresetn,

  cfg_bus_t.slave     ddra_tst_cfg_bus,
  cfg_bus_t.slave     ddrb_tst_cfg_bus,

  scrb_bus_t.master   ddra_scrb_bus,
  scrb_bus_t.master   ddrb_scrb_bus,

  axi_bus_t.master    sh_cl_dma_pcis_bus,
  axi_bus_t.master    cl_axi_mstr_bus,

  axi_bus_t.slave     scrb_axi_ddra,
  axi_bus_t.slave     scrb_axi_ddrb,

  axi_bus_t           sh_cl_dma_pcis_q
);

  //----------------------------
  // Internal signals
  //----------------------------
  axi_bus_t   sh_cl_dma_pcis_q2();

  axi_bus_t   xbar_axi_ddra();
  axi_bus_t   xbar_axi_ddra_q();
  axi_bus_t   xbar_axi_ddra_q2();

  axi_bus_t   xbar_axi_ddrb();
  axi_bus_t   xbar_axi_ddrb_q();
  axi_bus_t   xbar_axi_ddrb_q2();

  cfg_bus_t   ddra_tst_cfg_bus_q();
  cfg_bus_t   ddrb_tst_cfg_bus_q();

  scrb_bus_t  ddra_scrb_bus_q();
  scrb_bus_t  ddrb_scrb_bus_q();

  logic   slr0_rst_n_sync;
  logic   slr1_rst_n_sync;
  logic   slr2_rst_n_sync;

  logic   slr0_sync_aresetn;
  logic   slr1_sync_aresetn;
  logic   slr2_sync_aresetn;
  //----------------------------
  // End Internal signals
  //----------------------------

  xpm_cdc_async_rst CDC_ASYNC_RST_N_SLR0 (.src_arst(aresetn), .dest_clk(aclk), .dest_arst(slr0_rst_n_sync));
  xpm_cdc_async_rst CDC_ASYNC_RST_N_SLR1 (.src_arst(aresetn), .dest_clk(aclk), .dest_arst(slr1_rst_n_sync));
  xpm_cdc_async_rst CDC_ASYNC_RST_N_SLR2 (.src_arst(aresetn), .dest_clk(aclk), .dest_arst(slr2_rst_n_sync));

  lib_pipe #(.WIDTH(1), .STAGES(4)) SLR0_PIPE_RST_N (.clk(aclk), .rst_n(1'b1), .in_bus(slr0_rst_n_sync), .out_bus(slr0_sync_aresetn));
  lib_pipe #(.WIDTH(1), .STAGES(4)) SLR1_PIPE_RST_N (.clk(aclk), .rst_n(1'b1), .in_bus(slr1_rst_n_sync), .out_bus(slr1_sync_aresetn));
  lib_pipe #(.WIDTH(1), .STAGES(4)) SLR2_PIPE_RST_N (.clk(aclk), .rst_n(1'b1), .in_bus(slr2_rst_n_sync), .out_bus(slr2_sync_aresetn));

  axi_register_slice AXI4_REG_SLC_PCIS_SLR2
  (
    .aclk                   (aclk                      ),
    .aresetn                (slr2_sync_aresetn         ),
    .s_axi_awid             (sh_cl_dma_pcis_bus.awid   ),
    .s_axi_awaddr           (sh_cl_dma_pcis_bus.awaddr ),
    .s_axi_awlen            (sh_cl_dma_pcis_bus.awlen  ),
    .s_axi_awsize           (sh_cl_dma_pcis_bus.awsize ),
    .s_axi_awburst          (`DEF_AXBURST              ),
    .s_axi_awlock           (`DEF_AXLOCK               ),
    .s_axi_awcache          (`DEF_AXCACHE              ),
    .s_axi_awprot           (`DEF_AXPROT               ),
    .s_axi_awregion         (`DEF_AXREGION             ),
    .s_axi_awqos            (`DEF_AXQOS                ),
    .s_axi_awvalid          (sh_cl_dma_pcis_bus.awvalid),
    .s_axi_awready          (sh_cl_dma_pcis_bus.awready),
    .s_axi_wdata            (sh_cl_dma_pcis_bus.wdata  ),
    .s_axi_wstrb            (sh_cl_dma_pcis_bus.wstrb  ),
    .s_axi_wlast            (sh_cl_dma_pcis_bus.wlast  ),
    .s_axi_wvalid           (sh_cl_dma_pcis_bus.wvalid ),
    .s_axi_wready           (sh_cl_dma_pcis_bus.wready ),
    .s_axi_bid              (sh_cl_dma_pcis_bus.bid    ),
    .s_axi_bresp            (sh_cl_dma_pcis_bus.bresp  ),
    .s_axi_bvalid           (sh_cl_dma_pcis_bus.bvalid ),
    .s_axi_bready           (sh_cl_dma_pcis_bus.bready ),
    .s_axi_arid             (sh_cl_dma_pcis_bus.arid   ),
    .s_axi_araddr           (sh_cl_dma_pcis_bus.araddr ),
    .s_axi_arlen            (sh_cl_dma_pcis_bus.arlen  ),
    .s_axi_arsize           (sh_cl_dma_pcis_bus.arsize ),
    .s_axi_arburst          (`DEF_AXBURST              ),
    .s_axi_arlock           (`DEF_AXLOCK               ),
    .s_axi_arcache          (`DEF_AXCACHE              ),
    .s_axi_arprot           (`DEF_AXPROT               ),
    .s_axi_arregion         (`DEF_AXREGION             ),
    .s_axi_arqos            (`DEF_AXQOS                ),
    .s_axi_arvalid          (sh_cl_dma_pcis_bus.arvalid),
    .s_axi_arready          (sh_cl_dma_pcis_bus.arready),
    .s_axi_rid              (sh_cl_dma_pcis_bus.rid    ),
    .s_axi_rdata            (sh_cl_dma_pcis_bus.rdata  ),
    .s_axi_rresp            (sh_cl_dma_pcis_bus.rresp  ),
    .s_axi_rlast            (sh_cl_dma_pcis_bus.rlast  ),
    .s_axi_rvalid           (sh_cl_dma_pcis_bus.rvalid ),
    .s_axi_rready           (sh_cl_dma_pcis_bus.rready ),

    .m_axi_awid             (sh_cl_dma_pcis_q.awid     ),
    .m_axi_awaddr           (sh_cl_dma_pcis_q.awaddr   ),
    .m_axi_awlen            (sh_cl_dma_pcis_q.awlen    ),
    .m_axi_awsize           (sh_cl_dma_pcis_q.awsize   ),
    .m_axi_awburst          (sh_cl_dma_pcis_q.awburst  ),
    .m_axi_awlock           (                          ),
    .m_axi_awcache          (                          ),
    .m_axi_awprot           (                          ),
    .m_axi_awregion         (                          ),
    .m_axi_awqos            (                          ),
    .m_axi_awvalid          (sh_cl_dma_pcis_q.awvalid  ),
    .m_axi_awready          (sh_cl_dma_pcis_q.awready  ),
    .m_axi_wdata            (sh_cl_dma_pcis_q.wdata    ),
    .m_axi_wstrb            (sh_cl_dma_pcis_q.wstrb    ),
    .m_axi_wvalid           (sh_cl_dma_pcis_q.wvalid   ),
    .m_axi_wlast            (sh_cl_dma_pcis_q.wlast    ),
    .m_axi_wready           (sh_cl_dma_pcis_q.wready   ),
    .m_axi_bresp            (sh_cl_dma_pcis_q.bresp    ),
    .m_axi_bvalid           (sh_cl_dma_pcis_q.bvalid   ),
    .m_axi_bid              (sh_cl_dma_pcis_q.bid      ),
    .m_axi_bready           (sh_cl_dma_pcis_q.bready   ),
    .m_axi_arid             (sh_cl_dma_pcis_q.arid     ),
    .m_axi_araddr           (sh_cl_dma_pcis_q.araddr   ),
    .m_axi_arlen            (sh_cl_dma_pcis_q.arlen    ),
    .m_axi_arsize           (sh_cl_dma_pcis_q.arsize   ),
    .m_axi_arburst          (sh_cl_dma_pcis_q.arburst  ),
    .m_axi_arlock           (                          ),
    .m_axi_arcache          (                          ),
    .m_axi_arprot           (                          ),
    .m_axi_arregion         (                          ),
    .m_axi_arqos            (                          ),
    .m_axi_arvalid          (sh_cl_dma_pcis_q.arvalid  ),
    .m_axi_arready          (sh_cl_dma_pcis_q.arready  ),
    .m_axi_rid              (sh_cl_dma_pcis_q.rid      ),
    .m_axi_rdata            (sh_cl_dma_pcis_q.rdata    ),
    .m_axi_rresp            (sh_cl_dma_pcis_q.rresp    ),
    .m_axi_rlast            (sh_cl_dma_pcis_q.rlast    ),
    .m_axi_rvalid           (sh_cl_dma_pcis_q.rvalid   ),
    .m_axi_rready           (sh_cl_dma_pcis_q.rready   )
  );

  axi_register_slice AXI4_REG_SLC_PCIS_SLR1
  (
    .aclk                   (aclk                      ),
    .aresetn                (slr1_sync_aresetn         ),

    .s_axi_awid             (sh_cl_dma_pcis_q.awid     ),
    .s_axi_awaddr           (sh_cl_dma_pcis_q.awaddr   ),
    .s_axi_awlen            (sh_cl_dma_pcis_q.awlen    ),
    .s_axi_awsize           (sh_cl_dma_pcis_q.awsize   ),
    .s_axi_awburst          (sh_cl_dma_pcis_q.awburst  ),
    .s_axi_awlock           (`DEF_AXLOCK               ),
    .s_axi_awcache          (`DEF_AXCACHE              ),
    .s_axi_awprot           (`DEF_AXPROT               ),
    .s_axi_awregion         (`DEF_AXREGION             ),
    .s_axi_awqos            (`DEF_AXQOS                ),
    .s_axi_awvalid          (sh_cl_dma_pcis_q.awvalid  ),
    .s_axi_awready          (sh_cl_dma_pcis_q.awready  ),
    .s_axi_wdata            (sh_cl_dma_pcis_q.wdata    ),
    .s_axi_wstrb            (sh_cl_dma_pcis_q.wstrb    ),
    .s_axi_wlast            (sh_cl_dma_pcis_q.wlast    ),
    .s_axi_wvalid           (sh_cl_dma_pcis_q.wvalid   ),
    .s_axi_wready           (sh_cl_dma_pcis_q.wready   ),
    .s_axi_bid              (sh_cl_dma_pcis_q.bid      ),
    .s_axi_bresp            (sh_cl_dma_pcis_q.bresp    ),
    .s_axi_bvalid           (sh_cl_dma_pcis_q.bvalid   ),
    .s_axi_bready           (sh_cl_dma_pcis_q.bready   ),
    .s_axi_arid             (sh_cl_dma_pcis_q.arid     ),
    .s_axi_araddr           (sh_cl_dma_pcis_q.araddr   ),
    .s_axi_arlen            (sh_cl_dma_pcis_q.arlen    ),
    .s_axi_arsize           (sh_cl_dma_pcis_q.arsize   ),
    .s_axi_arburst          (sh_cl_dma_pcis_q.arburst  ),
    .s_axi_arlock           (`DEF_AXLOCK               ),
    .s_axi_arcache          (`DEF_AXCACHE              ),
    .s_axi_arprot           (`DEF_AXPROT               ),
    .s_axi_arregion         (`DEF_AXREGION             ),
    .s_axi_arqos            (`DEF_AXQOS                ),
    .s_axi_arvalid          (sh_cl_dma_pcis_q.arvalid  ),
    .s_axi_arready          (sh_cl_dma_pcis_q.arready  ),
    .s_axi_rid              (sh_cl_dma_pcis_q.rid      ),
    .s_axi_rdata            (sh_cl_dma_pcis_q.rdata    ),
    .s_axi_rresp            (sh_cl_dma_pcis_q.rresp    ),
    .s_axi_rlast            (sh_cl_dma_pcis_q.rlast    ),
    .s_axi_rvalid           (sh_cl_dma_pcis_q.rvalid   ),
    .s_axi_rready           (sh_cl_dma_pcis_q.rready   ),

    .m_axi_awid             (sh_cl_dma_pcis_q2.awid    ),
    .m_axi_awaddr           (sh_cl_dma_pcis_q2.awaddr  ),
    .m_axi_awlen            (sh_cl_dma_pcis_q2.awlen   ),
    .m_axi_awsize           (sh_cl_dma_pcis_q2.awsize  ),
    .m_axi_awburst          (sh_cl_dma_pcis_q2.awburst ),
    .m_axi_awlock           (                          ),
    .m_axi_awcache          (                          ),
    .m_axi_awprot           (                          ),
    .m_axi_awregion         (                          ),
    .m_axi_awqos            (                          ),
    .m_axi_awvalid          (sh_cl_dma_pcis_q2.awvalid ),
    .m_axi_awready          (sh_cl_dma_pcis_q2.awready ),
    .m_axi_wdata            (sh_cl_dma_pcis_q2.wdata   ),
    .m_axi_wstrb            (sh_cl_dma_pcis_q2.wstrb   ),
    .m_axi_wvalid           (sh_cl_dma_pcis_q2.wvalid  ),
    .m_axi_wlast            (sh_cl_dma_pcis_q2.wlast   ),
    .m_axi_wready           (sh_cl_dma_pcis_q2.wready  ),
    .m_axi_bresp            (sh_cl_dma_pcis_q2.bresp   ),
    .m_axi_bvalid           (sh_cl_dma_pcis_q2.bvalid  ),
    .m_axi_bid              (sh_cl_dma_pcis_q2.bid     ),
    .m_axi_bready           (sh_cl_dma_pcis_q2.bready  ),
    .m_axi_arid             (sh_cl_dma_pcis_q2.arid    ),
    .m_axi_araddr           (sh_cl_dma_pcis_q2.araddr  ),
    .m_axi_arlen            (sh_cl_dma_pcis_q2.arlen   ),
    .m_axi_arsize           (sh_cl_dma_pcis_q2.arsize  ),
    .m_axi_arburst          (sh_cl_dma_pcis_q2.arburst ),
    .m_axi_arlock           (                          ),
    .m_axi_arcache          (                          ),
    .m_axi_arprot           (                          ),
    .m_axi_arregion         (                          ),
    .m_axi_arqos            (                          ),
    .m_axi_arvalid          (sh_cl_dma_pcis_q2.arvalid ),
    .m_axi_arready          (sh_cl_dma_pcis_q2.arready ),
    .m_axi_rid              (sh_cl_dma_pcis_q2.rid     ),
    .m_axi_rdata            (sh_cl_dma_pcis_q2.rdata   ),
    .m_axi_rresp            (sh_cl_dma_pcis_q2.rresp   ),
    .m_axi_rlast            (sh_cl_dma_pcis_q2.rlast   ),
    .m_axi_rvalid           (sh_cl_dma_pcis_q2.rvalid  ),
    .m_axi_rready           (sh_cl_dma_pcis_q2.rready  )
  );

  //----------------------------------------------------
  // axi interconnect for DDR address decodes
  // Addr 0x00_0000_0000 - 0x0F_FFFF_FFFF (64GB) : DDR
  // Addr 0x10_0000_0000 - 0x1C_FFFF_FFFF (16GB) : HBM
  //----------------------------------------------------
  cl_axi_sc_2x2_wrapper AXI4_CROSSBAR
  (
    .aclk_250               (aclk                      ),
    .aresetn_250            (slr1_sync_aresetn         ),

    .XDMA_awid              (sh_cl_dma_pcis_q2.awid    ),
    .XDMA_awaddr            (sh_cl_dma_pcis_q2.awaddr  ),
    .XDMA_awvalid           (sh_cl_dma_pcis_q2.awvalid ),
    .XDMA_awready           (sh_cl_dma_pcis_q2.awready ),
    .XDMA_awsize            (sh_cl_dma_pcis_q2.awsize  ),
    .XDMA_awlen             (sh_cl_dma_pcis_q2.awlen   ),
    .XDMA_awburst           (sh_cl_dma_pcis_q2.awburst ),
    .XDMA_awcache           (`DEF_AXCACHE              ),
    .XDMA_awlock            (`DEF_AXLOCK               ),
    .XDMA_awprot            (`DEF_AXPROT               ),
    .XDMA_awqos             (`DEF_AXQOS                ),
    .XDMA_wdata             (sh_cl_dma_pcis_q2.wdata   ),
    .XDMA_wvalid            (sh_cl_dma_pcis_q2.wvalid  ),
    .XDMA_wready            (sh_cl_dma_pcis_q2.wready  ),
    .XDMA_wstrb             (sh_cl_dma_pcis_q2.wstrb   ),
    .XDMA_wlast             (sh_cl_dma_pcis_q2.wlast   ),
    .XDMA_bid               (sh_cl_dma_pcis_q2.bid     ),
    .XDMA_bvalid            (sh_cl_dma_pcis_q2.bvalid  ),
    .XDMA_bready            (sh_cl_dma_pcis_q2.bready  ),
    .XDMA_bresp             (sh_cl_dma_pcis_q2.bresp   ),
    .XDMA_arid              (sh_cl_dma_pcis_q2.arid    ),
    .XDMA_araddr            (sh_cl_dma_pcis_q2.araddr  ),
    .XDMA_arvalid           (sh_cl_dma_pcis_q2.arvalid ),
    .XDMA_arready           (sh_cl_dma_pcis_q2.arready ),
    .XDMA_arsize            (sh_cl_dma_pcis_q2.arsize  ),
    .XDMA_arlen             (sh_cl_dma_pcis_q2.arlen   ),
    .XDMA_arburst           (sh_cl_dma_pcis_q2.arburst ),
    .XDMA_arcache           (`DEF_AXCACHE              ),
    .XDMA_arlock            (`DEF_AXLOCK               ),
    .XDMA_arprot            (`DEF_AXPROT               ),
    .XDMA_arqos             (`DEF_AXQOS                ),
    .XDMA_rid               (sh_cl_dma_pcis_q2.rid     ),
    .XDMA_rdata             (sh_cl_dma_pcis_q2.rdata   ),
    .XDMA_rresp             (sh_cl_dma_pcis_q2.rresp   ),
    .XDMA_rvalid            (sh_cl_dma_pcis_q2.rvalid  ),
    .XDMA_rready            (sh_cl_dma_pcis_q2.rready  ),
    .XDMA_rlast             (sh_cl_dma_pcis_q2.rlast   ),

    .ATG_awid               (cl_axi_mstr_bus.awid      ),
    .ATG_awaddr             (cl_axi_mstr_bus.awaddr    ),
    .ATG_awvalid            (cl_axi_mstr_bus.awvalid   ),
    .ATG_awready            (cl_axi_mstr_bus.awready   ),
    .ATG_awsize             (cl_axi_mstr_bus.awsize    ),
    .ATG_awlen              (cl_axi_mstr_bus.awlen     ),
    .ATG_awburst            (`DEF_AXBURST              ),
    .ATG_awcache            (`DEF_AXCACHE              ),
    .ATG_awlock             (`DEF_AXLOCK               ),
    .ATG_awprot             (`DEF_AXPROT               ),
    .ATG_awqos              (`DEF_AXQOS                ),
    .ATG_wdata              (cl_axi_mstr_bus.wdata     ),
    .ATG_wvalid             (cl_axi_mstr_bus.wvalid    ),
    .ATG_wready             (cl_axi_mstr_bus.wready    ),
    .ATG_wstrb              (cl_axi_mstr_bus.wstrb     ),
    .ATG_wlast              (cl_axi_mstr_bus.wlast     ),
    .ATG_bid                (cl_axi_mstr_bus.bid       ),
    .ATG_bvalid             (cl_axi_mstr_bus.bvalid    ),
    .ATG_bready             (cl_axi_mstr_bus.bready    ),
    .ATG_bresp              (cl_axi_mstr_bus.bresp     ),
    .ATG_arid               (cl_axi_mstr_bus.arid      ),
    .ATG_araddr             (cl_axi_mstr_bus.araddr    ),
    .ATG_arvalid            (cl_axi_mstr_bus.arvalid   ),
    .ATG_arready            (cl_axi_mstr_bus.arready   ),
    .ATG_arsize             (cl_axi_mstr_bus.arsize    ),
    .ATG_arlen              (cl_axi_mstr_bus.arlen     ),
    .ATG_arburst            (`DEF_AXBURST              ),
    .ATG_arcache            (`DEF_AXCACHE              ),
    .ATG_arlock             (`DEF_AXLOCK               ),
    .ATG_arprot             (`DEF_AXPROT               ),
    .ATG_arqos              (`DEF_AXQOS                ),
    .ATG_rid                (cl_axi_mstr_bus.rid       ),
    .ATG_rdata              (cl_axi_mstr_bus.rdata     ),
    .ATG_rresp              (cl_axi_mstr_bus.rresp     ),
    .ATG_rvalid             (cl_axi_mstr_bus.rvalid    ),
    .ATG_rready             (cl_axi_mstr_bus.rready    ),
    .ATG_rlast              (cl_axi_mstr_bus.rlast     ),

    .DDRA_awaddr            (xbar_axi_ddra.awaddr      ),
    .DDRA_awsize            (xbar_axi_ddra.awsize      ),
    .DDRA_awlen             (xbar_axi_ddra.awlen       ),
    .DDRA_awvalid           (xbar_axi_ddra.awvalid     ),
    .DDRA_awready           (xbar_axi_ddra.awready     ),
    .DDRA_awburst           (xbar_axi_ddra.awburst     ),
    .DDRA_awcache           (                          ),
    .DDRA_awlock            (                          ),
    .DDRA_awprot            (                          ),
    .DDRA_awqos             (                          ),
    .DDRA_wdata             (xbar_axi_ddra.wdata       ),
    .DDRA_wvalid            (xbar_axi_ddra.wvalid      ),
    .DDRA_wready            (xbar_axi_ddra.wready      ),
    .DDRA_wstrb             (xbar_axi_ddra.wstrb       ),
    .DDRA_wlast             (xbar_axi_ddra.wlast       ),
    .DDRA_bresp             (xbar_axi_ddra.bresp       ),
    .DDRA_bvalid            (xbar_axi_ddra.bvalid      ),
    .DDRA_bready            (xbar_axi_ddra.bready      ),
    .DDRA_araddr            (xbar_axi_ddra.araddr      ),
    .DDRA_arvalid           (xbar_axi_ddra.arvalid     ),
    .DDRA_arready           (xbar_axi_ddra.arready     ),
    .DDRA_arsize            (xbar_axi_ddra.arsize      ),
    .DDRA_arlen             (xbar_axi_ddra.arlen       ),
    .DDRA_arburst           (xbar_axi_ddra.arburst     ),
    .DDRA_arcache           (                          ),
    .DDRA_arlock            (                          ),
    .DDRA_arprot            (                          ),
    .DDRA_arqos             (                          ),
    .DDRA_rdata             (xbar_axi_ddra.rdata       ),
    .DDRA_rresp             (xbar_axi_ddra.rresp       ),
    .DDRA_rvalid            (xbar_axi_ddra.rvalid      ),
    .DDRA_rready            (xbar_axi_ddra.rready      ),
    .DDRA_rlast             (xbar_axi_ddra.rlast       ),

    .DDRB_awaddr            (xbar_axi_ddrb.awaddr      ),
    .DDRB_awsize            (xbar_axi_ddrb.awsize      ),
    .DDRB_awlen             (xbar_axi_ddrb.awlen       ),
    .DDRB_awvalid           (xbar_axi_ddrb.awvalid     ),
    .DDRB_awready           (xbar_axi_ddrb.awready     ),
    .DDRB_awburst           (xbar_axi_ddrb.awburst     ),
    .DDRB_awcache           (                          ),
    .DDRB_awlock            (                          ),
    .DDRB_awprot            (                          ),
    .DDRB_awqos             (                          ),
    .DDRB_wdata             (xbar_axi_ddrb.wdata       ),
    .DDRB_wvalid            (xbar_axi_ddrb.wvalid      ),
    .DDRB_wready            (xbar_axi_ddrb.wready      ),
    .DDRB_wstrb             (xbar_axi_ddrb.wstrb       ),
    .DDRB_wlast             (xbar_axi_ddrb.wlast       ),
    .DDRB_bresp             (xbar_axi_ddrb.bresp       ),
    .DDRB_bvalid            (xbar_axi_ddrb.bvalid      ),
    .DDRB_bready            (xbar_axi_ddrb.bready      ),
    .DDRB_araddr            (xbar_axi_ddrb.araddr      ),
    .DDRB_arvalid           (xbar_axi_ddrb.arvalid     ),
    .DDRB_arready           (xbar_axi_ddrb.arready     ),
    .DDRB_arsize            (xbar_axi_ddrb.arsize      ),
    .DDRB_arlen             (xbar_axi_ddrb.arlen       ),
    .DDRB_arburst           (xbar_axi_ddrb.arburst     ),
    .DDRB_arcache           (                          ),
    .DDRB_arlock            (                          ),
    .DDRB_arprot            (                          ),
    .DDRB_arqos             (                          ),
    .DDRB_rdata             (xbar_axi_ddrb.rdata       ),
    .DDRB_rresp             (xbar_axi_ddrb.rresp       ),
    .DDRB_rvalid            (xbar_axi_ddrb.rvalid      ),
    .DDRB_rready            (xbar_axi_ddrb.rready      ),
    .DDRB_rlast             (xbar_axi_ddrb.rlast       )
  );

  axi_register_slice AXI4_REG_SLC_DDRA_SLR1
  (
    .aclk                   (aclk                      ),
    .aresetn                (slr1_sync_aresetn         ),

    .s_axi_awid             (16'b0                     ),
    .s_axi_awaddr           (xbar_axi_ddra.awaddr      ),
    .s_axi_awlen            (xbar_axi_ddra.awlen       ),
    .s_axi_awsize           (xbar_axi_ddra.awsize      ),
    .s_axi_awvalid          (xbar_axi_ddra.awvalid     ),
    .s_axi_awready          (xbar_axi_ddra.awready     ),
    .s_axi_awburst          (xbar_axi_ddra.awburst     ),
    .s_axi_awlock           (`DEF_AXLOCK               ),
    .s_axi_awcache          (`DEF_AXCACHE              ),
    .s_axi_awprot           (`DEF_AXPROT               ),
    .s_axi_awregion         (`DEF_AXREGION             ),
    .s_axi_awqos            (`DEF_AXQOS                ),
    .s_axi_wdata            (xbar_axi_ddra.wdata       ),
    .s_axi_wstrb            (xbar_axi_ddra.wstrb       ),
    .s_axi_wlast            (xbar_axi_ddra.wlast       ),
    .s_axi_wvalid           (xbar_axi_ddra.wvalid      ),
    .s_axi_wready           (xbar_axi_ddra.wready      ),
    .s_axi_bid              (xbar_axi_ddra.bid         ),
    .s_axi_bresp            (xbar_axi_ddra.bresp       ),
    .s_axi_bvalid           (xbar_axi_ddra.bvalid      ),
    .s_axi_bready           (xbar_axi_ddra.bready      ),
    .s_axi_arid             (16'b0                     ),
    .s_axi_araddr           (xbar_axi_ddra.araddr      ),
    .s_axi_arlen            (xbar_axi_ddra.arlen       ),
    .s_axi_arsize           (xbar_axi_ddra.arsize      ),
    .s_axi_arburst          (xbar_axi_ddra.arburst     ),
    .s_axi_arlock           (`DEF_AXLOCK               ),
    .s_axi_arcache          (`DEF_AXCACHE              ),
    .s_axi_arprot           (`DEF_AXPROT               ),
    .s_axi_arregion         (`DEF_AXREGION             ),
    .s_axi_arqos            (`DEF_AXQOS                ),
    .s_axi_arvalid          (xbar_axi_ddra.arvalid     ),
    .s_axi_arready          (xbar_axi_ddra.arready     ),
    .s_axi_rid              (xbar_axi_ddra.rid         ),
    .s_axi_rdata            (xbar_axi_ddra.rdata       ),
    .s_axi_rresp            (xbar_axi_ddra.rresp       ),
    .s_axi_rlast            (xbar_axi_ddra.rlast       ),
    .s_axi_rvalid           (xbar_axi_ddra.rvalid      ),
    .s_axi_rready           (xbar_axi_ddra.rready      ),

    .m_axi_awid             (xbar_axi_ddra_q.awid      ),
    .m_axi_awaddr           (xbar_axi_ddra_q.awaddr    ),
    .m_axi_awlen            (xbar_axi_ddra_q.awlen     ),
    .m_axi_awsize           (xbar_axi_ddra_q.awsize    ),
    .m_axi_awburst          (xbar_axi_ddra_q.awburst   ),
    .m_axi_awlock           (                          ),
    .m_axi_awcache          (                          ),
    .m_axi_awprot           (                          ),
    .m_axi_awregion         (                          ),
    .m_axi_awqos            (                          ),
    .m_axi_awvalid          (xbar_axi_ddra_q.awvalid   ),
    .m_axi_awready          (xbar_axi_ddra_q.awready   ),
    .m_axi_wdata            (xbar_axi_ddra_q.wdata     ),
    .m_axi_wstrb            (xbar_axi_ddra_q.wstrb     ),
    .m_axi_wvalid           (xbar_axi_ddra_q.wvalid    ),
    .m_axi_wlast            (xbar_axi_ddra_q.wlast     ),
    .m_axi_wready           (xbar_axi_ddra_q.wready    ),
    .m_axi_bresp            (xbar_axi_ddra_q.bresp     ),
    .m_axi_bvalid           (xbar_axi_ddra_q.bvalid    ),
    .m_axi_bid              (xbar_axi_ddra_q.bid       ),
    .m_axi_bready           (xbar_axi_ddra_q.bready    ),
    .m_axi_arid             (xbar_axi_ddra_q.arid      ),
    .m_axi_araddr           (xbar_axi_ddra_q.araddr    ),
    .m_axi_arlen            (xbar_axi_ddra_q.arlen     ),
    .m_axi_arsize           (xbar_axi_ddra_q.arsize    ),
    .m_axi_arburst          (xbar_axi_ddra_q.arburst   ),
    .m_axi_arlock           (                          ),
    .m_axi_arcache          (                          ),
    .m_axi_arprot           (                          ),
    .m_axi_arregion         (                          ),
    .m_axi_arqos            (                          ),
    .m_axi_arvalid          (xbar_axi_ddra_q.arvalid   ),
    .m_axi_arready          (xbar_axi_ddra_q.arready   ),
    .m_axi_rid              (xbar_axi_ddra_q.rid       ),
    .m_axi_rdata            (xbar_axi_ddra_q.rdata     ),
    .m_axi_rresp            (xbar_axi_ddra_q.rresp     ),
    .m_axi_rlast            (xbar_axi_ddra_q.rlast     ),
    .m_axi_rvalid           (xbar_axi_ddra_q.rvalid    ),
    .m_axi_rready           (xbar_axi_ddra_q.rready    )
  );

  axi_register_slice AXI4_REG_SLC_DDRA_SLR2
  (
    .aclk                   (aclk                      ),
    .aresetn                (slr2_sync_aresetn         ),

    .s_axi_awid             (xbar_axi_ddra_q.awid      ),
    .s_axi_awaddr           (xbar_axi_ddra_q.awaddr    ),
    .s_axi_awlen            (xbar_axi_ddra_q.awlen     ),
    .s_axi_awsize           (xbar_axi_ddra_q.awsize    ),
    .s_axi_awburst          (xbar_axi_ddra_q.awburst   ),
    .s_axi_awlock           (`DEF_AXLOCK               ),
    .s_axi_awcache          (`DEF_AXCACHE              ),
    .s_axi_awprot           (`DEF_AXPROT               ),
    .s_axi_awregion         (`DEF_AXREGION             ),
    .s_axi_awqos            (`DEF_AXQOS                ),
    .s_axi_awvalid          (xbar_axi_ddra_q.awvalid   ),
    .s_axi_awready          (xbar_axi_ddra_q.awready   ),
    .s_axi_wdata            (xbar_axi_ddra_q.wdata     ),
    .s_axi_wstrb            (xbar_axi_ddra_q.wstrb     ),
    .s_axi_wlast            (xbar_axi_ddra_q.wlast     ),
    .s_axi_wvalid           (xbar_axi_ddra_q.wvalid    ),
    .s_axi_wready           (xbar_axi_ddra_q.wready    ),
    .s_axi_bid              (xbar_axi_ddra_q.bid       ),
    .s_axi_bresp            (xbar_axi_ddra_q.bresp     ),
    .s_axi_bvalid           (xbar_axi_ddra_q.bvalid    ),
    .s_axi_bready           (xbar_axi_ddra_q.bready    ),
    .s_axi_arid             (xbar_axi_ddra_q.arid      ),
    .s_axi_araddr           (xbar_axi_ddra_q.araddr    ),
    .s_axi_arlen            (xbar_axi_ddra_q.arlen     ),
    .s_axi_arsize           (xbar_axi_ddra_q.arsize    ),
    .s_axi_arburst          (xbar_axi_ddra_q.arburst   ),
    .s_axi_arlock           (`DEF_AXLOCK               ),
    .s_axi_arcache          (`DEF_AXCACHE              ),
    .s_axi_arprot           (`DEF_AXPROT               ),
    .s_axi_arregion         (`DEF_AXREGION             ),
    .s_axi_arqos            (`DEF_AXQOS                ),
    .s_axi_arvalid          (xbar_axi_ddra_q.arvalid   ),
    .s_axi_arready          (xbar_axi_ddra_q.arready   ),
    .s_axi_rid              (xbar_axi_ddra_q.rid       ),
    .s_axi_rdata            (xbar_axi_ddra_q.rdata     ),
    .s_axi_rresp            (xbar_axi_ddra_q.rresp     ),
    .s_axi_rlast            (xbar_axi_ddra_q.rlast     ),
    .s_axi_rvalid           (xbar_axi_ddra_q.rvalid    ),
    .s_axi_rready           (xbar_axi_ddra_q.rready    ),

    .m_axi_awid             (xbar_axi_ddra_q2.awid     ),
    .m_axi_awaddr           (xbar_axi_ddra_q2.awaddr   ),
    .m_axi_awlen            (xbar_axi_ddra_q2.awlen    ),
    .m_axi_awsize           (xbar_axi_ddra_q2.awsize   ),
    .m_axi_awburst          (xbar_axi_ddra_q2.awburst  ),
    .m_axi_awlock           (                          ),
    .m_axi_awcache          (                          ),
    .m_axi_awprot           (                          ),
    .m_axi_awregion         (                          ),
    .m_axi_awqos            (                          ),
    .m_axi_awvalid          (xbar_axi_ddra_q2.awvalid  ),
    .m_axi_awready          (xbar_axi_ddra_q2.awready  ),
    .m_axi_wdata            (xbar_axi_ddra_q2.wdata    ),
    .m_axi_wstrb            (xbar_axi_ddra_q2.wstrb    ),
    .m_axi_wvalid           (xbar_axi_ddra_q2.wvalid   ),
    .m_axi_wlast            (xbar_axi_ddra_q2.wlast    ),
    .m_axi_wready           (xbar_axi_ddra_q2.wready   ),
    .m_axi_bresp            (xbar_axi_ddra_q2.bresp    ),
    .m_axi_bvalid           (xbar_axi_ddra_q2.bvalid   ),
    .m_axi_bid              (xbar_axi_ddra_q2.bid      ),
    .m_axi_bready           (xbar_axi_ddra_q2.bready   ),
    .m_axi_arid             (xbar_axi_ddra_q2.arid     ),
    .m_axi_araddr           (xbar_axi_ddra_q2.araddr   ),
    .m_axi_arlen            (xbar_axi_ddra_q2.arlen    ),
    .m_axi_arsize           (xbar_axi_ddra_q2.arsize   ),
    .m_axi_arburst          (xbar_axi_ddra_q2.arburst  ),
    .m_axi_arlock           (                          ),
    .m_axi_arcache          (                          ),
    .m_axi_arprot           (                          ),
    .m_axi_arregion         (                          ),
    .m_axi_arqos            (                          ),
    .m_axi_arvalid          (xbar_axi_ddra_q2.arvalid  ),
    .m_axi_arready          (xbar_axi_ddra_q2.arready  ),
    .m_axi_rid              (xbar_axi_ddra_q2.rid      ),
    .m_axi_rdata            (xbar_axi_ddra_q2.rdata    ),
    .m_axi_rresp            (xbar_axi_ddra_q2.rresp    ),
    .m_axi_rlast            (xbar_axi_ddra_q2.rlast    ),
    .m_axi_rvalid           (xbar_axi_ddra_q2.rvalid   ),
    .m_axi_rready           (xbar_axi_ddra_q2.rready   )
  );

  //----------------------------
  // ATG/scrubber for DDRA
  //----------------------------

  localparam NUM_CFG_STGS_CL_DDR_ATG = 4;

  lib_pipe
  #(
    .WIDTH                  (32+32+1+1                 ),
    .STAGES                 (NUM_CFG_STGS_CL_DDR_ATG   )
  )
  PIPE_CFG_REQ_DDRA
  (
    .clk                    (aclk                      ),
    .rst_n                  (slr2_sync_aresetn         ),
    .in_bus                 ({ddra_tst_cfg_bus.addr,
                              ddra_tst_cfg_bus.wdata,
                              ddra_tst_cfg_bus.wr,
                              ddra_tst_cfg_bus.rd}     ),
    .out_bus                ({ddra_tst_cfg_bus_q.addr,
                              ddra_tst_cfg_bus_q.wdata,
                              ddra_tst_cfg_bus_q.wr,
                              ddra_tst_cfg_bus_q.rd}   )
  );

  lib_pipe
  #(
    .WIDTH                  (32+1                      ),
    .STAGES                 (NUM_CFG_STGS_CL_DDR_ATG   )
  )
  PIPE_CFG_ACK_DDRA
  (
    .clk                    (aclk                      ),
    .rst_n                  (slr2_sync_aresetn         ),
    .in_bus                 ({ddra_tst_cfg_bus_q.ack,
                              ddra_tst_cfg_bus_q.rdata}),
    .out_bus                ({ddra_tst_cfg_bus.ack,
                              ddra_tst_cfg_bus.rdata}  )
  );

  lib_pipe
  #(
    .WIDTH                  (2+3+64                    ),
    .STAGES                 (NUM_CFG_STGS_CL_DDR_ATG   )
  )
  PIPE_SCRB_DDRA
  (
    .clk                    (aclk                      ),
    .rst_n                  (slr2_sync_aresetn         ),
    .in_bus                 ({ddra_scrb_bus.enable,
                              ddra_scrb_bus_q.done,
                              ddra_scrb_bus_q.state,
                              ddra_scrb_bus_q.addr}    ),
    .out_bus                ({ddra_scrb_bus_q.enable,
                              ddra_scrb_bus.done,
                              ddra_scrb_bus.state,
                              ddra_scrb_bus.addr}      )
  );

  cl_tst_scrb
  #(
    .DATA_WIDTH             (512                       ),
    .SCRB_BURST_LEN_MINUS1  (SCRB_BURST_LEN_MINUS1     ),
    .SCRB_MAX_ADDR          (SCRB_MAX_ADDR             ),
    .NO_SCRB_INST           (NO_SCRB_INST              )
  )
  CL_TST_DDRA
  (
    .clk                    (aclk                      ),
    .rst_n                  (slr2_sync_aresetn         ),

    .cfg_addr               (ddra_tst_cfg_bus_q.addr   ),
    .cfg_wdata              (ddra_tst_cfg_bus_q.wdata  ),
    .cfg_wr                 (ddra_tst_cfg_bus_q.wr     ),
    .cfg_rd                 (ddra_tst_cfg_bus_q.rd     ),
    .tst_cfg_ack            (ddra_tst_cfg_bus_q.ack    ),
    .tst_cfg_rdata          (ddra_tst_cfg_bus_q.rdata  ),

    .scrb_enable            (ddra_scrb_bus_q.enable    ),
    .scrb_done              (ddra_scrb_bus_q.done      ),
    .scrb_dbg_state         (ddra_scrb_bus_q.state     ),
    .scrb_dbg_addr          (ddra_scrb_bus_q.addr      ),

    .slv_awid               (xbar_axi_ddra_q2.awid     ),
    .slv_awaddr             (xbar_axi_ddra_q2.awaddr   ),
    .slv_awlen              (xbar_axi_ddra_q2.awlen    ),
    .slv_awsize             (xbar_axi_ddra_q2.awsize   ),
    .slv_awvalid            (xbar_axi_ddra_q2.awvalid  ),
    .slv_awready            (xbar_axi_ddra_q2.awready  ),
    .slv_awuser             (11'b0                     ),
    .slv_wid                (7'b0                      ),
    .slv_wdata              (xbar_axi_ddra_q2.wdata    ),
    .slv_wstrb              (xbar_axi_ddra_q2.wstrb    ),
    .slv_wlast              (xbar_axi_ddra_q2.wlast    ),
    .slv_wvalid             (xbar_axi_ddra_q2.wvalid   ),
    .slv_wready             (xbar_axi_ddra_q2.wready   ),
    .slv_bid                (xbar_axi_ddra_q2.bid      ),
    .slv_bresp              (xbar_axi_ddra_q2.bresp    ),
    .slv_buser              (                          ),
    .slv_bvalid             (xbar_axi_ddra_q2.bvalid   ),
    .slv_bready             (xbar_axi_ddra_q2.bready   ),
    .slv_arid               (xbar_axi_ddra_q2.arid     ),
    .slv_araddr             (xbar_axi_ddra_q2.araddr   ),
    .slv_arlen              (xbar_axi_ddra_q2.arlen    ),
    .slv_arsize             (xbar_axi_ddra_q2.arsize   ),
    .slv_arvalid            (xbar_axi_ddra_q2.arvalid  ),
    .slv_aruser             (11'b0                     ),
    .slv_arready            (xbar_axi_ddra_q2.arready  ),
    .slv_rid                (xbar_axi_ddra_q2.rid      ),
    .slv_rdata              (xbar_axi_ddra_q2.rdata    ),
    .slv_rresp              (xbar_axi_ddra_q2.rresp    ),
    .slv_rlast              (xbar_axi_ddra_q2.rlast    ),
    .slv_ruser              (                          ),
    .slv_rvalid             (xbar_axi_ddra_q2.rvalid   ),
    .slv_rready             (xbar_axi_ddra_q2.rready   ),

    .awid                   (scrb_axi_ddra.awid        ),
    .awaddr                 (scrb_axi_ddra.awaddr      ),
    .awlen                  (scrb_axi_ddra.awlen       ),
    .awsize                 (scrb_axi_ddra.awsize      ),
    .awuser                 (                          ),
    .awvalid                (scrb_axi_ddra.awvalid     ),
    .awready                (scrb_axi_ddra.awready     ),
    .wid                    (scrb_axi_ddra.wid[8:0]    ),
    .wdata                  (scrb_axi_ddra.wdata       ),
    .wstrb                  (scrb_axi_ddra.wstrb       ),
    .wlast                  (scrb_axi_ddra.wlast       ),
    .wvalid                 (scrb_axi_ddra.wvalid      ),
    .wready                 (scrb_axi_ddra.wready      ),
    .bid                    (scrb_axi_ddra.bid         ),
    .bresp                  (scrb_axi_ddra.bresp       ),
    .buser                  (18'h0                     ),
    .bvalid                 (scrb_axi_ddra.bvalid      ),
    .bready                 (scrb_axi_ddra.bready      ),
    .arid                   (scrb_axi_ddra.arid        ),
    .araddr                 (scrb_axi_ddra.araddr      ),
    .arlen                  (scrb_axi_ddra.arlen       ),
    .arsize                 (scrb_axi_ddra.arsize      ),
    .aruser                 (                          ),
    .arvalid                (scrb_axi_ddra.arvalid     ),
    .arready                (scrb_axi_ddra.arready     ),
    .rid                    (scrb_axi_ddra.rid         ),
    .rdata                  (scrb_axi_ddra.rdata       ),
    .rresp                  (scrb_axi_ddra.rresp       ),
    .rlast                  (scrb_axi_ddra.rlast       ),
    .ruser                  (18'h0                     ),
    .rvalid                 (scrb_axi_ddra.rvalid      ),
    .rready                 (scrb_axi_ddra.rready      )
  );

  assign scrb_axi_ddra.wid[15:9] = 'b0;
  assign scrb_axi_ddra.awburst   = `DEF_AXBURST;
  assign scrb_axi_ddra.arburst   = `DEF_AXBURST;

  axi_register_slice AXI4_REG_SLC_DDRB_SLR1
  (
    .aclk                   (aclk                      ),
    .aresetn                (slr1_sync_aresetn         ),

    .s_axi_awid             (16'b0                     ),
    .s_axi_awaddr           (xbar_axi_ddrb.awaddr      ),
    .s_axi_awlen            (xbar_axi_ddrb.awlen       ),
    .s_axi_awsize           (xbar_axi_ddrb.awsize      ),
    .s_axi_awburst          (xbar_axi_ddrb.awburst     ),
    .s_axi_awlock           (`DEF_AXLOCK               ),
    .s_axi_awcache          (`DEF_AXCACHE              ),
    .s_axi_awprot           (`DEF_AXPROT               ),
    .s_axi_awregion         (`DEF_AXREGION             ),
    .s_axi_awqos            (`DEF_AXQOS                ),
    .s_axi_awvalid          (xbar_axi_ddrb.awvalid     ),
    .s_axi_awready          (xbar_axi_ddrb.awready     ),
    .s_axi_wdata            (xbar_axi_ddrb.wdata       ),
    .s_axi_wstrb            (xbar_axi_ddrb.wstrb       ),
    .s_axi_wlast            (xbar_axi_ddrb.wlast       ),
    .s_axi_wvalid           (xbar_axi_ddrb.wvalid      ),
    .s_axi_wready           (xbar_axi_ddrb.wready      ),
    .s_axi_bid              (xbar_axi_ddrb.bid         ),
    .s_axi_bresp            (xbar_axi_ddrb.bresp       ),
    .s_axi_bvalid           (xbar_axi_ddrb.bvalid      ),
    .s_axi_bready           (xbar_axi_ddrb.bready      ),
    .s_axi_arid             (16'b0                     ),
    .s_axi_araddr           (xbar_axi_ddrb.araddr      ),
    .s_axi_arlen            (xbar_axi_ddrb.arlen       ),
    .s_axi_arsize           (xbar_axi_ddrb.arsize      ),
    .s_axi_arburst          (xbar_axi_ddrb.arburst     ),
    .s_axi_arlock           (`DEF_AXLOCK               ),
    .s_axi_arcache          (`DEF_AXCACHE              ),
    .s_axi_arprot           (`DEF_AXPROT               ),
    .s_axi_arregion         (`DEF_AXREGION             ),
    .s_axi_arqos            (`DEF_AXQOS                ),
    .s_axi_arvalid          (xbar_axi_ddrb.arvalid     ),
    .s_axi_arready          (xbar_axi_ddrb.arready     ),
    .s_axi_rid              (xbar_axi_ddrb.rid         ),
    .s_axi_rdata            (xbar_axi_ddrb.rdata       ),
    .s_axi_rresp            (xbar_axi_ddrb.rresp       ),
    .s_axi_rlast            (xbar_axi_ddrb.rlast       ),
    .s_axi_rvalid           (xbar_axi_ddrb.rvalid      ),
    .s_axi_rready           (xbar_axi_ddrb.rready      ),

    .m_axi_awid             (xbar_axi_ddrb_q.awid      ),
    .m_axi_awaddr           (xbar_axi_ddrb_q.awaddr    ),
    .m_axi_awlen            (xbar_axi_ddrb_q.awlen     ),
    .m_axi_awsize           (xbar_axi_ddrb_q.awsize    ),
    .m_axi_awburst          (xbar_axi_ddrb_q.awburst   ),
    .m_axi_awlock           (                          ),
    .m_axi_awcache          (                          ),
    .m_axi_awprot           (                          ),
    .m_axi_awregion         (                          ),
    .m_axi_awqos            (                          ),
    .m_axi_awvalid          (xbar_axi_ddrb_q.awvalid   ),
    .m_axi_awready          (xbar_axi_ddrb_q.awready   ),
    .m_axi_wdata            (xbar_axi_ddrb_q.wdata     ),
    .m_axi_wstrb            (xbar_axi_ddrb_q.wstrb     ),
    .m_axi_wvalid           (xbar_axi_ddrb_q.wvalid    ),
    .m_axi_wlast            (xbar_axi_ddrb_q.wlast     ),
    .m_axi_wready           (xbar_axi_ddrb_q.wready    ),
    .m_axi_bresp            (xbar_axi_ddrb_q.bresp     ),
    .m_axi_bvalid           (xbar_axi_ddrb_q.bvalid    ),
    .m_axi_bid              (xbar_axi_ddrb_q.bid       ),
    .m_axi_bready           (xbar_axi_ddrb_q.bready    ),
    .m_axi_arid             (xbar_axi_ddrb_q.arid      ),
    .m_axi_araddr           (xbar_axi_ddrb_q.araddr    ),
    .m_axi_arlen            (xbar_axi_ddrb_q.arlen     ),
    .m_axi_arsize           (xbar_axi_ddrb_q.arsize    ),
    .m_axi_arburst          (xbar_axi_ddrb_q.arburst   ),
    .m_axi_arlock           (                          ),
    .m_axi_arcache          (                          ),
    .m_axi_arprot           (                          ),
    .m_axi_arregion         (                          ),
    .m_axi_arqos            (                          ),
    .m_axi_arvalid          (xbar_axi_ddrb_q.arvalid   ),
    .m_axi_arready          (xbar_axi_ddrb_q.arready   ),
    .m_axi_rid              (xbar_axi_ddrb_q.rid       ),
    .m_axi_rdata            (xbar_axi_ddrb_q.rdata     ),
    .m_axi_rresp            (xbar_axi_ddrb_q.rresp     ),
    .m_axi_rlast            (xbar_axi_ddrb_q.rlast     ),
    .m_axi_rvalid           (xbar_axi_ddrb_q.rvalid    ),
    .m_axi_rready           (xbar_axi_ddrb_q.rready    )
  );

  axi_register_slice AXI4_REG_SLC_DDRB_SLR0
  (
    .aclk                   (aclk                      ),
    .aresetn                (slr0_sync_aresetn         ),

    .s_axi_awid             (xbar_axi_ddrb_q.awid      ),
    .s_axi_awaddr           (xbar_axi_ddrb_q.awaddr    ),
    .s_axi_awlen            (xbar_axi_ddrb_q.awlen     ),
    .s_axi_awsize           (xbar_axi_ddrb_q.awsize    ),
    .s_axi_awburst          (xbar_axi_ddrb_q.awburst   ),
    .s_axi_awlock           (`DEF_AXLOCK               ),
    .s_axi_awcache          (`DEF_AXCACHE              ),
    .s_axi_awprot           (`DEF_AXPROT               ),
    .s_axi_awregion         (`DEF_AXREGION             ),
    .s_axi_awqos            (`DEF_AXQOS                ),
    .s_axi_awvalid          (xbar_axi_ddrb_q.awvalid   ),
    .s_axi_awready          (xbar_axi_ddrb_q.awready   ),
    .s_axi_wdata            (xbar_axi_ddrb_q.wdata     ),
    .s_axi_wstrb            (xbar_axi_ddrb_q.wstrb     ),
    .s_axi_wlast            (xbar_axi_ddrb_q.wlast     ),
    .s_axi_wvalid           (xbar_axi_ddrb_q.wvalid    ),
    .s_axi_wready           (xbar_axi_ddrb_q.wready    ),
    .s_axi_bid              (xbar_axi_ddrb_q.bid       ),
    .s_axi_bresp            (xbar_axi_ddrb_q.bresp     ),
    .s_axi_bvalid           (xbar_axi_ddrb_q.bvalid    ),
    .s_axi_bready           (xbar_axi_ddrb_q.bready    ),
    .s_axi_arid             (xbar_axi_ddrb_q.arid      ),
    .s_axi_araddr           (xbar_axi_ddrb_q.araddr    ),
    .s_axi_arlen            (xbar_axi_ddrb_q.arlen     ),
    .s_axi_arburst          (xbar_axi_ddrb_q.arburst   ),
    .s_axi_arlock           (`DEF_AXLOCK               ),
    .s_axi_arcache          (`DEF_AXCACHE              ),
    .s_axi_arprot           (`DEF_AXPROT               ),
    .s_axi_arregion         (`DEF_AXREGION             ),
    .s_axi_arqos            (`DEF_AXQOS                ),
    .s_axi_arsize           (xbar_axi_ddrb_q.arsize    ),
    .s_axi_arvalid          (xbar_axi_ddrb_q.arvalid   ),
    .s_axi_arready          (xbar_axi_ddrb_q.arready   ),
    .s_axi_rid              (xbar_axi_ddrb_q.rid       ),
    .s_axi_rdata            (xbar_axi_ddrb_q.rdata     ),
    .s_axi_rresp            (xbar_axi_ddrb_q.rresp     ),
    .s_axi_rlast            (xbar_axi_ddrb_q.rlast     ),
    .s_axi_rvalid           (xbar_axi_ddrb_q.rvalid    ),
    .s_axi_rready           (xbar_axi_ddrb_q.rready    ),

    .m_axi_awid             (xbar_axi_ddrb_q2.awid     ),
    .m_axi_awaddr           (xbar_axi_ddrb_q2.awaddr   ),
    .m_axi_awlen            (xbar_axi_ddrb_q2.awlen    ),
    .m_axi_awsize           (xbar_axi_ddrb_q2.awsize   ),
    .m_axi_awburst          (xbar_axi_ddrb_q2.awburst  ),
    .m_axi_awlock           (                          ),
    .m_axi_awcache          (                          ),
    .m_axi_awprot           (                          ),
    .m_axi_awregion         (                          ),
    .m_axi_awqos            (                          ),
    .m_axi_awvalid          (xbar_axi_ddrb_q2.awvalid  ),
    .m_axi_awready          (xbar_axi_ddrb_q2.awready  ),
    .m_axi_wdata            (xbar_axi_ddrb_q2.wdata    ),
    .m_axi_wstrb            (xbar_axi_ddrb_q2.wstrb    ),
    .m_axi_wvalid           (xbar_axi_ddrb_q2.wvalid   ),
    .m_axi_wlast            (xbar_axi_ddrb_q2.wlast    ),
    .m_axi_wready           (xbar_axi_ddrb_q2.wready   ),
    .m_axi_bresp            (xbar_axi_ddrb_q2.bresp    ),
    .m_axi_bvalid           (xbar_axi_ddrb_q2.bvalid   ),
    .m_axi_bid              (xbar_axi_ddrb_q2.bid      ),
    .m_axi_bready           (xbar_axi_ddrb_q2.bready   ),
    .m_axi_arid             (xbar_axi_ddrb_q2.arid     ),
    .m_axi_araddr           (xbar_axi_ddrb_q2.araddr   ),
    .m_axi_arlen            (xbar_axi_ddrb_q2.arlen    ),
    .m_axi_arsize           (xbar_axi_ddrb_q2.arsize   ),
    .m_axi_arburst          (xbar_axi_ddrb_q2.arburst  ),
    .m_axi_arlock           (                          ),
    .m_axi_arcache          (                          ),
    .m_axi_arprot           (                          ),
    .m_axi_arregion         (                          ),
    .m_axi_arqos            (                          ),
    .m_axi_arvalid          (xbar_axi_ddrb_q2.arvalid  ),
    .m_axi_arready          (xbar_axi_ddrb_q2.arready  ),
    .m_axi_rid              (xbar_axi_ddrb_q2.rid      ),
    .m_axi_rdata            (xbar_axi_ddrb_q2.rdata    ),
    .m_axi_rresp            (xbar_axi_ddrb_q2.rresp    ),
    .m_axi_rlast            (xbar_axi_ddrb_q2.rlast    ),
    .m_axi_rvalid           (xbar_axi_ddrb_q2.rvalid   ),
    .m_axi_rready           (xbar_axi_ddrb_q2.rready   )
  );

  //----------------------------
  // ATG/scrubber for DDRB
  //----------------------------

  lib_pipe
  #(
    .WIDTH                  (32+32+1+1                  ),
    .STAGES                 (NUM_CFG_STGS_CL_DDR_ATG    )
  )
  PIPE_CFG_REQ_DDRB
  (
    .clk                    (aclk                       ),
    .rst_n                  (slr0_sync_aresetn          ),
    .in_bus                 ({ddrb_tst_cfg_bus.addr,
                              ddrb_tst_cfg_bus.wdata,
                              ddrb_tst_cfg_bus.wr,
                              ddrb_tst_cfg_bus.rd}      ),
    .out_bus                ({ddrb_tst_cfg_bus_q.addr,
                              ddrb_tst_cfg_bus_q.wdata,
                              ddrb_tst_cfg_bus_q.wr,
                              ddrb_tst_cfg_bus_q.rd}    )
  );

  lib_pipe
  #(
    .WIDTH                  (32+1                       ),
    .STAGES                 (NUM_CFG_STGS_CL_DDR_ATG    )
  )
  PIPE_CFG_ACK_DDRB
  (
    .clk                    (aclk                       ),
    .rst_n                  (slr0_sync_aresetn          ),
    .in_bus                 ({ddrb_tst_cfg_bus_q.ack,
                              ddrb_tst_cfg_bus_q.rdata} ),
    .out_bus                ({ddrb_tst_cfg_bus.ack,
                              ddrb_tst_cfg_bus.rdata}   )
  );

  lib_pipe
  #(
    .WIDTH                  (2+3+64                     ),
    .STAGES                 (NUM_CFG_STGS_CL_DDR_ATG    )
  )
  PIPE_SCRB_DDRB
  (
    .clk                    (aclk                       ),
    .rst_n                  (slr0_sync_aresetn          ),
    .in_bus                 ({ddrb_scrb_bus.enable,
                              ddrb_scrb_bus_q.done,
                              ddrb_scrb_bus_q.state,
                              ddrb_scrb_bus_q.addr}     ),
    .out_bus                ({ddrb_scrb_bus_q.enable,
                              ddrb_scrb_bus.done,
                              ddrb_scrb_bus.state,
                              ddrb_scrb_bus.addr}       )
  );

  cl_tst_scrb
  #(
    .DATA_WIDTH             (512                        ),
    .SCRB_BURST_LEN_MINUS1  (SCRB_BURST_LEN_MINUS1      ),
    .SCRB_MAX_ADDR          (SCRB_MAX_ADDR              ),
    .NO_SCRB_INST           (NO_SCRB_INST               )
  )
  CL_TST_DDRB
  (
    .clk                    (aclk                       ),
    .rst_n                  (slr0_sync_aresetn          ),

    .cfg_addr               (ddrb_tst_cfg_bus_q.addr    ),
    .cfg_wdata              (ddrb_tst_cfg_bus_q.wdata   ),
    .cfg_wr                 (ddrb_tst_cfg_bus_q.wr      ),
    .cfg_rd                 (ddrb_tst_cfg_bus_q.rd      ),
    .tst_cfg_ack            (ddrb_tst_cfg_bus_q.ack     ),
    .tst_cfg_rdata          (ddrb_tst_cfg_bus_q.rdata   ),

    .scrb_enable            (ddrb_scrb_bus_q.enable     ),
    .scrb_done              (ddrb_scrb_bus_q.done       ),
    .scrb_dbg_state         (ddrb_scrb_bus_q.state      ),
    .scrb_dbg_addr          (ddrb_scrb_bus_q.addr       ),

    .slv_awid               (xbar_axi_ddrb_q2.awid      ),
    .slv_awaddr             (xbar_axi_ddrb_q2.awaddr    ),
    .slv_awlen              (xbar_axi_ddrb_q2.awlen     ),
    .slv_awsize             (xbar_axi_ddrb_q2.awsize    ),
    .slv_awvalid            (xbar_axi_ddrb_q2.awvalid   ),
    .slv_awready            (xbar_axi_ddrb_q2.awready   ),
    .slv_awuser             (11'b0                      ),
    .slv_wid                (7'b0                       ),
    .slv_wdata              (xbar_axi_ddrb_q2.wdata     ),
    .slv_wstrb              (xbar_axi_ddrb_q2.wstrb     ),
    .slv_wlast              (xbar_axi_ddrb_q2.wlast     ),
    .slv_wvalid             (xbar_axi_ddrb_q2.wvalid    ),
    .slv_wready             (xbar_axi_ddrb_q2.wready    ),
    .slv_bid                (xbar_axi_ddrb_q2.bid       ),
    .slv_bresp              (xbar_axi_ddrb_q2.bresp     ),
    .slv_buser              (                           ),
    .slv_bvalid             (xbar_axi_ddrb_q2.bvalid    ),
    .slv_bready             (xbar_axi_ddrb_q2.bready    ),
    .slv_arid               (xbar_axi_ddrb_q2.arid      ),
    .slv_araddr             (xbar_axi_ddrb_q2.araddr    ),
    .slv_arlen              (xbar_axi_ddrb_q2.arlen     ),
    .slv_arsize             (xbar_axi_ddrb_q2.arsize    ),
    .slv_arvalid            (xbar_axi_ddrb_q2.arvalid   ),
    .slv_aruser             (11'b0                      ),
    .slv_arready            (xbar_axi_ddrb_q2.arready   ),
    .slv_rid                (xbar_axi_ddrb_q2.rid       ),
    .slv_rdata              (xbar_axi_ddrb_q2.rdata     ),
    .slv_rresp              (xbar_axi_ddrb_q2.rresp     ),
    .slv_rlast              (xbar_axi_ddrb_q2.rlast     ),
    .slv_ruser              (                           ),
    .slv_rvalid             (xbar_axi_ddrb_q2.rvalid    ),
    .slv_rready             (xbar_axi_ddrb_q2.rready    ),

    .awid                   (scrb_axi_ddrb.awid         ),
    .awaddr                 (scrb_axi_ddrb.awaddr       ),
    .awlen                  (scrb_axi_ddrb.awlen        ),
    .awsize                 (scrb_axi_ddrb.awsize       ),
    .awuser                 (                           ),
    .awvalid                (scrb_axi_ddrb.awvalid      ),
    .awready                (scrb_axi_ddrb.awready      ),
    .wid                    (scrb_axi_ddrb.wid[8:0]     ),
    .wdata                  (scrb_axi_ddrb.wdata        ),
    .wstrb                  (scrb_axi_ddrb.wstrb        ),
    .wlast                  (scrb_axi_ddrb.wlast        ),
    .wvalid                 (scrb_axi_ddrb.wvalid       ),
    .wready                 (scrb_axi_ddrb.wready       ),
    .bid                    (scrb_axi_ddrb.bid          ),
    .bresp                  (scrb_axi_ddrb.bresp        ),
    .buser                  (18'h0                      ),
    .bvalid                 (scrb_axi_ddrb.bvalid       ),
    .bready                 (scrb_axi_ddrb.bready       ),
    .arid                   (scrb_axi_ddrb.arid         ),
    .araddr                 (scrb_axi_ddrb.araddr       ),
    .arlen                  (scrb_axi_ddrb.arlen        ),
    .arsize                 (scrb_axi_ddrb.arsize       ),
    .aruser                 (                           ),
    .arvalid                (scrb_axi_ddrb.arvalid      ),
    .arready                (scrb_axi_ddrb.arready      ),
    .rid                    (scrb_axi_ddrb.rid          ),
    .rdata                  (scrb_axi_ddrb.rdata        ),
    .rresp                  (scrb_axi_ddrb.rresp        ),
    .rlast                  (scrb_axi_ddrb.rlast        ),
    .ruser                  (18'h0                      ),
    .rvalid                 (scrb_axi_ddrb.rvalid       ),
    .rready                 (scrb_axi_ddrb.rready       )
  );

  assign scrb_axi_ddrb.wid[15:9] = 'b0;
  assign scrb_axi_ddrb.awburst   = `DEF_AXBURST;
  assign scrb_axi_ddrb.arburst   = `DEF_AXBURST;

endmodule
