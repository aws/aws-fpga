// =============================================================================
// Amazon FPGA Hardware Development Kit
//
// Copyright 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
// =============================================================================


// CL CLK GEN

`include "cl_clk_gen_defines.vh"

module cl_clk_gen
(
  `include "cl_ports.vh"
);

`include "cl_id_defines.vh"
`include "unused_flr_template.inc"
`include "unused_ddr_template.inc"
`include "unused_apppf_irq_template.inc"
`include "unused_dma_pcis_template.inc"
`include "unused_pcim_template.inc"

  assign cl_sh_id0 = `CL_SH_ID0;
  assign cl_sh_id1 = `CL_SH_ID1;

//----------------------------
// Clock Generation
//----------------------------

  logic gen_clk_extra_a1, gen_clk_extra_a2, gen_clk_extra_a3;
  logic gen_clk_extra_b0, gen_clk_extra_b1;
  logic gen_clk_extra_c0, gen_clk_extra_c1;
  logic gen_clk_hbm_axi, gen_clk_hbm_ref, gen_clk_main_a0;
  logic gen_rst_main_n, gen_rst_a1_n, gen_rst_a2_n, gen_rst_a3_n;
  logic gen_rst_b0_n, gen_rst_b1_n, gen_rst_c0_n, gen_rst_c1_n;
  logic gen_rst_hbm_axi_n, gen_rst_hbm_ref_n;

aws_clk_gen #(
  .CLK_GRP_A_EN (1), // Only Clock Group A enabled
  .CLK_GRP_B_EN (0),
  .CLK_GRP_C_EN (0),
  .CLK_HBM_EN   (0)
) AWS_CLK_GEN (
  .i_clk_main_a0       (clk_main_a0     ),
  .i_rst_main_n        (rst_main_n      ),
  .i_clk_hbm_ref       (clk_hbm_ref     ),
  .s_axil_ctrl_awaddr  (sda_cl_awaddr   ),
  .s_axil_ctrl_awvalid (sda_cl_awvalid  ),
  .s_axil_ctrl_awready (cl_sda_awready  ),
  .s_axil_ctrl_wdata   (sda_cl_wdata    ),
  .s_axil_ctrl_wstrb   (sda_cl_wstrb    ),
  .s_axil_ctrl_wvalid  (sda_cl_wvalid   ),
  .s_axil_ctrl_wready  (cl_sda_wready   ),
  .s_axil_ctrl_bresp   (cl_sda_bresp    ),
  .s_axil_ctrl_bvalid  (cl_sda_bvalid   ),
  .s_axil_ctrl_bready  (sda_cl_bready   ),
  .s_axil_ctrl_araddr  (sda_cl_araddr   ),
  .s_axil_ctrl_arvalid (sda_cl_arvalid  ),
  .s_axil_ctrl_arready (cl_sda_arready  ),
  .s_axil_ctrl_rdata   (cl_sda_rdata    ),
  .s_axil_ctrl_rresp   (cl_sda_rresp    ),
  .s_axil_ctrl_rvalid  (cl_sda_rvalid   ),
  .s_axil_ctrl_rready  (sda_cl_rready   ),
  .o_clk_hbm_ref       (gen_clk_hbm_ref ),
  .o_clk_main_a0       (gen_clk_main_a0 ),
  .o_clk_extra_a1      (gen_clk_extra_a1),
  .o_clk_extra_a2      (gen_clk_extra_a2),
  .o_clk_extra_a3      (gen_clk_extra_a3),
  .o_clk_extra_b0      (gen_clk_extra_b0),
  .o_clk_extra_b1      (gen_clk_extra_b1),
  .o_clk_extra_c0      (gen_clk_extra_c0),
  .o_clk_extra_c1      (gen_clk_extra_c1),
  .o_clk_hbm_axi       (gen_clk_hbm_axi),
  .o_cl_rst_main_n     (gen_rst_main_n  ),
  .o_cl_rst_a1_n       (gen_rst_a1_n    ),
  .o_cl_rst_a2_n       (gen_rst_a2_n    ),
  .o_cl_rst_a3_n       (gen_rst_a3_n    ),
  .o_cl_rst_b0_n       (gen_rst_b0_n    ),
  .o_cl_rst_b1_n       (gen_rst_b1_n    ),
  .o_cl_rst_c0_n       (gen_rst_c0_n    ),
  .o_cl_rst_c1_n       (gen_rst_c1_n    ),
  .o_cl_rst_hbm_axi_n (gen_rst_hbm_axi_n),
  .o_cl_rst_hbm_ref_n (gen_rst_hbm_ref_n)
);

//----------------------------
// OCL Clock Domain Crossing
//----------------------------

  // Stable reset synchronized to clk_extra_a1
  logic cc_rst_n;

  xpm_cdc_async_rst #(
    .DEST_SYNC_FF    (4),
    .INIT_SYNC_FF    (0),
    .RST_ACTIVE_HIGH (0)
  ) CDC_ASYNC_RST_CC (
    .src_arst  (rst_main_n),
    .dest_clk  (gen_clk_extra_a1),
    .dest_arst (cc_rst_n)
  );

  // Clock converter to register slice wires
  logic [31:0] cc_awaddr, cc_wdata, cc_araddr, cc_rdata;
  logic [3:0]  cc_wstrb;
  logic [1:0]  cc_bresp, cc_rresp;
  logic        cc_awvalid, cc_awready;
  logic        cc_wvalid,  cc_wready;
  logic        cc_bvalid,  cc_bready;
  logic        cc_arvalid, cc_arready;
  logic        cc_rvalid,  cc_rready;

  // Register slice to adder wires
  logic [31:0] adder_awaddr, adder_wdata, adder_araddr, adder_rdata;
  logic [3:0]  adder_wstrb;
  logic [1:0]  adder_bresp, adder_rresp;
  logic        adder_awvalid, adder_awready;
  logic        adder_wvalid,  adder_wready;
  logic        adder_bvalid,  adder_bready;
  logic        adder_arvalid, adder_arready;
  logic        adder_rvalid,  adder_rready;

// AXI-Lite clock converter: clk_main_a0 --> clk_extra_a1
cl_axi_clock_converter_light AXIL_CLK_CONV (
  .s_axi_aclk    (clk_main_a0),
  .s_axi_aresetn (rst_main_n),
  .s_axi_awaddr  (ocl_cl_awaddr),
  .s_axi_awprot  (3'd0),
  .s_axi_awvalid (ocl_cl_awvalid),
  .s_axi_awready (cl_ocl_awready),
  .s_axi_wdata   (ocl_cl_wdata),
  .s_axi_wstrb   (ocl_cl_wstrb),
  .s_axi_wvalid  (ocl_cl_wvalid),
  .s_axi_wready  (cl_ocl_wready),
  .s_axi_bresp   (cl_ocl_bresp),
  .s_axi_bvalid  (cl_ocl_bvalid),
  .s_axi_bready  (ocl_cl_bready),
  .s_axi_araddr  (ocl_cl_araddr),
  .s_axi_arprot  (3'd0),
  .s_axi_arvalid (ocl_cl_arvalid),
  .s_axi_arready (cl_ocl_arready),
  .s_axi_rdata   (cl_ocl_rdata),
  .s_axi_rresp   (cl_ocl_rresp),
  .s_axi_rvalid  (cl_ocl_rvalid),
  .s_axi_rready  (ocl_cl_rready),
  .m_axi_aclk    (gen_clk_extra_a1),
  .m_axi_aresetn (cc_rst_n),
  .m_axi_awaddr  (cc_awaddr),
  .m_axi_awprot  (),
  .m_axi_awvalid (cc_awvalid),
  .m_axi_awready (cc_awready),
  .m_axi_wdata   (cc_wdata),
  .m_axi_wstrb   (cc_wstrb),
  .m_axi_wvalid  (cc_wvalid),
  .m_axi_wready  (cc_wready),
  .m_axi_bresp   (cc_bresp),
  .m_axi_bvalid  (cc_bvalid),
  .m_axi_bready  (cc_bready),
  .m_axi_araddr  (cc_araddr),
  .m_axi_arprot  (),
  .m_axi_arvalid (cc_arvalid),
  .m_axi_arready (cc_arready),
  .m_axi_rdata   (cc_rdata),
  .m_axi_rresp   (cc_rresp),
  .m_axi_rvalid  (cc_rvalid),
  .m_axi_rready  (cc_rready)
);

// Register slice in clk_extra_a1 domain
axi_register_slice_light AXIL_REG_SLC (
  .aclk          (gen_clk_extra_a1),
  .aresetn       (gen_rst_a1_n),
  .s_axi_awaddr  (cc_awaddr),
  .s_axi_awprot  (3'h0),
  .s_axi_awvalid (cc_awvalid),
  .s_axi_awready (cc_awready),
  .s_axi_wdata   (cc_wdata),
  .s_axi_wstrb   (cc_wstrb),
  .s_axi_wvalid  (cc_wvalid),
  .s_axi_wready  (cc_wready),
  .s_axi_bresp   (cc_bresp),
  .s_axi_bvalid  (cc_bvalid),
  .s_axi_bready  (cc_bready),
  .s_axi_araddr  (cc_araddr),
  .s_axi_arprot  (3'h0),
  .s_axi_arvalid (cc_arvalid),
  .s_axi_arready (cc_arready),
  .s_axi_rdata   (cc_rdata),
  .s_axi_rresp   (cc_rresp),
  .s_axi_rvalid  (cc_rvalid),
  .s_axi_rready  (cc_rready),
  .m_axi_awaddr  (adder_awaddr),
  .m_axi_awprot  (),
  .m_axi_awvalid (adder_awvalid),
  .m_axi_awready (adder_awready),
  .m_axi_wdata   (adder_wdata),
  .m_axi_wstrb   (adder_wstrb),
  .m_axi_wvalid  (adder_wvalid),
  .m_axi_wready  (adder_wready),
  .m_axi_bresp   (adder_bresp),
  .m_axi_bvalid  (adder_bvalid),
  .m_axi_bready  (adder_bready),
  .m_axi_araddr  (adder_araddr),
  .m_axi_arvalid (adder_arvalid),
  .m_axi_arready (adder_arready),
  .m_axi_rdata   (adder_rdata),
  .m_axi_rresp   (adder_rresp),
  .m_axi_rvalid  (adder_rvalid),
  .m_axi_rready  (adder_rready)
);

//----------------------------
// Application Logic
//----------------------------

cl_axil_adder ADDER_I (
  .clk             (gen_clk_extra_a1),
  .rst_n           (gen_rst_a1_n),
  .s_axil_awaddr   (adder_awaddr),
  .s_axil_awvalid  (adder_awvalid),
  .s_axil_awready  (adder_awready),
  .s_axil_wdata    (adder_wdata),
  .s_axil_wstrb    (adder_wstrb),
  .s_axil_wvalid   (adder_wvalid),
  .s_axil_wready   (adder_wready),
  .s_axil_bresp    (adder_bresp),
  .s_axil_bvalid   (adder_bvalid),
  .s_axil_bready   (adder_bready),
  .s_axil_araddr   (adder_araddr),
  .s_axil_arvalid  (adder_arvalid),
  .s_axil_arready  (adder_arready),
  .s_axil_rdata    (adder_rdata),
  .s_axil_rresp    (adder_rresp),
  .s_axil_rvalid   (adder_rvalid),
  .s_axil_rready   (adder_rready)
);

//-------------------------------------
// Debug Bridge
//-------------------------------------

`ifndef SIMULATION
cl_debug_bridge CL_DEBUG_BRIDGE (
  .clk                (clk_main_a0),
  .S_BSCAN_drck       (drck),
  .S_BSCAN_shift      (shift),
  .S_BSCAN_tdi        (tdi),
  .S_BSCAN_update     (update),
  .S_BSCAN_sel        (sel),
  .S_BSCAN_tdo        (tdo),
  .S_BSCAN_tms        (tms),
  .S_BSCAN_tck        (tck),
  .S_BSCAN_runtest    (runtest),
  .S_BSCAN_reset      (reset),
  .S_BSCAN_capture    (capture),
  .S_BSCAN_bscanid_en (bscanid_en)
);
`endif

endmodule
