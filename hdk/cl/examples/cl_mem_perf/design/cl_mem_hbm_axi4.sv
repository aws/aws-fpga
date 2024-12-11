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

//=============================================================================
// CL_MEM_HBM_AXI4
// --------------
// - Convert 512b 250MHz AXI4 to 450MHz AXI3 bus to feed into HBM
// - Instantiate CL_HBM_PERF_KERNEL for high performance traffic into HBM
// - Instantiate HBM Wrapper
//=============================================================================

module cl_mem_hbm_axi4
#(
  parameter             HBM_PRESENT = 1
)
(
  input logic           clk_hbm_ref,
  input logic           clk_hbm_axi,
  input logic           hbm_axi_rst_n,
  input logic           clk,
  input logic           rst_n,

  axi_bus_t.master      hbm_axi4_bus,         // AXI4 data bus to HBM
  cfg_bus_t.slave       hbm_stat_bus,         // CFG Stats bus to HBM
  cfg_bus_t.slave       hbm_kern_cfg_bus,     // CFG bus to cl_hbm_perf_kerne

  input  logic          i_hbm_apb_preset_n_1, // HBM APB interface to the shell
  output logic [21:0]   o_hbm_apb_paddr_1,
  output logic  [2:0]   o_hbm_apb_pprot_1,
  output logic          o_hbm_apb_psel_1,
  output logic          o_hbm_apb_penable_1,
  output logic          o_hbm_apb_pwrite_1,
  output logic [31:0]   o_hbm_apb_pwdata_1,
  output logic  [3:0]   o_hbm_apb_pstrb_1,
  output logic          o_hbm_apb_pready_1,
  output logic [31:0]   o_hbm_apb_prdata_1,
  output logic          o_hbm_apb_pslverr_1,

  input  logic          i_hbm_apb_preset_n_0,
  output logic [21:0]   o_hbm_apb_paddr_0,
  output logic  [2:0]   o_hbm_apb_pprot_0,
  output logic          o_hbm_apb_psel_0,
  output logic          o_hbm_apb_penable_0,
  output logic          o_hbm_apb_pwrite_0,
  output logic [31:0]   o_hbm_apb_pwdata_0,
  output logic  [3:0]   o_hbm_apb_pstrb_0,
  output logic          o_hbm_apb_pready_0,
  output logic [31:0]   o_hbm_apb_prdata_0,
  output logic          o_hbm_apb_pslverr_0,

  output logic [7:0]    o_cl_sh_hbm_stat_int, // output [7:0] No interrupts from HBM
  output logic          o_hbm_ready           // output HBM Init Ready
);

  //----------------------------------
  // HBM
  //----------------------------------
  localparam NUM_OF_HBM_PORTS = 32;
  localparam AXLEN_WIDTH      = 4;

  // HBM channel number that the PCIS is MUX'ed with
  localparam MAP_PORT = 15;

  // 256bit AXI3 bus
  axi_bus_t #(.DATA_WIDTH(256), .ADDR_WIDTH(34), .ID_WIDTH(6), .LEN_WIDTH(AXLEN_WIDTH)) axi3_256b_bus();
  axi_bus_t #(.DATA_WIDTH(256), .ADDR_WIDTH(34), .ID_WIDTH(6), .LEN_WIDTH(AXLEN_WIDTH)) axi3_256b_bus_q();
  axi_bus_t #(.DATA_WIDTH(256), .ADDR_WIDTH(34), .ID_WIDTH(6), .LEN_WIDTH(AXLEN_WIDTH)) axi3_256b_hbm_mux();
  axi_bus_t #(.DATA_WIDTH(256), .ADDR_WIDTH(34), .ID_WIDTH(6), .LEN_WIDTH(AXLEN_WIDTH)) axi3_256b_hbm_mux_q();

  logic  [33:0]           hbm_araddr        [0:(NUM_OF_HBM_PORTS-1)];
  logic   [1:0]           hbm_arburst       [0:(NUM_OF_HBM_PORTS-1)];
  logic   [5:0]           hbm_arid          [0:(NUM_OF_HBM_PORTS-1)];
  logic [AXLEN_WIDTH-1:0] hbm_arlen         [0:(NUM_OF_HBM_PORTS-1)];
  logic   [2:0]           hbm_arsize        [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_arvalid       [0:(NUM_OF_HBM_PORTS-1)];
  logic  [33:0]           hbm_awaddr        [0:(NUM_OF_HBM_PORTS-1)];
  logic   [1:0]           hbm_awburst       [0:(NUM_OF_HBM_PORTS-1)];
  logic   [5:0]           hbm_awid          [0:(NUM_OF_HBM_PORTS-1)];
  logic [AXLEN_WIDTH-1:0] hbm_awlen         [0:(NUM_OF_HBM_PORTS-1)];
  logic   [2:0]           hbm_awsize        [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_awvalid       [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_rready        [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_bready        [0:(NUM_OF_HBM_PORTS-1)];
  logic [255:0]           hbm_wdata         [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_wlast         [0:(NUM_OF_HBM_PORTS-1)];
  logic  [31:0]           hbm_wstrb         [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_wvalid        [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_arready       [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_awready       [0:(NUM_OF_HBM_PORTS-1)];
  logic [255:0]           hbm_rdata         [0:(NUM_OF_HBM_PORTS-1)];
  logic   [5:0]           hbm_rid           [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_rlast         [0:(NUM_OF_HBM_PORTS-1)];
  logic   [1:0]           hbm_rresp         [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_rvalid        [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_wready        [0:(NUM_OF_HBM_PORTS-1)];
  logic   [5:0]           hbm_bid           [0:(NUM_OF_HBM_PORTS-1)];
  logic   [1:0]           hbm_bresp         [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_bvalid        [0:(NUM_OF_HBM_PORTS-1)];

  logic  [33:0]           hbm_kern_araddr   [0:(NUM_OF_HBM_PORTS-1)];
  logic   [1:0]           hbm_kern_arburst  [0:(NUM_OF_HBM_PORTS-1)];
  logic   [5:0]           hbm_kern_arid     [0:(NUM_OF_HBM_PORTS-1)];
  logic [AXLEN_WIDTH-1:0] hbm_kern_arlen    [0:(NUM_OF_HBM_PORTS-1)];
  logic   [2:0]           hbm_kern_arsize   [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_kern_arvalid  [0:(NUM_OF_HBM_PORTS-1)];
  logic  [33:0]           hbm_kern_awaddr   [0:(NUM_OF_HBM_PORTS-1)];
  logic   [1:0]           hbm_kern_awburst  [0:(NUM_OF_HBM_PORTS-1)];
  logic   [5:0]           hbm_kern_awid     [0:(NUM_OF_HBM_PORTS-1)];
  logic [AXLEN_WIDTH-1:0] hbm_kern_awlen    [0:(NUM_OF_HBM_PORTS-1)];
  logic   [2:0]           hbm_kern_awsize   [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_kern_awvalid  [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_kern_rready   [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_kern_bready   [0:(NUM_OF_HBM_PORTS-1)];
  logic [255:0]           hbm_kern_wdata    [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_kern_wlast    [0:(NUM_OF_HBM_PORTS-1)];
  logic  [31:0]           hbm_kern_wstrb    [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_kern_wvalid   [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_kern_arready  [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_kern_awready  [0:(NUM_OF_HBM_PORTS-1)];
  logic [255:0]           hbm_kern_rdata    [0:(NUM_OF_HBM_PORTS-1)];
  logic   [5:0]           hbm_kern_rid      [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_kern_rlast    [0:(NUM_OF_HBM_PORTS-1)];
  logic   [1:0]           hbm_kern_rresp    [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_kern_rvalid   [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_kern_wready   [0:(NUM_OF_HBM_PORTS-1)];
  logic   [5:0]           hbm_kern_bid      [0:(NUM_OF_HBM_PORTS-1)];
  logic   [1:0]           hbm_kern_bresp    [0:(NUM_OF_HBM_PORTS-1)];
  logic                   hbm_kern_bvalid   [0:(NUM_OF_HBM_PORTS-1)];

  genvar ii;

  generate

  if (HBM_PRESENT) begin : HBM_PRESENT_EQ_1

    logic [29:0] dummy_araddr;
    logic [29:0] dummy_awaddr;

    cl_axi_sc_1x1_wrapper AXI_CONVERTER_AXI4_AXI3
    (
      .aclk_250               (clk                            ),
      .aresetn_250            (rst_n                          ),
      .aclk_450               (clk_hbm_axi                    ),

      .AXI4_araddr            (hbm_axi4_bus.araddr            ),
      .AXI4_arburst           (hbm_axi4_bus.arburst           ),
      .AXI4_arcache           (`DEF_AXCACHE                   ),
      .AXI4_arid              (hbm_axi4_bus.arid              ),
      .AXI4_arlen             (hbm_axi4_bus.arlen             ),
      .AXI4_arlock            (`DEF_AXLOCK                    ),
      .AXI4_arprot            (`DEF_AXPROT                    ),
      .AXI4_arqos             (`DEF_AXQOS                     ),
      .AXI4_arready           (hbm_axi4_bus.arready           ),
      .AXI4_arsize            (hbm_axi4_bus.arsize            ),
      .AXI4_arvalid           (hbm_axi4_bus.arvalid           ),
      .AXI4_awaddr            (hbm_axi4_bus.awaddr            ),
      .AXI4_awburst           (hbm_axi4_bus.awburst           ),
      .AXI4_awcache           (`DEF_AXCACHE                   ),
      .AXI4_awid              (hbm_axi4_bus.awid              ),
      .AXI4_awlen             (hbm_axi4_bus.awlen             ),
      .AXI4_awlock            (`DEF_AXLOCK                    ),
      .AXI4_awprot            (`DEF_AXPROT                    ),
      .AXI4_awqos             (`DEF_AXQOS                     ),
      .AXI4_awready           (hbm_axi4_bus.awready           ),
      .AXI4_awsize            (hbm_axi4_bus.awsize            ),
      .AXI4_awvalid           (hbm_axi4_bus.awvalid           ),
      .AXI4_bid               (hbm_axi4_bus.bid               ),
      .AXI4_bready            (hbm_axi4_bus.bready            ),
      .AXI4_bresp             (hbm_axi4_bus.bresp             ),
      .AXI4_bvalid            (hbm_axi4_bus.bvalid            ),
      .AXI4_rdata             (hbm_axi4_bus.rdata             ),
      .AXI4_rid               (hbm_axi4_bus.rid               ),
      .AXI4_rlast             (hbm_axi4_bus.rlast             ),
      .AXI4_rready            (hbm_axi4_bus.rready            ),
      .AXI4_rresp             (hbm_axi4_bus.rresp             ),
      .AXI4_rvalid            (hbm_axi4_bus.rvalid            ),
      .AXI4_wdata             (hbm_axi4_bus.wdata             ),
      .AXI4_wlast             (hbm_axi4_bus.wlast             ),
      .AXI4_wready            (hbm_axi4_bus.wready            ),
      .AXI4_wstrb             (hbm_axi4_bus.wstrb             ),
      .AXI4_wvalid            (hbm_axi4_bus.wvalid            ),

      .AXI3_araddr            ({dummy_araddr, axi3_256b_bus.araddr}),
      .AXI3_arburst           (axi3_256b_bus.arburst          ),
      .AXI3_arcache           (                               ),
      .AXI3_arlen             (axi3_256b_bus.arlen            ),
      .AXI3_arlock            (                               ),
      .AXI3_arprot            (                               ),
      .AXI3_arqos             (                               ),
      .AXI3_arready           (axi3_256b_bus.arready          ),
      .AXI3_arsize            (axi3_256b_bus.arsize           ),
      .AXI3_arvalid           (axi3_256b_bus.arvalid          ),
      .AXI3_awaddr            ({dummy_awaddr, axi3_256b_bus.awaddr}),
      .AXI3_awburst           (axi3_256b_bus.awburst          ),
      .AXI3_awcache           (                               ),
      .AXI3_awlen             (axi3_256b_bus.awlen            ),
      .AXI3_awlock            (                               ),
      .AXI3_awprot            (                               ),
      .AXI3_awqos             (                               ),
      .AXI3_awready           (axi3_256b_bus.awready          ),
      .AXI3_awsize            (axi3_256b_bus.awsize           ),
      .AXI3_awvalid           (axi3_256b_bus.awvalid          ),
      .AXI3_bready            (axi3_256b_bus.bready           ),
      .AXI3_bresp             (axi3_256b_bus.bresp            ),
      .AXI3_bvalid            (axi3_256b_bus.bvalid           ),
      .AXI3_rdata             (axi3_256b_bus.rdata            ),
      .AXI3_rlast             (axi3_256b_bus.rlast            ),
      .AXI3_rready            (axi3_256b_bus.rready           ),
      .AXI3_rresp             (axi3_256b_bus.rresp            ),
      .AXI3_rvalid            (axi3_256b_bus.rvalid           ),
      .AXI3_wdata             (axi3_256b_bus.wdata            ),
      .AXI3_wlast             (axi3_256b_bus.wlast            ),
      .AXI3_wready            (axi3_256b_bus.wready           ),
      .AXI3_wstrb             (axi3_256b_bus.wstrb            ),
      .AXI3_wvalid            (axi3_256b_bus.wvalid           )
    );

    assign axi3_256b_bus.awid = 'b0;
    assign axi3_256b_bus.wid  = 'b0;
    assign axi3_256b_bus.arid = 'b0;

    // Instantiate HBM Kernel Core (can fully extract performance from HBM Core)
    // NOTE: HBM access is exclusive to CL_HBM_PERF_KERNEL when the block is enabled.
    //       axi3_256b_bus can only access HBM when this block is disabled.
    logic hbm_kern_enable;

    cl_hbm_perf_kernel
    #(
      .NUM_OT                 (64                             ),
      .NUM_CHANNELS           (NUM_OF_HBM_PORTS               ),
      .AXLEN_WIDTH            (AXLEN_WIDTH                    )
    )
    CL_HBM_PERF_KERNEL
    (
      .clk_main_a0            (clk                            ),
      .rst_main_a0            (rst_n                          ),
      .clk_hbm                (clk_hbm_axi                    ),
      .rst_hbm_n              (hbm_axi_rst_n                  ),

      .i_cfg_addr             (hbm_kern_cfg_bus.addr          ),
      .i_cfg_wdata            (hbm_kern_cfg_bus.wdata         ),
      .i_cfg_wr               (hbm_kern_cfg_bus.wr            ),
      .i_cfg_rd               (hbm_kern_cfg_bus.rd            ),
      .o_cfg_rdata            (hbm_kern_cfg_bus.rdata         ),
      .o_cfg_ack              (hbm_kern_cfg_bus.ack           ),

      .o_kernel_enable        (hbm_kern_enable                ),
      .o_axi_araddr           (hbm_kern_araddr                ),
      .o_axi_arburst          (hbm_kern_arburst               ),
      .o_axi_arid             (hbm_kern_arid                  ),
      .o_axi_arlen            (hbm_kern_arlen                 ),
      .o_axi_arsize           (hbm_kern_arsize                ),
      .o_axi_arvalid          (hbm_kern_arvalid               ),
      .o_axi_awaddr           (hbm_kern_awaddr                ),
      .o_axi_awburst          (hbm_kern_awburst               ),
      .o_axi_awid             (hbm_kern_awid                  ),
      .o_axi_awlen            (hbm_kern_awlen                 ),
      .o_axi_awsize           (hbm_kern_awsize                ),
      .o_axi_awvalid          (hbm_kern_awvalid               ),
      .o_axi_rready           (hbm_kern_rready                ),
      .o_axi_bready           (hbm_kern_bready                ),
      .o_axi_wdata            (hbm_kern_wdata                 ),
      .o_axi_wlast            (hbm_kern_wlast                 ),
      .o_axi_wstrb            (hbm_kern_wstrb                 ),
      .o_axi_wvalid           (hbm_kern_wvalid                ),
      .i_axi_arready          (hbm_kern_arready               ),
      .i_axi_awready          (hbm_kern_awready               ),
      .i_axi_rdata            (hbm_kern_rdata                 ),
      .i_axi_rid              (hbm_kern_rid                   ),
      .i_axi_rlast            (hbm_kern_rlast                 ),
      .i_axi_rresp            (hbm_kern_rresp                 ),
      .i_axi_rvalid           (hbm_kern_rvalid                ),
      .i_axi_wready           (hbm_kern_wready                ),
      .i_axi_bid              (hbm_kern_bid                   ),
      .i_axi_bresp            (hbm_kern_bresp                 ),
      .i_axi_bvalid           (hbm_kern_bvalid                )
    );

    // convert from interface to ports
    // MUX access to HBM Channel#0 between CL_HBM_PERF_KERNEL and AXI_CONVERTER_AXI4_AXI3
    always_comb begin
      axi3_256b_hbm_mux.awaddr      = hbm_kern_enable ? hbm_kern_awaddr[MAP_PORT]  : axi3_256b_bus.awaddr;
      axi3_256b_hbm_mux.awburst     = hbm_kern_enable ? hbm_kern_awburst[MAP_PORT] : axi3_256b_bus.awburst;
      axi3_256b_hbm_mux.awid        = hbm_kern_enable ? hbm_kern_awid[MAP_PORT]    : axi3_256b_bus.awid;
      axi3_256b_hbm_mux.awlen       = hbm_kern_enable ? hbm_kern_awlen[MAP_PORT]   : axi3_256b_bus.awlen;
      axi3_256b_hbm_mux.awsize      = hbm_kern_enable ? hbm_kern_awsize[MAP_PORT]  : axi3_256b_bus.awsize;
      axi3_256b_hbm_mux.awvalid     = hbm_kern_enable ? hbm_kern_awvalid[MAP_PORT] : axi3_256b_bus.awvalid;
      axi3_256b_bus.awready         = hbm_kern_enable ? 1'b0                       : axi3_256b_hbm_mux.awready;
      hbm_kern_awready[MAP_PORT]    = hbm_kern_enable ? axi3_256b_hbm_mux.awready  : 1'b0;

      axi3_256b_hbm_mux.wdata       = hbm_kern_enable ? hbm_kern_wdata[MAP_PORT]   : axi3_256b_bus.wdata;
      axi3_256b_hbm_mux.wlast       = hbm_kern_enable ? hbm_kern_wlast[MAP_PORT]   : axi3_256b_bus.wlast;
      axi3_256b_hbm_mux.wstrb       = hbm_kern_enable ? hbm_kern_wstrb[MAP_PORT]   : axi3_256b_bus.wstrb;
      axi3_256b_hbm_mux.wvalid      = hbm_kern_enable ? hbm_kern_wvalid[MAP_PORT]  : axi3_256b_bus.wvalid;
      axi3_256b_bus.wready          = hbm_kern_enable ? 1'b0                       : axi3_256b_hbm_mux.wready;
      hbm_kern_wready[MAP_PORT]     = hbm_kern_enable ? axi3_256b_hbm_mux.wready   : 1'b0;

      axi3_256b_bus.bid             = hbm_kern_enable ? 1'b0                       : axi3_256b_hbm_mux.bid;
      axi3_256b_bus.bresp           = hbm_kern_enable ? 1'b0                       : axi3_256b_hbm_mux.bresp;
      axi3_256b_bus.bvalid          = hbm_kern_enable ? 1'b0                       : axi3_256b_hbm_mux.bvalid;
      hbm_kern_bid[MAP_PORT]        = hbm_kern_enable ? axi3_256b_hbm_mux.bid      : 1'b0;
      hbm_kern_bresp[MAP_PORT]      = hbm_kern_enable ? axi3_256b_hbm_mux.bresp    : 1'b0;
      hbm_kern_bvalid[MAP_PORT]     = hbm_kern_enable ? axi3_256b_hbm_mux.bvalid   : 1'b0;
      axi3_256b_hbm_mux.bready      = hbm_kern_enable ? hbm_kern_bready[MAP_PORT]  : axi3_256b_bus.bready;

      axi3_256b_hbm_mux.araddr      = hbm_kern_enable ? hbm_kern_araddr[MAP_PORT]  : axi3_256b_bus.araddr;
      axi3_256b_hbm_mux.arburst     = hbm_kern_enable ? hbm_kern_arburst[MAP_PORT] : axi3_256b_bus.arburst;
      axi3_256b_hbm_mux.arid        = hbm_kern_enable ? hbm_kern_arid[MAP_PORT]    : axi3_256b_bus.arid;
      axi3_256b_hbm_mux.arlen       = hbm_kern_enable ? hbm_kern_arlen[MAP_PORT]   : axi3_256b_bus.arlen;
      axi3_256b_hbm_mux.arsize      = hbm_kern_enable ? hbm_kern_arsize[MAP_PORT]  : axi3_256b_bus.arsize;
      axi3_256b_hbm_mux.arvalid     = hbm_kern_enable ? hbm_kern_arvalid[MAP_PORT] : axi3_256b_bus.arvalid;
      axi3_256b_bus.arready         = hbm_kern_enable ? 1'b0                       : axi3_256b_hbm_mux.arready;
      axi3_256b_hbm_mux.rready      = hbm_kern_enable ? hbm_kern_rready[MAP_PORT]  : axi3_256b_bus.rready;
      hbm_kern_arready[MAP_PORT]    = hbm_kern_enable ? axi3_256b_hbm_mux.arready  : 1'b0;

      axi3_256b_bus.rdata           = hbm_kern_enable ? 1'b0                       : axi3_256b_hbm_mux.rdata;
      axi3_256b_bus.rid             = hbm_kern_enable ? 1'b0                       : axi3_256b_hbm_mux.rid;
      axi3_256b_bus.rlast           = hbm_kern_enable ? 1'b0                       : axi3_256b_hbm_mux.rlast;
      axi3_256b_bus.rresp           = hbm_kern_enable ? 1'b0                       : axi3_256b_hbm_mux.rresp;
      axi3_256b_bus.rvalid          = hbm_kern_enable ? 1'b0                       : axi3_256b_hbm_mux.rvalid;
      hbm_kern_rdata[MAP_PORT]      = hbm_kern_enable ? axi3_256b_hbm_mux.rdata    : 1'b0;
      hbm_kern_rid[MAP_PORT]        = hbm_kern_enable ? axi3_256b_hbm_mux.rid      : 1'b0;
      hbm_kern_rlast[MAP_PORT]      = hbm_kern_enable ? axi3_256b_hbm_mux.rlast    : 1'b0;
      hbm_kern_rresp[MAP_PORT]      = hbm_kern_enable ? axi3_256b_hbm_mux.rresp    : 1'b0;
      hbm_kern_rvalid[MAP_PORT]     = hbm_kern_enable ? axi3_256b_hbm_mux.rvalid   : 1'b0;
    end

  // AXI3 Slice for the mux signals
  cl_axi3_256b_reg_slice AXI3_REG_SLC_HBM_1
  (
    .aclk                     (clk_hbm_axi                    ),
    .aresetn                  (hbm_axi_rst_n                  ),

    .s_axi_awid               (axi3_256b_hbm_mux.awid         ),
    .s_axi_awaddr             (axi3_256b_hbm_mux.awaddr       ),
    .s_axi_awlen              (axi3_256b_hbm_mux.awlen        ),
    .s_axi_awsize             (axi3_256b_hbm_mux.awsize       ),
    .s_axi_awburst            (axi3_256b_hbm_mux.awburst      ),
    .s_axi_awlock             (`DEF_AXLOCK                    ),
    .s_axi_awcache            (`DEF_AXCACHE                   ),
    .s_axi_awprot             (`DEF_AXPROT                    ),
    .s_axi_awqos              (`DEF_AXQOS                     ),
    .s_axi_awvalid            (axi3_256b_hbm_mux.awvalid      ),
    .s_axi_awready            (axi3_256b_hbm_mux.awready      ),
    .s_axi_wid                (6'd0                           ),
    .s_axi_wdata              (axi3_256b_hbm_mux.wdata        ),
    .s_axi_wstrb              (axi3_256b_hbm_mux.wstrb        ),
    .s_axi_wlast              (axi3_256b_hbm_mux.wlast        ),
    .s_axi_wvalid             (axi3_256b_hbm_mux.wvalid       ),
    .s_axi_wready             (axi3_256b_hbm_mux.wready       ),
    .s_axi_bid                (axi3_256b_hbm_mux.bid          ),
    .s_axi_bresp              (axi3_256b_hbm_mux.bresp        ),
    .s_axi_bvalid             (axi3_256b_hbm_mux.bvalid       ),
    .s_axi_bready             (axi3_256b_hbm_mux.bready       ),
    .s_axi_arid               (axi3_256b_hbm_mux.arid         ),
    .s_axi_araddr             (axi3_256b_hbm_mux.araddr       ),
    .s_axi_arlen              (axi3_256b_hbm_mux.arlen        ),
    .s_axi_arsize             (axi3_256b_hbm_mux.arsize       ),
    .s_axi_arburst            (axi3_256b_hbm_mux.arburst      ),
    .s_axi_arlock             (`DEF_AXLOCK                    ),
    .s_axi_arcache            (`DEF_AXCACHE                   ),
    .s_axi_arprot             (`DEF_AXPROT                    ),
    .s_axi_arqos              (`DEF_AXQOS                     ),
    .s_axi_arvalid            (axi3_256b_hbm_mux.arvalid      ),
    .s_axi_arready            (axi3_256b_hbm_mux.arready      ),
    .s_axi_rid                (axi3_256b_hbm_mux.rid          ),
    .s_axi_rdata              (axi3_256b_hbm_mux.rdata        ),
    .s_axi_rresp              (axi3_256b_hbm_mux.rresp        ),
    .s_axi_rlast              (axi3_256b_hbm_mux.rlast        ),
    .s_axi_rvalid             (axi3_256b_hbm_mux.rvalid       ),
    .s_axi_rready             (axi3_256b_hbm_mux.rready       ),

    .m_axi_awid               (axi3_256b_hbm_mux_q.awid       ),
    .m_axi_awaddr             (axi3_256b_hbm_mux_q.awaddr     ),
    .m_axi_awlen              (axi3_256b_hbm_mux_q.awlen      ),
    .m_axi_awsize             (axi3_256b_hbm_mux_q.awsize     ),
    .m_axi_awburst            (axi3_256b_hbm_mux_q.awburst    ),
    .m_axi_awlock             (                               ),
    .m_axi_awcache            (                               ),
    .m_axi_awprot             (                               ),
    .m_axi_awqos              (                               ),
    .m_axi_awvalid            (axi3_256b_hbm_mux_q.awvalid    ),
    .m_axi_awready            (axi3_256b_hbm_mux_q.awready    ),
    .m_axi_wid                (axi3_256b_hbm_mux_q.wid        ),
    .m_axi_wdata              (axi3_256b_hbm_mux_q.wdata      ),
    .m_axi_wstrb              (axi3_256b_hbm_mux_q.wstrb      ),
    .m_axi_wlast              (axi3_256b_hbm_mux_q.wlast      ),
    .m_axi_wvalid             (axi3_256b_hbm_mux_q.wvalid     ),
    .m_axi_wready             (axi3_256b_hbm_mux_q.wready     ),
    .m_axi_bid                (axi3_256b_hbm_mux_q.bid        ),
    .m_axi_bresp              (axi3_256b_hbm_mux_q.bresp      ),
    .m_axi_bvalid             (axi3_256b_hbm_mux_q.bvalid     ),
    .m_axi_bready             (axi3_256b_hbm_mux_q.bready     ),
    .m_axi_arid               (axi3_256b_hbm_mux_q.arid       ),
    .m_axi_araddr             (axi3_256b_hbm_mux_q.araddr     ),
    .m_axi_arlen              (axi3_256b_hbm_mux_q.arlen      ),
    .m_axi_arsize             (axi3_256b_hbm_mux_q.arsize     ),
    .m_axi_arburst            (axi3_256b_hbm_mux_q.arburst    ),
    .m_axi_arlock             (                               ),
    .m_axi_arcache            (                               ),
    .m_axi_arprot             (                               ),
    .m_axi_arqos              (                               ),
    .m_axi_arvalid            (axi3_256b_hbm_mux_q.arvalid    ),
    .m_axi_arready            (axi3_256b_hbm_mux_q.arready    ),
    .m_axi_rid                (axi3_256b_hbm_mux_q.rid        ),
    .m_axi_rdata              (axi3_256b_hbm_mux_q.rdata      ),
    .m_axi_rresp              (axi3_256b_hbm_mux_q.rresp      ),
    .m_axi_rlast              (axi3_256b_hbm_mux_q.rlast      ),
    .m_axi_rvalid             (axi3_256b_hbm_mux_q.rvalid     ),
    .m_axi_rready             (axi3_256b_hbm_mux_q.rready     )
  );

    // Another AXI3 Slice for timing
    cl_axi3_256b_reg_slice AXI3_REG_SLC_HBM_2
    (
      .aclk                   (clk_hbm_axi                    ),
      .aresetn                (hbm_axi_rst_n                  ),

      .s_axi_awid             (axi3_256b_hbm_mux_q.awid       ),
      .s_axi_awaddr           (axi3_256b_hbm_mux_q.awaddr     ),
      .s_axi_awlen            (axi3_256b_hbm_mux_q.awlen      ),
      .s_axi_awsize           (axi3_256b_hbm_mux_q.awsize     ),
      .s_axi_awburst          (axi3_256b_hbm_mux_q.awburst    ),
      .s_axi_awlock           (`DEF_AXLOCK                    ),
      .s_axi_awcache          (`DEF_AXCACHE                   ),
      .s_axi_awprot           (`DEF_AXPROT                    ),
      .s_axi_awqos            (`DEF_AXQOS                     ),
      .s_axi_awvalid          (axi3_256b_hbm_mux_q.awvalid    ),
      .s_axi_awready          (axi3_256b_hbm_mux_q.awready    ),
      .s_axi_wid              (axi3_256b_hbm_mux_q.wid        ),
      .s_axi_wdata            (axi3_256b_hbm_mux_q.wdata      ),
      .s_axi_wstrb            (axi3_256b_hbm_mux_q.wstrb      ),
      .s_axi_wlast            (axi3_256b_hbm_mux_q.wlast      ),
      .s_axi_wvalid           (axi3_256b_hbm_mux_q.wvalid     ),
      .s_axi_wready           (axi3_256b_hbm_mux_q.wready     ),
      .s_axi_bid              (axi3_256b_hbm_mux_q.bid        ),
      .s_axi_bresp            (axi3_256b_hbm_mux_q.bresp      ),
      .s_axi_bvalid           (axi3_256b_hbm_mux_q.bvalid     ),
      .s_axi_bready           (axi3_256b_hbm_mux_q.bready     ),
      .s_axi_arid             (axi3_256b_hbm_mux_q.arid       ),
      .s_axi_araddr           (axi3_256b_hbm_mux_q.araddr     ),
      .s_axi_arlen            (axi3_256b_hbm_mux_q.arlen      ),
      .s_axi_arsize           (axi3_256b_hbm_mux_q.arsize     ),
      .s_axi_arburst          (axi3_256b_hbm_mux_q.arburst    ),
      .s_axi_arlock           (`DEF_AXLOCK                    ),
      .s_axi_arcache          (`DEF_AXCACHE                   ),
      .s_axi_arprot           (`DEF_AXPROT                    ),
      .s_axi_arqos            (`DEF_AXQOS                     ),
      .s_axi_arvalid          (axi3_256b_hbm_mux_q.arvalid    ),
      .s_axi_arready          (axi3_256b_hbm_mux_q.arready    ),
      .s_axi_rid              (axi3_256b_hbm_mux_q.rid        ),
      .s_axi_rdata            (axi3_256b_hbm_mux_q.rdata      ),
      .s_axi_rresp            (axi3_256b_hbm_mux_q.rresp      ),
      .s_axi_rlast            (axi3_256b_hbm_mux_q.rlast      ),
      .s_axi_rvalid           (axi3_256b_hbm_mux_q.rvalid     ),
      .s_axi_rready           (axi3_256b_hbm_mux_q.rready     ),

      .m_axi_awid             (hbm_awid[MAP_PORT]             ),
      .m_axi_awaddr           (hbm_awaddr[MAP_PORT]           ),
      .m_axi_awlen            (hbm_awlen[MAP_PORT]            ),
      .m_axi_awsize           (hbm_awsize[MAP_PORT]           ),
      .m_axi_awburst          (hbm_awburst[MAP_PORT]          ),
      .m_axi_awlock           (                               ),
      .m_axi_awcache          (                               ),
      .m_axi_awprot           (                               ),
      .m_axi_awqos            (                               ),
      .m_axi_awvalid          (hbm_awvalid[MAP_PORT]          ),
      .m_axi_awready          (hbm_awready[MAP_PORT]          ),
      .m_axi_wid              (                               ),
      .m_axi_wdata            (hbm_wdata[MAP_PORT]            ),
      .m_axi_wstrb            (hbm_wstrb[MAP_PORT]            ),
      .m_axi_wlast            (hbm_wlast[MAP_PORT]            ),
      .m_axi_wvalid           (hbm_wvalid[MAP_PORT]           ),
      .m_axi_wready           (hbm_wready[MAP_PORT]           ),
      .m_axi_bid              (hbm_bid[MAP_PORT]              ),
      .m_axi_bresp            (hbm_bresp[MAP_PORT]            ),
      .m_axi_bvalid           (hbm_bvalid[MAP_PORT]           ),
      .m_axi_bready           (hbm_bready[MAP_PORT]           ),
      .m_axi_arid             (hbm_arid[MAP_PORT]             ),
      .m_axi_araddr           (hbm_araddr[MAP_PORT]           ),
      .m_axi_arlen            (hbm_arlen[MAP_PORT]            ),
      .m_axi_arsize           (hbm_arsize[MAP_PORT]           ),
      .m_axi_arburst          (hbm_arburst[MAP_PORT]          ),
      .m_axi_arlock           (                               ),
      .m_axi_arcache          (                               ),
      .m_axi_arprot           (                               ),
      .m_axi_arqos            (                               ),
      .m_axi_arvalid          (hbm_arvalid[MAP_PORT]          ),
      .m_axi_arready          (hbm_arready[MAP_PORT]          ),
      .m_axi_rid              (hbm_rid[MAP_PORT]              ),
      .m_axi_rdata            (hbm_rdata[MAP_PORT]            ),
      .m_axi_rresp            (hbm_rresp[MAP_PORT]            ),
      .m_axi_rlast            (hbm_rlast[MAP_PORT]            ),
      .m_axi_rvalid           (hbm_rvalid[MAP_PORT]           ),
      .m_axi_rready           (hbm_rready[MAP_PORT]           )
    );

    // Connect other channels between Kernel and HBM
    for (ii = 0; ii < NUM_OF_HBM_PORTS; ii++) begin
      if (ii != MAP_PORT) begin : AXI3_MUX_MAPPING
        assign hbm_araddr      [ii] = hbm_kern_araddr [ii];
        assign hbm_arburst     [ii] = hbm_kern_arburst[ii];
        assign hbm_arid        [ii] = hbm_kern_arid   [ii];
        assign hbm_arlen       [ii] = hbm_kern_arlen  [ii];
        assign hbm_arsize      [ii] = hbm_kern_arsize [ii];
        assign hbm_arvalid     [ii] = hbm_kern_arvalid[ii];
        assign hbm_awaddr      [ii] = hbm_kern_awaddr [ii];
        assign hbm_awburst     [ii] = hbm_kern_awburst[ii];
        assign hbm_awid        [ii] = hbm_kern_awid   [ii];
        assign hbm_awlen       [ii] = hbm_kern_awlen  [ii];
        assign hbm_awsize      [ii] = hbm_kern_awsize [ii];
        assign hbm_awvalid     [ii] = hbm_kern_awvalid[ii];
        assign hbm_rready      [ii] = hbm_kern_rready [ii];
        assign hbm_bready      [ii] = hbm_kern_bready [ii];
        assign hbm_wdata       [ii] = hbm_kern_wdata  [ii];
        assign hbm_wlast       [ii] = hbm_kern_wlast  [ii];
        assign hbm_wstrb       [ii] = hbm_kern_wstrb  [ii];
        assign hbm_wvalid      [ii] = hbm_kern_wvalid [ii];
        assign hbm_kern_arready[ii] = hbm_arready     [ii];
        assign hbm_kern_awready[ii] = hbm_awready     [ii];
        assign hbm_kern_rdata  [ii] = hbm_rdata       [ii];
        assign hbm_kern_rid    [ii] = hbm_rid         [ii];
        assign hbm_kern_rlast  [ii] = hbm_rlast       [ii];
        assign hbm_kern_rresp  [ii] = hbm_rresp       [ii];
        assign hbm_kern_rvalid [ii] = hbm_rvalid      [ii];
        assign hbm_kern_wready [ii] = hbm_wready      [ii];
        assign hbm_kern_bid    [ii] = hbm_bid         [ii];
        assign hbm_kern_bresp  [ii] = hbm_bresp       [ii];
        assign hbm_kern_bvalid [ii] = hbm_bvalid      [ii];
      end
    end

    // HBM Wrapper
    cl_mem_hbm_wrapper
    #(
      .NUM_OF_AXI_PORTS       (NUM_OF_HBM_PORTS               ),
      .AXI4_INTERFACE         (0                              ),
      .AXLEN_WIDTH            (AXLEN_WIDTH                    )
    )
    HBM_WRAPPER_I
    (
      .apb_clk                (clk_hbm_ref                    ),
      .i_clk_250m             (clk                            ),
      .i_rst_250m_n           (rst_n                          ),
      .i_clk_450m             (clk_hbm_axi                    ),
      .i_rst_450m_n           (hbm_axi_rst_n                  ),

      .i_axi_araddr           (hbm_araddr                     ),
      .i_axi_arburst          (hbm_arburst                    ),
      .i_axi_arid             (hbm_arid                       ),
      .i_axi_arlen            (hbm_arlen                      ),
      .i_axi_arsize           (hbm_arsize                     ),
      .i_axi_arvalid          (hbm_arvalid                    ),
      .i_axi_awaddr           (hbm_awaddr                     ),
      .i_axi_awburst          (hbm_awburst                    ),
      .i_axi_awid             (hbm_awid                       ),
      .i_axi_awlen            (hbm_awlen                      ),
      .i_axi_awsize           (hbm_awsize                     ),
      .i_axi_awvalid          (hbm_awvalid                    ),
      .i_axi_rready           (hbm_rready                     ),
      .i_axi_bready           (hbm_bready                     ),
      .i_axi_wdata            (hbm_wdata                      ),
      .i_axi_wlast            (hbm_wlast                      ),
      .i_axi_wstrb            (hbm_wstrb                      ),
      .i_axi_wvalid           (hbm_wvalid                     ),
      .o_axi_arready          (hbm_arready                    ),
      .o_axi_awready          (hbm_awready                    ),
      .o_axi_rdata            (hbm_rdata                      ),
      .o_axi_rid              (hbm_rid                        ),
      .o_axi_rlast            (hbm_rlast                      ),
      .o_axi_rresp            (hbm_rresp                      ),
      .o_axi_rvalid           (hbm_rvalid                     ),
      .o_axi_wready           (hbm_wready                     ),
      .o_axi_bid              (hbm_bid                        ),
      .o_axi_bresp            (hbm_bresp                      ),
      .o_axi_bvalid           (hbm_bvalid                     ),

      .i_hbm_apb_preset_n_1   (i_hbm_apb_preset_n_1           ),
      .o_hbm_apb_paddr_1      (o_hbm_apb_paddr_1              ),
      .o_hbm_apb_pprot_1      (o_hbm_apb_pprot_1              ),
      .o_hbm_apb_psel_1       (o_hbm_apb_psel_1               ),
      .o_hbm_apb_penable_1    (o_hbm_apb_penable_1            ),
      .o_hbm_apb_pwrite_1     (o_hbm_apb_pwrite_1             ),
      .o_hbm_apb_pwdata_1     (o_hbm_apb_pwdata_1             ),
      .o_hbm_apb_pstrb_1      (o_hbm_apb_pstrb_1              ),
      .o_hbm_apb_pready_1     (o_hbm_apb_pready_1             ),
      .o_hbm_apb_prdata_1     (o_hbm_apb_prdata_1             ),
      .o_hbm_apb_pslverr_1    (o_hbm_apb_pslverr_1            ),
      .i_hbm_apb_preset_n_0   (i_hbm_apb_preset_n_0           ),
      .o_hbm_apb_paddr_0      (o_hbm_apb_paddr_0              ),
      .o_hbm_apb_pprot_0      (o_hbm_apb_pprot_0              ),
      .o_hbm_apb_psel_0       (o_hbm_apb_psel_0               ),
      .o_hbm_apb_penable_0    (o_hbm_apb_penable_0            ),
      .o_hbm_apb_pwrite_0     (o_hbm_apb_pwrite_0             ),
      .o_hbm_apb_pwdata_0     (o_hbm_apb_pwdata_0             ),
      .o_hbm_apb_pstrb_0      (o_hbm_apb_pstrb_0              ),
      .o_hbm_apb_pready_0     (o_hbm_apb_pready_0             ),
      .o_hbm_apb_prdata_0     (o_hbm_apb_prdata_0             ),
      .o_hbm_apb_pslverr_0    (o_hbm_apb_pslverr_0            ),

      .hbm_stat_bus           (hbm_stat_bus                   ),
      .o_cl_sh_hbm_stat_int   (o_cl_sh_hbm_stat_int           ),
      .o_hbm_ready            (o_hbm_ready                    )
    );

  end : HBM_PRESENT_EQ_1

  else begin : HBM_PRESENT_EQ_0

    always_comb begin
      hbm_axi4_bus.awready = 1'b1;
      hbm_axi4_bus.wready  = 1'b1;
      hbm_axi4_bus.bid     = 0;
      hbm_axi4_bus.bresp   = 0;
      hbm_axi4_bus.bvalid  = 0;
      hbm_axi4_bus.arready = 1'b1;
      hbm_axi4_bus.rid     = 0;
      hbm_axi4_bus.rdata   = 0;
      hbm_axi4_bus.rresp   = 0;
      hbm_axi4_bus.rlast   = 0;
      hbm_axi4_bus.rvalid  = 0;
      hbm_stat_bus.ack     = 1'b1;
      o_cl_sh_hbm_stat_int = 0;
      o_hbm_ready          = 0;
    end

  end : HBM_PRESENT_EQ_0

  endgenerate


endmodule // cl_mem_hbm_axi4
