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
// CL_HBM_AXI4
// --------
// - Convert 512b 250MHz AXI4 to 450MHz AXI3 bus to feed into HBM
// - Instantiate HBM Wrapper
//=============================================================================

module cl_hbm_axi4
#(
  parameter             HBM_PRESENT = 1
)
(
  input logic           clk_hbm_ref,
  input logic           clk,
  input logic           rst_n,
  axi_bus_t.master      hbm_axi4_bus,         // AXI4 data bus to HBM
  cfg_bus_t.slave       hbm_stat_bus,         // CFG Stats bus to HBM

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
  axi_bus_t  hbm_axi4_bus_q();

  // 256bit AXI3 bus
  axi_bus_t #(.DATA_WIDTH(256), .ADDR_WIDTH(34), .ID_WIDTH(6), .LEN_WIDTH(4)) axi3_256b_bus();
  axi_bus_t #(.DATA_WIDTH(256), .ADDR_WIDTH(34), .ID_WIDTH(6), .LEN_WIDTH(4)) axi3_256b_bus_q();

  logic axi_clk, axi_rst_n, apb_clk, apb_rst_n;

  // HBM wrapper ports
  localparam NUM_OF_HBM_PORTS = 1;

  logic  [33:0] hbm_araddr   [0:(NUM_OF_HBM_PORTS-1)];
  logic   [1:0] hbm_arburst  [0:(NUM_OF_HBM_PORTS-1)];
  logic   [5:0] hbm_arid     [0:(NUM_OF_HBM_PORTS-1)];
  logic   [3:0] hbm_arlen    [0:(NUM_OF_HBM_PORTS-1)];
  logic   [2:0] hbm_arsize   [0:(NUM_OF_HBM_PORTS-1)];
  logic         hbm_arvalid  [0:(NUM_OF_HBM_PORTS-1)];
  logic  [33:0] hbm_awaddr   [0:(NUM_OF_HBM_PORTS-1)];
  logic   [1:0] hbm_awburst  [0:(NUM_OF_HBM_PORTS-1)];
  logic   [5:0] hbm_awid     [0:(NUM_OF_HBM_PORTS-1)];
  logic   [3:0] hbm_awlen    [0:(NUM_OF_HBM_PORTS-1)];
  logic   [2:0] hbm_awsize   [0:(NUM_OF_HBM_PORTS-1)];
  logic         hbm_awvalid  [0:(NUM_OF_HBM_PORTS-1)];
  logic         hbm_rready   [0:(NUM_OF_HBM_PORTS-1)];
  logic         hbm_bready   [0:(NUM_OF_HBM_PORTS-1)];
  logic [255:0] hbm_wdata    [0:(NUM_OF_HBM_PORTS-1)];
  logic         hbm_wlast    [0:(NUM_OF_HBM_PORTS-1)];
  logic  [31:0] hbm_wstrb    [0:(NUM_OF_HBM_PORTS-1)];
  logic         hbm_wvalid   [0:(NUM_OF_HBM_PORTS-1)];
  logic         hbm_arready  [0:(NUM_OF_HBM_PORTS-1)];
  logic         hbm_awready  [0:(NUM_OF_HBM_PORTS-1)];
  logic [255:0] hbm_rdata    [0:(NUM_OF_HBM_PORTS-1)];
  logic   [5:0] hbm_rid      [0:(NUM_OF_HBM_PORTS-1)];
  logic         hbm_rlast    [0:(NUM_OF_HBM_PORTS-1)];
  logic   [1:0] hbm_rresp    [0:(NUM_OF_HBM_PORTS-1)];
  logic         hbm_rvalid   [0:(NUM_OF_HBM_PORTS-1)];
  logic         hbm_wready   [0:(NUM_OF_HBM_PORTS-1)];
  logic   [5:0] hbm_bid      [0:(NUM_OF_HBM_PORTS-1)];
  logic   [1:0] hbm_bresp    [0:(NUM_OF_HBM_PORTS-1)];
  logic         hbm_bvalid   [0:(NUM_OF_HBM_PORTS-1)];

if (HBM_PRESENT) begin : HBM_PRESENT_EQ_1

  axi_register_slice AXI4_REG_SLC_HBM
  (
    .aclk                   (clk                        ),
    .aresetn                (rst_n                      ),

    .s_axi_awid             (hbm_axi4_bus.awid          ),
    .s_axi_awaddr           (hbm_axi4_bus.awaddr        ),
    .s_axi_awlen            (hbm_axi4_bus.awlen         ),
    .s_axi_awsize           (hbm_axi4_bus.awsize        ),
    .s_axi_awburst          (hbm_axi4_bus.awburst       ),
    .s_axi_awlock           (`DEF_AXLOCK                ),
    .s_axi_awcache          (`DEF_AXCACHE               ),
    .s_axi_awprot           (`DEF_AXPROT                ),
    .s_axi_awregion         (`DEF_AXREGION              ),
    .s_axi_awqos            (`DEF_AXQOS                 ),
    .s_axi_awvalid          (hbm_axi4_bus.awvalid       ),
    .s_axi_awready          (hbm_axi4_bus.awready       ),
    .s_axi_wdata            (hbm_axi4_bus.wdata         ),
    .s_axi_wstrb            (hbm_axi4_bus.wstrb         ),
    .s_axi_wlast            (hbm_axi4_bus.wlast         ),
    .s_axi_wvalid           (hbm_axi4_bus.wvalid        ),
    .s_axi_wready           (hbm_axi4_bus.wready        ),
    .s_axi_bid              (hbm_axi4_bus.bid           ),
    .s_axi_bresp            (hbm_axi4_bus.bresp         ),
    .s_axi_bvalid           (hbm_axi4_bus.bvalid        ),
    .s_axi_bready           (hbm_axi4_bus.bready        ),
    .s_axi_arid             (hbm_axi4_bus.arid          ),
    .s_axi_araddr           (hbm_axi4_bus.araddr        ),
    .s_axi_arlen            (hbm_axi4_bus.arlen         ),
    .s_axi_arsize           (hbm_axi4_bus.arsize        ),
    .s_axi_arburst          (hbm_axi4_bus.arburst       ),
    .s_axi_arlock           (`DEF_AXLOCK                ),
    .s_axi_arcache          (`DEF_AXCACHE               ),
    .s_axi_arprot           (`DEF_AXPROT                ),
    .s_axi_arregion         (`DEF_AXREGION              ),
    .s_axi_arqos            (`DEF_AXQOS                 ),
    .s_axi_arvalid          (hbm_axi4_bus.arvalid       ),
    .s_axi_arready          (hbm_axi4_bus.arready       ),
    .s_axi_rid              (hbm_axi4_bus.rid           ),
    .s_axi_rdata            (hbm_axi4_bus.rdata         ),
    .s_axi_rresp            (hbm_axi4_bus.rresp         ),
    .s_axi_rlast            (hbm_axi4_bus.rlast         ),
    .s_axi_rvalid           (hbm_axi4_bus.rvalid        ),
    .s_axi_rready           (hbm_axi4_bus.rready        ),

    .m_axi_awid             (hbm_axi4_bus_q.awid        ),
    .m_axi_awaddr           (hbm_axi4_bus_q.awaddr      ),
    .m_axi_awlen            (hbm_axi4_bus_q.awlen       ),
    .m_axi_awsize           (hbm_axi4_bus_q.awsize      ),
    .m_axi_awburst          (hbm_axi4_bus_q.awburst     ),
    .m_axi_awlock           (                           ),
    .m_axi_awcache          (                           ),
    .m_axi_awprot           (                           ),
    .m_axi_awregion         (                           ),
    .m_axi_awqos            (                           ),
    .m_axi_awvalid          (hbm_axi4_bus_q.awvalid     ),
    .m_axi_awready          (hbm_axi4_bus_q.awready     ),
    .m_axi_wdata            (hbm_axi4_bus_q.wdata       ),
    .m_axi_wstrb            (hbm_axi4_bus_q.wstrb       ),
    .m_axi_wvalid           (hbm_axi4_bus_q.wvalid      ),
    .m_axi_wlast            (hbm_axi4_bus_q.wlast       ),
    .m_axi_wready           (hbm_axi4_bus_q.wready      ),
    .m_axi_bresp            (hbm_axi4_bus_q.bresp       ),
    .m_axi_bvalid           (hbm_axi4_bus_q.bvalid      ),
    .m_axi_bid              (hbm_axi4_bus_q.bid         ),
    .m_axi_bready           (hbm_axi4_bus_q.bready      ),
    .m_axi_arid             (hbm_axi4_bus_q.arid        ),
    .m_axi_araddr           (hbm_axi4_bus_q.araddr      ),
    .m_axi_arlen            (hbm_axi4_bus_q.arlen       ),
    .m_axi_arsize           (hbm_axi4_bus_q.arsize      ),
    .m_axi_arburst          (hbm_axi4_bus_q.arburst     ),
    .m_axi_arlock           (                           ),
    .m_axi_arcache          (                           ),
    .m_axi_arprot           (                           ),
    .m_axi_arregion         (                           ),
    .m_axi_arqos            (                           ),
    .m_axi_arvalid          (hbm_axi4_bus_q.arvalid     ),
    .m_axi_arready          (hbm_axi4_bus_q.arready     ),
    .m_axi_rid              (hbm_axi4_bus_q.rid         ),
    .m_axi_rdata            (hbm_axi4_bus_q.rdata       ),
    .m_axi_rresp            (hbm_axi4_bus_q.rresp       ),
    .m_axi_rlast            (hbm_axi4_bus_q.rlast       ),
    .m_axi_rvalid           (hbm_axi4_bus_q.rvalid      ),
    .m_axi_rready           (hbm_axi4_bus_q.rready      )
  );

  assign hbm_axi4_bus_q.wid = 'b0;

  logic [29:0] dummy_araddr;
  logic [29:0] dummy_awaddr;

  cl_axi_sc_1x1_wrapper AXI_CONVERTER_AXI4_AXI3
  (
    .aclk_250               (clk                        ),
    .aresetn_250            (rst_n                      ),
    .aclk_450               (axi_clk                    ),

    .AXI4_araddr            (hbm_axi4_bus_q.araddr      ),
    .AXI4_arburst           (hbm_axi4_bus_q.arburst     ),
    .AXI4_arcache           (`DEF_AXCACHE               ),
    .AXI4_arid              (hbm_axi4_bus_q.arid        ),
    .AXI4_arlen             (hbm_axi4_bus_q.arlen       ),
    .AXI4_arlock            (`DEF_AXLOCK                ),
    .AXI4_arprot            (`DEF_AXPROT                ),
    .AXI4_arqos             (`DEF_AXQOS                 ),
    .AXI4_arready           (hbm_axi4_bus_q.arready     ),
    .AXI4_arsize            (hbm_axi4_bus_q.arsize      ),
    .AXI4_arvalid           (hbm_axi4_bus_q.arvalid     ),
    .AXI4_awaddr            (hbm_axi4_bus_q.awaddr      ),
    .AXI4_awburst           (hbm_axi4_bus_q.awburst     ),
    .AXI4_awcache           (`DEF_AXCACHE               ),
    .AXI4_awid              (hbm_axi4_bus_q.awid        ),
    .AXI4_awlen             (hbm_axi4_bus_q.awlen       ),
    .AXI4_awlock            (`DEF_AXLOCK                ),
    .AXI4_awprot            (`DEF_AXPROT                ),
    .AXI4_awqos             (`DEF_AXQOS                 ),
    .AXI4_awready           (hbm_axi4_bus_q.awready     ),
    .AXI4_awsize            (hbm_axi4_bus_q.awsize      ),
    .AXI4_awvalid           (hbm_axi4_bus_q.awvalid     ),
    .AXI4_bid               (hbm_axi4_bus_q.bid         ),
    .AXI4_bready            (hbm_axi4_bus_q.bready      ),
    .AXI4_bresp             (hbm_axi4_bus_q.bresp       ),
    .AXI4_bvalid            (hbm_axi4_bus_q.bvalid      ),
    .AXI4_rdata             (hbm_axi4_bus_q.rdata       ),
    .AXI4_rid               (hbm_axi4_bus_q.rid         ),
    .AXI4_rlast             (hbm_axi4_bus_q.rlast       ),
    .AXI4_rready            (hbm_axi4_bus_q.rready      ),
    .AXI4_rresp             (hbm_axi4_bus_q.rresp       ),
    .AXI4_rvalid            (hbm_axi4_bus_q.rvalid      ),
    .AXI4_wdata             (hbm_axi4_bus_q.wdata       ),
    .AXI4_wlast             (hbm_axi4_bus_q.wlast       ),
    .AXI4_wready            (hbm_axi4_bus_q.wready      ),
    .AXI4_wstrb             (hbm_axi4_bus_q.wstrb       ),
    .AXI4_wvalid            (hbm_axi4_bus_q.wvalid      ),

    .AXI3_araddr            ({dummy_araddr, axi3_256b_bus.araddr}),
    .AXI3_arburst           (axi3_256b_bus.arburst      ),
    .AXI3_arcache           (                           ),
    .AXI3_arlen             (axi3_256b_bus.arlen        ),
    .AXI3_arlock            (                           ),
    .AXI3_arprot            (                           ),
    .AXI3_arqos             (                           ),
    .AXI3_arready           (axi3_256b_bus.arready      ),
    .AXI3_arsize            (axi3_256b_bus.arsize       ),
    .AXI3_arvalid           (axi3_256b_bus.arvalid      ),
    .AXI3_awaddr            ({dummy_awaddr, axi3_256b_bus.awaddr}),
    .AXI3_awburst           (axi3_256b_bus.awburst      ),
    .AXI3_awcache           (                           ),
    .AXI3_awlen             (axi3_256b_bus.awlen        ),
    .AXI3_awlock            (                           ),
    .AXI3_awprot            (                           ),
    .AXI3_awqos             (                           ),
    .AXI3_awready           (axi3_256b_bus.awready      ),
    .AXI3_awsize            (axi3_256b_bus.awsize       ),
    .AXI3_awvalid           (axi3_256b_bus.awvalid      ),
    .AXI3_bready            (axi3_256b_bus.bready       ),
    .AXI3_bresp             (axi3_256b_bus.bresp        ),
    .AXI3_bvalid            (axi3_256b_bus.bvalid       ),
    .AXI3_rdata             (axi3_256b_bus.rdata        ),
    .AXI3_rlast             (axi3_256b_bus.rlast        ),
    .AXI3_rready            (axi3_256b_bus.rready       ),
    .AXI3_rresp             (axi3_256b_bus.rresp        ),
    .AXI3_rvalid            (axi3_256b_bus.rvalid       ),
    .AXI3_wdata             (axi3_256b_bus.wdata        ),
    .AXI3_wlast             (axi3_256b_bus.wlast        ),
    .AXI3_wready            (axi3_256b_bus.wready       ),
    .AXI3_wstrb             (axi3_256b_bus.wstrb        ),
    .AXI3_wvalid            (axi3_256b_bus.wvalid       )
  );

  assign axi3_256b_bus.awid = 'b0;
  assign axi3_256b_bus.wid  = 'b0;
  assign axi3_256b_bus.arid = 'b0;

cl_axi3_256b_reg_slice AXI3_REG_SLC_HBM
  (
    .aclk                   (axi_clk                    ),
    .aresetn                (axi_rst_n                  ),

    .s_axi_awid             (axi3_256b_bus.awid         ),
    .s_axi_awaddr           (axi3_256b_bus.awaddr       ),
    .s_axi_awlen            (axi3_256b_bus.awlen        ),
    .s_axi_awsize           (axi3_256b_bus.awsize       ),
    .s_axi_awburst          (axi3_256b_bus.awburst      ),
    .s_axi_awlock           ({2{`DEF_AXLOCK}}           ),
    .s_axi_awcache          (`DEF_AXCACHE               ),
    .s_axi_awprot           (`DEF_AXPROT                ),
    .s_axi_awqos            (`DEF_AXQOS                 ),
    .s_axi_awvalid          (axi3_256b_bus.awvalid      ),
    .s_axi_awready          (axi3_256b_bus.awready      ),
    .s_axi_wid              (axi3_256b_bus.wid          ),
    .s_axi_wdata            (axi3_256b_bus.wdata        ),
    .s_axi_wstrb            (axi3_256b_bus.wstrb        ),
    .s_axi_wlast            (axi3_256b_bus.wlast        ),
    .s_axi_wvalid           (axi3_256b_bus.wvalid       ),
    .s_axi_wready           (axi3_256b_bus.wready       ),
    .s_axi_bid              (axi3_256b_bus.bid          ),
    .s_axi_bresp            (axi3_256b_bus.bresp        ),
    .s_axi_bvalid           (axi3_256b_bus.bvalid       ),
    .s_axi_bready           (axi3_256b_bus.bready       ),
    .s_axi_arid             (axi3_256b_bus.arid         ),
    .s_axi_araddr           (axi3_256b_bus.araddr       ),
    .s_axi_arlen            (axi3_256b_bus.arlen        ),
    .s_axi_arsize           (axi3_256b_bus.arsize       ),
    .s_axi_arburst          (axi3_256b_bus.arburst      ),
    .s_axi_arlock           ({2{`DEF_AXLOCK}}           ),
    .s_axi_arcache          (`DEF_AXCACHE               ),
    .s_axi_arprot           (`DEF_AXPROT                ),
    .s_axi_arqos            (`DEF_AXQOS                 ),
    .s_axi_arvalid          (axi3_256b_bus.arvalid      ),
    .s_axi_arready          (axi3_256b_bus.arready      ),
    .s_axi_rid              (axi3_256b_bus.rid          ),
    .s_axi_rdata            (axi3_256b_bus.rdata        ),
    .s_axi_rresp            (axi3_256b_bus.rresp        ),
    .s_axi_rlast            (axi3_256b_bus.rlast        ),
    .s_axi_rvalid           (axi3_256b_bus.rvalid       ),
    .s_axi_rready           (axi3_256b_bus.rready       ),

    .m_axi_awid             (axi3_256b_bus_q.awid       ),
    .m_axi_awaddr           (axi3_256b_bus_q.awaddr     ),
    .m_axi_awlen            (axi3_256b_bus_q.awlen      ),
    .m_axi_awsize           (axi3_256b_bus_q.awsize     ),
    .m_axi_awburst          (axi3_256b_bus_q.awburst    ),
    .m_axi_awlock           (                           ),
    .m_axi_awcache          (                           ),
    .m_axi_awprot           (                           ),
    .m_axi_awqos            (                           ),
    .m_axi_awvalid          (axi3_256b_bus_q.awvalid    ),
    .m_axi_awready          (axi3_256b_bus_q.awready    ),
    .m_axi_wid              (axi3_256b_bus_q.wid        ),
    .m_axi_wdata            (axi3_256b_bus_q.wdata      ),
    .m_axi_wstrb            (axi3_256b_bus_q.wstrb      ),
    .m_axi_wlast            (axi3_256b_bus_q.wlast      ),
    .m_axi_wvalid           (axi3_256b_bus_q.wvalid     ),
    .m_axi_wready           (axi3_256b_bus_q.wready     ),
    .m_axi_bid              (axi3_256b_bus_q.bid        ),
    .m_axi_bresp            (axi3_256b_bus_q.bresp      ),
    .m_axi_bvalid           (axi3_256b_bus_q.bvalid     ),
    .m_axi_bready           (axi3_256b_bus_q.bready     ),
    .m_axi_arid             (axi3_256b_bus_q.arid       ),
    .m_axi_araddr           (axi3_256b_bus_q.araddr     ),
    .m_axi_arlen            (axi3_256b_bus_q.arlen      ),
    .m_axi_arsize           (axi3_256b_bus_q.arsize     ),
    .m_axi_arburst          (axi3_256b_bus_q.arburst    ),
    .m_axi_arlock           (                           ),
    .m_axi_arcache          (                           ),
    .m_axi_arprot           (                           ),
    .m_axi_arqos            (                           ),
    .m_axi_arvalid          (axi3_256b_bus_q.arvalid    ),
    .m_axi_arready          (axi3_256b_bus_q.arready    ),
    .m_axi_rid              (axi3_256b_bus_q.rid        ),
    .m_axi_rdata            (axi3_256b_bus_q.rdata      ),
    .m_axi_rresp            (axi3_256b_bus_q.rresp      ),
    .m_axi_rlast            (axi3_256b_bus_q.rlast      ),
    .m_axi_rvalid           (axi3_256b_bus_q.rvalid     ),
    .m_axi_rready           (axi3_256b_bus_q.rready     )
    );

  // convert from interface to ports
  always_comb begin
    hbm_araddr[0]            = axi3_256b_bus_q.araddr;
    hbm_arburst[0]           = axi3_256b_bus_q.arburst;
    hbm_arid[0]              = axi3_256b_bus_q.arid;
    hbm_arlen[0]             = axi3_256b_bus_q.arlen;
    hbm_arsize[0]            = axi3_256b_bus_q.arsize;
    hbm_arvalid[0]           = axi3_256b_bus_q.arvalid;
    hbm_awaddr[0]            = axi3_256b_bus_q.awaddr;
    hbm_awburst[0]           = axi3_256b_bus_q.awburst;
    hbm_awid[0]              = axi3_256b_bus_q.awid;
    hbm_awlen[0]             = axi3_256b_bus_q.awlen;
    hbm_awsize[0]            = axi3_256b_bus_q.awsize;
    hbm_awvalid [0]          = axi3_256b_bus_q.awvalid;
    hbm_rready[0]            = axi3_256b_bus_q.rready;
    hbm_bready[0]            = axi3_256b_bus_q.bready;
    hbm_wdata[0]             = axi3_256b_bus_q.wdata;
    hbm_wlast[0]             = axi3_256b_bus_q.wlast;
    hbm_wstrb[0]             = axi3_256b_bus_q.wstrb;
    hbm_wvalid[0]            = axi3_256b_bus_q.wvalid;
    axi3_256b_bus_q.arready  = hbm_arready[0];
    axi3_256b_bus_q.awready  = hbm_awready[0];
    axi3_256b_bus_q.rdata    = hbm_rdata[0];
    axi3_256b_bus_q.rid      = hbm_rid[0];
    axi3_256b_bus_q.rlast    = hbm_rlast[0];
    axi3_256b_bus_q.rresp    = hbm_rresp[0];
    axi3_256b_bus_q.rvalid   = hbm_rvalid[0];
    axi3_256b_bus_q.wready   = hbm_wready[0];
    axi3_256b_bus_q.bid      = hbm_bid[0];
    axi3_256b_bus_q.bresp    = hbm_bresp[0];
    axi3_256b_bus_q.bvalid   = hbm_bvalid[0];
  end

  cl_hbm_wrapper
  #(
    .NUM_OF_AXI_PORTS       (NUM_OF_HBM_PORTS           ),
    .AXI4_INTERFACE         (0                          ),
    .AXLEN_WIDTH            (4                          )
  )
  HBM_WRAPPER_I
  (
    .apb_clk                (clk_hbm_ref                ),  // Input clk 100 MHz
    .i_clk_250m             (clk                        ),  // Input clk 250 MHz
    .i_rst_250m_n           (rst_n                      ),  // Input reset syncd to i_clk_250m
    .o_clk_450m             (axi_clk                    ),  // Output clk 450MHz. This is the clock for AXI interfaces.
    .o_rst_450m_n           (axi_rst_n                  ),  // Output reset syncd to o_clk_450m
    .o_clk_100m             (apb_clk                    ),  // Output clk 100Mhz. This is the APB clock used by HBM's APB interface.
    .o_rst_100m_n           (apb_rst_n                  ),  // Output clk 100Mhz. Reset synchronized to 100MHz clock
    .i_axi_araddr           (hbm_araddr                 ),
    .i_axi_arburst          (hbm_arburst                ),
    .i_axi_arid             (hbm_arid                   ),
    .i_axi_arlen            (hbm_arlen                  ),
    .i_axi_arsize           (hbm_arsize                 ),
    .i_axi_arvalid          (hbm_arvalid                ),
    .i_axi_awaddr           (hbm_awaddr                 ),
    .i_axi_awburst          (hbm_awburst                ),
    .i_axi_awid             (hbm_awid                   ),
    .i_axi_awlen            (hbm_awlen                  ),
    .i_axi_awsize           (hbm_awsize                 ),
    .i_axi_awvalid          (hbm_awvalid                ),
    .i_axi_rready           (hbm_rready                 ),
    .i_axi_bready           (hbm_bready                 ),
    .i_axi_wdata            (hbm_wdata                  ),
    .i_axi_wlast            (hbm_wlast                  ),
    .i_axi_wstrb            (hbm_wstrb                  ),
    .i_axi_wvalid           (hbm_wvalid                 ),
    .o_axi_arready          (hbm_arready                ),
    .o_axi_awready          (hbm_awready                ),
    .o_axi_rdata            (hbm_rdata                  ),
    .o_axi_rid              (hbm_rid                    ),
    .o_axi_rlast            (hbm_rlast                  ),
    .o_axi_rresp            (hbm_rresp                  ),
    .o_axi_rvalid           (hbm_rvalid                 ),
    .o_axi_wready           (hbm_wready                 ),
    .o_axi_bid              (hbm_bid                    ),
    .o_axi_bresp            (hbm_bresp                  ),
    .o_axi_bvalid           (hbm_bvalid                 ),

    .i_hbm_apb_preset_n_1   (i_hbm_apb_preset_n_1       ),
    .o_hbm_apb_paddr_1      (o_hbm_apb_paddr_1          ),
    .o_hbm_apb_pprot_1      (o_hbm_apb_pprot_1          ),
    .o_hbm_apb_psel_1       (o_hbm_apb_psel_1           ),
    .o_hbm_apb_penable_1    (o_hbm_apb_penable_1        ),
    .o_hbm_apb_pwrite_1     (o_hbm_apb_pwrite_1         ),
    .o_hbm_apb_pwdata_1     (o_hbm_apb_pwdata_1         ),
    .o_hbm_apb_pstrb_1      (o_hbm_apb_pstrb_1          ),
    .o_hbm_apb_pready_1     (o_hbm_apb_pready_1         ),
    .o_hbm_apb_prdata_1     (o_hbm_apb_prdata_1         ),
    .o_hbm_apb_pslverr_1    (o_hbm_apb_pslverr_1        ),
    .i_hbm_apb_preset_n_0   (i_hbm_apb_preset_n_0       ),
    .o_hbm_apb_paddr_0      (o_hbm_apb_paddr_0          ),
    .o_hbm_apb_pprot_0      (o_hbm_apb_pprot_0          ),
    .o_hbm_apb_psel_0       (o_hbm_apb_psel_0           ),
    .o_hbm_apb_penable_0    (o_hbm_apb_penable_0        ),
    .o_hbm_apb_pwrite_0     (o_hbm_apb_pwrite_0         ),
    .o_hbm_apb_pwdata_0     (o_hbm_apb_pwdata_0         ),
    .o_hbm_apb_pstrb_0      (o_hbm_apb_pstrb_0          ),
    .o_hbm_apb_pready_0     (o_hbm_apb_pready_0         ),
    .o_hbm_apb_prdata_0     (o_hbm_apb_prdata_0         ),
    .o_hbm_apb_pslverr_0    (o_hbm_apb_pslverr_0        ),

    .hbm_stat_bus           (hbm_stat_bus               ),  // CFG Stats bus to HBM (in i_clk_250m domain)
    .o_cl_sh_hbm_stat_int   (o_cl_sh_hbm_stat_int       ),  // output [7:0] No interrupts from HBM
    .o_hbm_ready            (o_hbm_ready                )   // output HBM Init Ready (in clk 250mhz domain)
  );

end : HBM_PRESENT_EQ_1
else begin : HBM_PRESENT_EQ_0

  always_comb begin
    hbm_axi4_bus_q.awready = 1'b1;
    hbm_axi4_bus_q.wready  = 1'b1;
    hbm_axi4_bus_q.bid     = 0;
    hbm_axi4_bus_q.bresp   = 0;
    hbm_axi4_bus_q.bvalid  = 0;
    hbm_axi4_bus_q.arready = 1'b1;
    hbm_axi4_bus_q.rid     = 0;
    hbm_axi4_bus_q.rdata   = 0;
    hbm_axi4_bus_q.rresp   = 0;
    hbm_axi4_bus_q.rlast   = 0;
    hbm_axi4_bus_q.rvalid  = 0;
    hbm_stat_bus.ack       = 1'b1;
    o_cl_sh_hbm_stat_int   = 0;
    o_hbm_ready            = 0;
  end

end : HBM_PRESENT_EQ_0

endmodule // cl_hbm_axi4
