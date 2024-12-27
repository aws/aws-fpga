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


///////////////////////////////////////////////////////////////////////////////////////
// CL_HBM_PERF_KERNEL
// -------------------
// - Kernel fine tuned to max out HBM Bandwidth and measure throughput
//
///////////////////////////////////////////////////////////////////////////////////////

module cl_hbm_perf_kernel
  #(
    parameter NUM_OT        = 64, // Number of Outstanding Transaactions
    parameter NUM_CHANNELS  = 32,
    parameter AXLEN_WIDTH   = 4
    )
   (
    input  logic                        clk_main_a0,
    input  logic                        rst_main_a0,
    input  logic                        clk_hbm,
    input  logic                        rst_hbm_n,
    //
    // CFG Interface in clk_main_a0 domain
    //
    input  logic [31:0]                 i_cfg_addr,
    input  logic [31:0]                 i_cfg_wdata,
    input  logic                        i_cfg_wr,
    input  logic                        i_cfg_rd,
    output logic [31:0]                 o_cfg_rdata,
    output logic                        o_cfg_ack,
    output logic                        o_kernel_enable,
    //
    // HBM AXI-3 Channels in clk_hbm domain
    //
    output logic  [33 : 0]              o_axi_araddr   [0:NUM_CHANNELS-1],
    output logic  [1 : 0]               o_axi_arburst  [0:NUM_CHANNELS-1],
    output logic  [5 : 0]               o_axi_arid     [0:NUM_CHANNELS-1],
    output logic  [AXLEN_WIDTH-1 : 0]   o_axi_arlen    [0:NUM_CHANNELS-1],
    output logic  [2 : 0]               o_axi_arsize   [0:NUM_CHANNELS-1],
    output logic                        o_axi_arvalid  [0:NUM_CHANNELS-1],
    output logic  [33 : 0]              o_axi_awaddr   [0:NUM_CHANNELS-1],
    output logic  [1 : 0]               o_axi_awburst  [0:NUM_CHANNELS-1],
    output logic  [5 : 0]               o_axi_awid     [0:NUM_CHANNELS-1],
    output logic  [AXLEN_WIDTH-1 : 0]   o_axi_awlen    [0:NUM_CHANNELS-1],
    output logic  [2 : 0]               o_axi_awsize   [0:NUM_CHANNELS-1],
    output logic                        o_axi_awvalid  [0:NUM_CHANNELS-1],
    output logic                        o_axi_rready   [0:NUM_CHANNELS-1],
    output logic                        o_axi_bready   [0:NUM_CHANNELS-1],
    output logic  [255 : 0]             o_axi_wdata    [0:NUM_CHANNELS-1],
    output logic                        o_axi_wlast    [0:NUM_CHANNELS-1],
    output logic  [31 : 0]              o_axi_wstrb    [0:NUM_CHANNELS-1],
    output logic                        o_axi_wvalid   [0:NUM_CHANNELS-1],
    input  logic                        i_axi_arready  [0:NUM_CHANNELS-1],
    input  logic                        i_axi_awready  [0:NUM_CHANNELS-1],
    input  logic  [255 : 0]             i_axi_rdata    [0:NUM_CHANNELS-1],
    input  logic  [5 : 0]               i_axi_rid      [0:NUM_CHANNELS-1],
    input  logic                        i_axi_rlast    [0:NUM_CHANNELS-1],
    input  logic  [1 : 0]               i_axi_rresp    [0:NUM_CHANNELS-1],
    input  logic                        i_axi_rvalid   [0:NUM_CHANNELS-1],
    input  logic                        i_axi_wready   [0:NUM_CHANNELS-1],
    input  logic  [5 : 0]               i_axi_bid      [0:NUM_CHANNELS-1],
    input  logic  [1 : 0]               i_axi_bresp    [0:NUM_CHANNELS-1],
    input  logic                        i_axi_bvalid   [0:NUM_CHANNELS-1]
    );

   //===================================================================
   // local signals
   //===================================================================
   localparam DEF_AWBURST      = 2'd1; // Only INCR burst
   localparam DEF_AWLOCK       = 1'd0;
   localparam DEF_AWCACHE      = 4'h1; // Device bufferable, non-cacheable
   localparam DEF_AWPROT       = 3'd0;
   localparam DEF_AWREGION     = 4'd0;
   localparam DEF_AWQOS        = 4'd0;

   logic [NUM_CHANNELS-1:0]             wr_pulse;
   logic [NUM_CHANNELS-1:0]             rd_pulse;
   logic [3:0]                          cfg_axlen;
   logic [31:0]                         wdata_pattern;
   logic [NUM_CHANNELS-1:0]             wr_done_pulse;
   logic [NUM_CHANNELS-1:0]             rd_done_pulse;
   logic [NUM_CHANNELS-1:0]             bresp_err_pulse;
   logic [NUM_CHANNELS-1:0]             rresp_err_pulse;

   logic [33 : 0]                       axi_araddr   [0:NUM_CHANNELS-1];
   logic [1 : 0]                        axi_arburst  [0:NUM_CHANNELS-1];
   logic [5 : 0]                        axi_arid     [0:NUM_CHANNELS-1];
   logic [AXLEN_WIDTH-1 : 0]            axi_arlen    [0:NUM_CHANNELS-1];
   logic [2 : 0]                        axi_arsize   [0:NUM_CHANNELS-1];
   logic                                axi_arvalid  [0:NUM_CHANNELS-1];
   logic [33 : 0]                       axi_awaddr   [0:NUM_CHANNELS-1];
   logic [1 : 0]                        axi_awburst  [0:NUM_CHANNELS-1];
   logic [5 : 0]                        axi_awid     [0:NUM_CHANNELS-1];
   logic [AXLEN_WIDTH-1 : 0]            axi_awlen    [0:NUM_CHANNELS-1];
   logic [2 : 0]                        axi_awsize   [0:NUM_CHANNELS-1];
   logic                                axi_awvalid  [0:NUM_CHANNELS-1];
   logic                                axi_rready   [0:NUM_CHANNELS-1];
   logic                                axi_bready   [0:NUM_CHANNELS-1];
   logic [255 : 0]                      axi_wdata    [0:NUM_CHANNELS-1];
   logic                                axi_wlast    [0:NUM_CHANNELS-1];
   logic [31 : 0]                       axi_wstrb    [0:NUM_CHANNELS-1];
   logic                                axi_wvalid   [0:NUM_CHANNELS-1];
   logic                                axi_arready  [0:NUM_CHANNELS-1];
   logic                                axi_awready  [0:NUM_CHANNELS-1];
   logic [255 : 0]                      axi_rdata    [0:NUM_CHANNELS-1];
   logic [5 : 0]                        axi_rid      [0:NUM_CHANNELS-1];
   logic                                axi_rlast    [0:NUM_CHANNELS-1];
   logic [1 : 0]                        axi_rresp    [0:NUM_CHANNELS-1];
   logic                                axi_rvalid   [0:NUM_CHANNELS-1];
   logic                                axi_wready   [0:NUM_CHANNELS-1];
   logic [5 : 0]                        axi_bid      [0:NUM_CHANNELS-1];
   logic [1 : 0]                        axi_bresp    [0:NUM_CHANNELS-1];
   logic                                axi_bvalid   [0:NUM_CHANNELS-1];

   logic [33 : 0]                       q1_axi_araddr   [0:NUM_CHANNELS-1];
   logic [1 : 0]                        q1_axi_arburst  [0:NUM_CHANNELS-1];
   logic [5 : 0]                        q1_axi_arid     [0:NUM_CHANNELS-1];
   logic [AXLEN_WIDTH-1 : 0]            q1_axi_arlen    [0:NUM_CHANNELS-1];
   logic [2 : 0]                        q1_axi_arsize   [0:NUM_CHANNELS-1];
   logic                                q1_axi_arvalid  [0:NUM_CHANNELS-1];
   logic [33 : 0]                       q1_axi_awaddr   [0:NUM_CHANNELS-1];
   logic [1 : 0]                        q1_axi_awburst  [0:NUM_CHANNELS-1];
   logic [5 : 0]                        q1_axi_awid     [0:NUM_CHANNELS-1];
   logic [AXLEN_WIDTH-1 : 0]            q1_axi_awlen    [0:NUM_CHANNELS-1];
   logic [2 : 0]                        q1_axi_awsize   [0:NUM_CHANNELS-1];
   logic                                q1_axi_awvalid  [0:NUM_CHANNELS-1];
   logic                                q1_axi_rready   [0:NUM_CHANNELS-1];
   logic                                q1_axi_bready   [0:NUM_CHANNELS-1];
   logic [255 : 0]                      q1_axi_wdata    [0:NUM_CHANNELS-1];
   logic                                q1_axi_wlast    [0:NUM_CHANNELS-1];
   logic [31 : 0]                       q1_axi_wstrb    [0:NUM_CHANNELS-1];
   logic                                q1_axi_wvalid   [0:NUM_CHANNELS-1];
   logic                                q1_axi_arready  [0:NUM_CHANNELS-1];
   logic                                q1_axi_awready  [0:NUM_CHANNELS-1];
   logic [255 : 0]                      q1_axi_rdata    [0:NUM_CHANNELS-1];
   logic [5 : 0]                        q1_axi_rid      [0:NUM_CHANNELS-1];
   logic                                q1_axi_rlast    [0:NUM_CHANNELS-1];
   logic [1 : 0]                        q1_axi_rresp    [0:NUM_CHANNELS-1];
   logic                                q1_axi_rvalid   [0:NUM_CHANNELS-1];
   logic                                q1_axi_wready   [0:NUM_CHANNELS-1];
   logic [5 : 0]                        q1_axi_bid      [0:NUM_CHANNELS-1];
   logic [1 : 0]                        q1_axi_bresp    [0:NUM_CHANNELS-1];
   logic                                q1_axi_bvalid   [0:NUM_CHANNELS-1];

   logic [33 : 0]                       q2_axi_araddr   [0:NUM_CHANNELS-1];
   logic [1 : 0]                        q2_axi_arburst  [0:NUM_CHANNELS-1];
   logic [5 : 0]                        q2_axi_arid     [0:NUM_CHANNELS-1];
   logic [AXLEN_WIDTH-1 : 0]            q2_axi_arlen    [0:NUM_CHANNELS-1];
   logic [2 : 0]                        q2_axi_arsize   [0:NUM_CHANNELS-1];
   logic                                q2_axi_arvalid  [0:NUM_CHANNELS-1];
   logic [33 : 0]                       q2_axi_awaddr   [0:NUM_CHANNELS-1];
   logic [1 : 0]                        q2_axi_awburst  [0:NUM_CHANNELS-1];
   logic [5 : 0]                        q2_axi_awid     [0:NUM_CHANNELS-1];
   logic [AXLEN_WIDTH-1 : 0]            q2_axi_awlen    [0:NUM_CHANNELS-1];
   logic [2 : 0]                        q2_axi_awsize   [0:NUM_CHANNELS-1];
   logic                                q2_axi_awvalid  [0:NUM_CHANNELS-1];
   logic                                q2_axi_rready   [0:NUM_CHANNELS-1];
   logic                                q2_axi_bready   [0:NUM_CHANNELS-1];
   logic [255 : 0]                      q2_axi_wdata    [0:NUM_CHANNELS-1];
   logic                                q2_axi_wlast    [0:NUM_CHANNELS-1];
   logic [31 : 0]                       q2_axi_wstrb    [0:NUM_CHANNELS-1];
   logic                                q2_axi_wvalid   [0:NUM_CHANNELS-1];
   logic                                q2_axi_arready  [0:NUM_CHANNELS-1];
   logic                                q2_axi_awready  [0:NUM_CHANNELS-1];
   logic [255 : 0]                      q2_axi_rdata    [0:NUM_CHANNELS-1];
   logic [5 : 0]                        q2_axi_rid      [0:NUM_CHANNELS-1];
   logic                                q2_axi_rlast    [0:NUM_CHANNELS-1];
   logic [1 : 0]                        q2_axi_rresp    [0:NUM_CHANNELS-1];
   logic                                q2_axi_rvalid   [0:NUM_CHANNELS-1];
   logic                                q2_axi_wready   [0:NUM_CHANNELS-1];
   logic [5 : 0]                        q2_axi_bid      [0:NUM_CHANNELS-1];
   logic [1 : 0]                        q2_axi_bresp    [0:NUM_CHANNELS-1];
   logic                                q2_axi_bvalid   [0:NUM_CHANNELS-1];

   //===================================================================
   // Instantiate Kernel Controller
   //===================================================================
   cl_kernel_ctl
     #(
       .NUM_OT             (NUM_OT          ),
       .NUM_CHANNELS       (NUM_CHANNELS)
       )
   CL_KERNEL_CTL_I
     (
      .clk_main_a0         (clk_main_a0     ),
      .rst_main_a0         (rst_main_a0     ),
      .clk_hbm             (clk_hbm         ),
      .rst_hbm_n           (rst_hbm_n       ),
      .o_wr_pulse          (wr_pulse        ),  // clk_hbm domain
      .o_rd_pulse          (rd_pulse        ),  // clk_hbm domain
      .o_cfg_axlen         (cfg_axlen       ),  // clk_hbm domain
      .o_cfg_wdata_pattern (wdata_pattern   ),  // clk_hbm domian
      .i_wr_done_pulse     (wr_done_pulse   ),  // in clk_hbm domain
      .i_rd_done_pulse     (rd_done_pulse   ),  // in clk_hbm domain
      .i_bresp_err_pulse   (bresp_err_pulse ),  // in clk_hbm domain
      .i_rresp_err_pulse   (rresp_err_pulse ),  // in clk_hbm domain
      .i_cfg_addr          (i_cfg_addr      ),
      .i_cfg_wdata         (i_cfg_wdata     ),
      .i_cfg_wr            (i_cfg_wr        ),
      .i_cfg_rd            (i_cfg_rd        ),
      .o_cfg_rdata         (o_cfg_rdata     ),
      .o_cfg_ack           (o_cfg_ack       ),
      .o_kernel_enable     (o_kernel_enable )
      );

   //===================================================================
   // Instantiate AXI3 Interface
   //===================================================================
   localparam HBM_START_ADDR = 64'h0000_0000_0000_0000;

   generate //{
      for (genvar jj = 0; jj < NUM_CHANNELS; jj++) begin : HBM_AXI3_I //{
         cl_axi_ctl
             #(
               .DATA_WIDTH        (256                     ),
               .NUM_OT            (NUM_OT                  ),
               .AXI_START_ADDR    (HBM_START_ADDR + (jj * 64'h0000_0000_2000_0000)),
               .AXI_END_ADDR_MASK (64'h0000_0000_1FFF_FFFF ),
               .AXLEN_WIDTH       (AXLEN_WIDTH             ),
               .AXID_WIDTH        (6                       )
               )
         CL_AXI_CTL_I
              (
               .clk               (clk_hbm             ),
               .rst_n             (rst_hbm_n           ),
               .i_wr_pulse        (wr_pulse[jj]        ),
               .i_rd_pulse        (rd_pulse[jj]        ),
               .i_cfg_axlen       (cfg_axlen           ),
               .i_wdata_pattern   (wdata_pattern       ),
               .o_wr_done_pulse   (wr_done_pulse[jj]   ),
               .o_rd_done_pulse   (rd_done_pulse[jj]   ),
               .o_bresp_err_pulse (bresp_err_pulse[jj] ),
               .o_rresp_err_pulse (rresp_err_pulse[jj] ),
               .o_wr_req_pend     (                    ),
               .o_rd_req_pend     (                    ),
               .o_axi_awid        (axi_awid[jj]        ),
               .o_axi_awaddr      (axi_awaddr[jj]      ),
               .o_axi_awregion    (                    ),
               .o_axi_awlen       (axi_awlen[jj]       ),
               .o_axi_awsize      (axi_awsize[jj]      ),
               .o_axi_awburst     (axi_awburst[jj]     ),
               .o_axi_awvalid     (axi_awvalid[jj]     ),
               .i_axi_awready     (axi_awready[jj]     ),
               .o_axi_wid         (                    ),
               .o_axi_wdata       (axi_wdata[jj]       ),
               .o_axi_wstrb       (axi_wstrb[jj]       ),
               .o_axi_wlast       (axi_wlast[jj]       ),
               .o_axi_wvalid      (axi_wvalid[jj]      ),
               .i_axi_wready      (axi_wready[jj]      ),
               .i_axi_bid         (axi_bid[jj]         ),
               .i_axi_bresp       (axi_bresp[jj]       ),
               .i_axi_bvalid      (axi_bvalid[jj]      ),
               .o_axi_bready      (axi_bready[jj]      ),
               .o_axi_arid        (axi_arid[jj]        ),
               .o_axi_araddr      (axi_araddr[jj]      ),
               .o_axi_arregion    (                    ),
               .o_axi_arlen       (axi_arlen[jj]       ),
               .o_axi_arsize      (axi_arsize[jj]      ),
               .o_axi_arburst     (axi_arburst[jj]     ),
               .o_axi_arvalid     (axi_arvalid[jj]     ),
               .i_axi_arready     (axi_arready[jj]     ),
               .i_axi_rid         (axi_rid[jj]         ),
               .i_axi_rdata       (axi_rdata[jj]       ),
               .i_axi_rresp       (axi_rresp[jj]       ),
               .i_axi_rlast       (axi_rlast[jj]       ),
               .i_axi_rvalid      (axi_rvalid[jj]      ),
               .o_axi_rready      (axi_rready[jj]      )
              );

         //
         // AXI3 Reg Slice
         //
         cl_axi3_256b_reg_slice CL_AXI3_HBM_REG_SLC_I
           (
            .aclk                 (clk_hbm             ),  //  input wire aclk
            .aresetn              (rst_hbm_n           ),  //  input wire aresetn
            .s_axi_awid           (axi_awid       [jj] ),  //  input wire [5 : 0] s_axi_awid
            .s_axi_awaddr         (axi_awaddr     [jj] ),  //  input wire [33 : 0] s_axi_awaddr
            .s_axi_awlen          (axi_awlen      [jj] ),  //  input wire [3 : 0] s_axi_awlen
            .s_axi_awsize         (axi_awsize     [jj] ),  //  input wire [2 : 0] s_axi_awsize
            .s_axi_awburst        (axi_awburst    [jj] ),  //  input wire [1 : 0] s_axi_awburst
            .s_axi_awlock         (DEF_AWLOCK          ),  //  input wire [1 : 0] s_axi_awlock
            .s_axi_awcache        (DEF_AWCACHE         ),  //  input wire [3 : 0] s_axi_awcache
            .s_axi_awprot         (DEF_AWPROT          ),  //  input wire [2 : 0] s_axi_awprot
            .s_axi_awqos          (DEF_AWQOS           ),  //  input wire [3 : 0] s_axi_awqos
            .s_axi_awvalid        (axi_awvalid    [jj] ),  //  input wire s_axi_awvalid
            .s_axi_awready        (axi_awready    [jj] ),  //  output wire s_axi_awready
            .s_axi_wid            (6'd0                ),  //  input wire [5 : 0] s_axi_wid
            .s_axi_wdata          (axi_wdata      [jj] ),  //  input wire [255 : 0] s_axi_wdata
            .s_axi_wstrb          (axi_wstrb      [jj] ),  //  input wire [31 : 0] s_axi_wstrb
            .s_axi_wlast          (axi_wlast      [jj] ),  //  input wire s_axi_wlast
            .s_axi_wvalid         (axi_wvalid     [jj] ),  //  input wire s_axi_wvalid
            .s_axi_wready         (axi_wready     [jj] ),  //  output wire s_axi_wready
            .s_axi_bid            (axi_bid        [jj] ),  //  output wire [5 : 0] s_axi_bid
            .s_axi_bresp          (axi_bresp      [jj] ),  //  output wire [1 : 0] s_axi_bresp
            .s_axi_bvalid         (axi_bvalid     [jj] ),  //  output wire s_axi_bvalid
            .s_axi_bready         (axi_bready     [jj] ),  //  input wire s_axi_bready
            .s_axi_arid           (axi_arid       [jj] ),  //  input wire [5 : 0] s_axi_arid
            .s_axi_araddr         (axi_araddr     [jj] ),  //  input wire [33 : 0] s_axi_araddr
            .s_axi_arlen          (axi_arlen      [jj] ),  //  input wire [3 : 0] s_axi_arlen
            .s_axi_arsize         (axi_arsize     [jj] ),  //  input wire [2 : 0] s_axi_arsize
            .s_axi_arburst        (DEF_AWBURST         ),  //  input wire [1 : 0] s_axi_arburst
            .s_axi_arlock         (DEF_AWLOCK          ),  //  input wire [1 : 0] s_axi_arlock
            .s_axi_arcache        (DEF_AWCACHE         ),  //  input wire [3 : 0] s_axi_arcache
            .s_axi_arprot         (DEF_AWPROT          ),  //  input wire [2 : 0] s_axi_arprot
            .s_axi_arqos          (DEF_AWQOS           ),  //  input wire [3 : 0] s_axi_arqos
            .s_axi_arvalid        (axi_arvalid    [jj] ),  //  input wire s_axi_arvalid
            .s_axi_arready        (axi_arready    [jj] ),  //  output wire s_axi_arready
            .s_axi_rid            (axi_rid        [jj] ),  //  output wire [5 : 0] s_axi_rid
            .s_axi_rdata          (axi_rdata      [jj] ),  //  output wire [255 : 0] s_axi_rdata
            .s_axi_rresp          (axi_rresp      [jj] ),  //  output wire [1 : 0] s_axi_rresp
            .s_axi_rlast          (axi_rlast      [jj] ),  //  output wire s_axi_rlast
            .s_axi_rvalid         (axi_rvalid     [jj] ),  //  output wire s_axi_rvalid
            .s_axi_rready         (axi_rready     [jj] ),  //  input wire s_axi_rready
            .m_axi_awid           (q1_axi_awid    [jj] ),  //  output wire [5 : 0] m_axi_awid
            .m_axi_awaddr         (q1_axi_awaddr  [jj] ),  //  output wire [33 : 0] m_axi_awaddr
            .m_axi_awlen          (q1_axi_awlen   [jj] ),  //  output wire [3 : 0] m_axi_awlen
            .m_axi_awsize         (q1_axi_awsize  [jj] ),  //  output wire [2 : 0] m_axi_awsize
            .m_axi_awburst        (q1_axi_awburst [jj] ),  //  output wire [1 : 0] m_axi_awburst
            .m_axi_awlock         (                    ),  //  output wire [1 : 0] m_axi_awlock
            .m_axi_awcache        (                    ),  //  output wire [3 : 0] m_axi_awcache
            .m_axi_awprot         (                    ),  //  output wire [2 : 0] m_axi_awprot
            .m_axi_awqos          (                    ),  //  output wire [3 : 0] m_axi_awqos
            .m_axi_awvalid        (q1_axi_awvalid [jj] ),  //  output wire m_axi_awvalid
            .m_axi_awready        (q1_axi_awready [jj] ),  //  input wire m_axi_awready
            .m_axi_wid            (                    ),  //  output wire [5 : 0] m_axi_wid
            .m_axi_wdata          (q1_axi_wdata   [jj] ),  //  output wire [255 : 0] m_axi_wdata
            .m_axi_wstrb          (q1_axi_wstrb   [jj] ),  //  output wire [31 : 0] m_axi_wstrb
            .m_axi_wlast          (q1_axi_wlast   [jj] ),  //  output wire m_axi_wlast
            .m_axi_wvalid         (q1_axi_wvalid  [jj] ),  //  output wire m_axi_wvalid
            .m_axi_wready         (q1_axi_wready  [jj] ),  //  input wire m_axi_wready
            .m_axi_bid            (q1_axi_bid     [jj] ),  //  input wire [5 : 0] m_axi_bid
            .m_axi_bresp          (q1_axi_bresp   [jj] ),  //  input wire [1 : 0] m_axi_bresp
            .m_axi_bvalid         (q1_axi_bvalid  [jj] ),  //  input wire m_axi_bvalid
            .m_axi_bready         (q1_axi_bready  [jj] ),  //  output wire m_axi_bready
            .m_axi_arid           (q1_axi_arid    [jj] ),  //  output wire [5 : 0] m_axi_arid
            .m_axi_araddr         (q1_axi_araddr  [jj] ),  //  output wire [33 : 0] m_axi_araddr
            .m_axi_arlen          (q1_axi_arlen   [jj] ),  //  output wire [3 : 0] m_axi_arlen
            .m_axi_arsize         (q1_axi_arsize  [jj] ),  //  output wire [2 : 0] m_axi_arsize
            .m_axi_arburst        (q1_axi_arburst [jj] ),  //  output wire [1 : 0] m_axi_arburst
            .m_axi_arlock         (                    ),  //  output wire [1 : 0] m_axi_arlock
            .m_axi_arcache        (                    ),  //  output wire [3 : 0] m_axi_arcache
            .m_axi_arprot         (                    ),  //  output wire [2 : 0] m_axi_arprot
            .m_axi_arqos          (                    ),  //  output wire [3 : 0] m_axi_arqos
            .m_axi_arvalid        (q1_axi_arvalid [jj] ),  //  output wire m_axi_arvalid
            .m_axi_arready        (q1_axi_arready [jj] ),  //  input wire m_axi_arready
            .m_axi_rid            (q1_axi_rid     [jj] ),  //  input wire [5 : 0] m_axi_rid
            .m_axi_rdata          (q1_axi_rdata   [jj] ),  //  input wire [255 : 0] m_axi_rdata
            .m_axi_rresp          (q1_axi_rresp   [jj] ),  //  input wire [1 : 0] m_axi_rresp
            .m_axi_rlast          (q1_axi_rlast   [jj] ),  //  input wire m_axi_rlast
            .m_axi_rvalid         (q1_axi_rvalid  [jj] ),  //  input wire m_axi_rvalid
            .m_axi_rready         (q1_axi_rready  [jj] )   //  output wire m_axi_rready
            );

         //
         // AXI3 Reg Slice2
         //
         cl_axi3_256b_reg_slice CL_AXI3_HBM_REG_SLC2_I
           (
            .aclk                 (clk_hbm                ),  //  input wire aclk
            .aresetn              (rst_hbm_n              ),  //  input wire aresetn
            .s_axi_awid           (q1_axi_awid      [jj]  ),  //  input wire [5 : 0] s_axi_awid
            .s_axi_awaddr         (q1_axi_awaddr    [jj]  ),  //  input wire [33 : 0] s_axi_awaddr
            .s_axi_awlen          (q1_axi_awlen     [jj]  ),  //  input wire [3 : 0] s_axi_awlen
            .s_axi_awsize         (q1_axi_awsize    [jj]  ),  //  input wire [2 : 0] s_axi_awsize
            .s_axi_awburst        (q1_axi_awburst   [jj]  ),  //  input wire [1 : 0] s_axi_awburst
            .s_axi_awlock         (DEF_AWLOCK             ),  //  input wire [1 : 0] s_axi_awlock
            .s_axi_awcache        (DEF_AWCACHE            ),  //  input wire [3 : 0] s_axi_awcache
            .s_axi_awprot         (DEF_AWPROT             ),  //  input wire [2 : 0] s_axi_awprot
            .s_axi_awqos          (DEF_AWQOS              ),  //  input wire [3 : 0] s_axi_awqos
            .s_axi_awvalid        (q1_axi_awvalid   [jj]  ),  //  input wire s_axi_awvalid
            .s_axi_awready        (q1_axi_awready   [jj]  ),  //  output wire s_axi_awready
            .s_axi_wid            (6'd0                   ),  //  input wire [5 : 0] s_axi_wid
            .s_axi_wdata          (q1_axi_wdata     [jj]  ),  //  input wire [255 : 0] s_axi_wdata
            .s_axi_wstrb          (q1_axi_wstrb     [jj]  ),  //  input wire [31 : 0] s_axi_wstrb
            .s_axi_wlast          (q1_axi_wlast     [jj]  ),  //  input wire s_axi_wlast
            .s_axi_wvalid         (q1_axi_wvalid    [jj]  ),  //  input wire s_axi_wvalid
            .s_axi_wready         (q1_axi_wready    [jj]  ),  //  output wire s_axi_wready
            .s_axi_bid            (q1_axi_bid       [jj]  ),  //  output wire [5 : 0] s_axi_bid
            .s_axi_bresp          (q1_axi_bresp     [jj]  ),  //  output wire [1 : 0] s_axi_bresp
            .s_axi_bvalid         (q1_axi_bvalid    [jj]  ),  //  output wire s_axi_bvalid
            .s_axi_bready         (q1_axi_bready    [jj]  ),  //  input wire s_axi_bready
            .s_axi_arid           (q1_axi_arid      [jj]  ),  //  input wire [5 : 0] s_axi_arid
            .s_axi_araddr         (q1_axi_araddr    [jj]  ),  //  input wire [33 : 0] s_axi_araddr
            .s_axi_arlen          (q1_axi_arlen     [jj]  ),  //  input wire [3 : 0] s_axi_arlen
            .s_axi_arsize         (q1_axi_arsize    [jj]  ),  //  input wire [2 : 0] s_axi_arsize
            .s_axi_arburst        (DEF_AWBURST            ),  //  input wire [1 : 0] s_axi_arburst
            .s_axi_arlock         (DEF_AWLOCK             ),  //  input wire [1 : 0] s_axi_arlock
            .s_axi_arcache        (DEF_AWCACHE            ),  //  input wire [3 : 0] s_axi_arcache
            .s_axi_arprot         (DEF_AWPROT             ),  //  input wire [2 : 0] s_axi_arprot
            .s_axi_arqos          (DEF_AWQOS              ),  //  input wire [3 : 0] s_axi_arqos
            .s_axi_arvalid        (q1_axi_arvalid   [jj]  ),  //  input wire s_axi_arvalid
            .s_axi_arready        (q1_axi_arready   [jj]  ),  //  output wire s_axi_arready
            .s_axi_rid            (q1_axi_rid       [jj]  ),  //  output wire [5 : 0] s_axi_rid
            .s_axi_rdata          (q1_axi_rdata     [jj]  ),  //  output wire [255 : 0] s_axi_rdata
            .s_axi_rresp          (q1_axi_rresp     [jj]  ),  //  output wire [1 : 0] s_axi_rresp
            .s_axi_rlast          (q1_axi_rlast     [jj]  ),  //  output wire s_axi_rlast
            .s_axi_rvalid         (q1_axi_rvalid    [jj]  ),  //  output wire s_axi_rvalid
            .s_axi_rready         (q1_axi_rready    [jj]  ),  //  input wire s_axi_rready
            .m_axi_awid           (q2_axi_awid      [jj]  ),  //  output wire [5 : 0] m_axi_awid
            .m_axi_awaddr         (q2_axi_awaddr    [jj]  ),  //  output wire [33 : 0] m_axi_awaddr
            .m_axi_awlen          (q2_axi_awlen     [jj]  ),  //  output wire [3 : 0] m_axi_awlen
            .m_axi_awsize         (q2_axi_awsize    [jj]  ),  //  output wire [2 : 0] m_axi_awsize
            .m_axi_awburst        (q2_axi_awburst   [jj]  ),  //  output wire [1 : 0] m_axi_awburst
            .m_axi_awlock         (                       ),  //  output wire [1 : 0] m_axi_awlock
            .m_axi_awcache        (                       ),  //  output wire [3 : 0] m_axi_awcache
            .m_axi_awprot         (                       ),  //  output wire [2 : 0] m_axi_awprot
            .m_axi_awqos          (                       ),  //  output wire [3 : 0] m_axi_awqos
            .m_axi_awvalid        (q2_axi_awvalid   [jj]  ),  //  output wire m_axi_awvalid
            .m_axi_awready        (q2_axi_awready   [jj]  ),  //  input wire m_axi_awready
            .m_axi_wid            (                       ),  //  output wire [5 : 0] m_axi_wid
            .m_axi_wdata          (q2_axi_wdata     [jj]  ),  //  output wire [255 : 0] m_axi_wdata
            .m_axi_wstrb          (q2_axi_wstrb     [jj]  ),  //  output wire [31 : 0] m_axi_wstrb
            .m_axi_wlast          (q2_axi_wlast     [jj]  ),  //  output wire m_axi_wlast
            .m_axi_wvalid         (q2_axi_wvalid    [jj]  ),  //  output wire m_axi_wvalid
            .m_axi_wready         (q2_axi_wready    [jj]  ),  //  input wire m_axi_wready
            .m_axi_bid            (q2_axi_bid       [jj]  ),  //  input wire [5 : 0] m_axi_bid
            .m_axi_bresp          (q2_axi_bresp     [jj]  ),  //  input wire [1 : 0] m_axi_bresp
            .m_axi_bvalid         (q2_axi_bvalid    [jj]  ),  //  input wire m_axi_bvalid
            .m_axi_bready         (q2_axi_bready    [jj]  ),  //  output wire m_axi_bready
            .m_axi_arid           (q2_axi_arid      [jj]  ),  //  output wire [5 : 0] m_axi_arid
            .m_axi_araddr         (q2_axi_araddr    [jj]  ),  //  output wire [33 : 0] m_axi_araddr
            .m_axi_arlen          (q2_axi_arlen     [jj]  ),  //  output wire [3 : 0] m_axi_arlen
            .m_axi_arsize         (q2_axi_arsize    [jj]  ),  //  output wire [2 : 0] m_axi_arsize
            .m_axi_arburst        (q2_axi_arburst   [jj]  ),  //  output wire [1 : 0] m_axi_arburst
            .m_axi_arlock         (                       ),  //  output wire [1 : 0] m_axi_arlock
            .m_axi_arcache        (                       ),  //  output wire [3 : 0] m_axi_arcache
            .m_axi_arprot         (                       ),  //  output wire [2 : 0] m_axi_arprot
            .m_axi_arqos          (                       ),  //  output wire [3 : 0] m_axi_arqos
            .m_axi_arvalid        (q2_axi_arvalid   [jj]  ),  //  output wire m_axi_arvalid
            .m_axi_arready        (q2_axi_arready   [jj]  ),  //  input wire m_axi_arready
            .m_axi_rid            (q2_axi_rid       [jj]  ),  //  input wire [5 : 0] m_axi_rid
            .m_axi_rdata          (q2_axi_rdata     [jj]  ),  //  input wire [255 : 0] m_axi_rdata
            .m_axi_rresp          (q2_axi_rresp     [jj]  ),  //  input wire [1 : 0] m_axi_rresp
            .m_axi_rlast          (q2_axi_rlast     [jj]  ),  //  input wire m_axi_rlast
            .m_axi_rvalid         (q2_axi_rvalid    [jj]  ),  //  input wire m_axi_rvalid
            .m_axi_rready         (q2_axi_rready    [jj]  )   //  output wire m_axi_rready
            );

         //
         // AXI3 Reg Slice3
         //
         cl_axi3_256b_reg_slice CL_AXI3_HBM_REG_SLC3_I
           (
            .aclk                 (clk_hbm               ),  //  input wire aclk
            .aresetn              (rst_hbm_n             ),  //  input wire aresetn
            .s_axi_awid           (q2_axi_awid      [jj] ),  //  input wire [5 : 0] s_axi_awid
            .s_axi_awaddr         (q2_axi_awaddr    [jj] ),  //  input wire [33 : 0] s_axi_awaddr
            .s_axi_awlen          (q2_axi_awlen     [jj] ),  //  input wire [3 : 0] s_axi_awlen
            .s_axi_awsize         (q2_axi_awsize    [jj] ),  //  input wire [2 : 0] s_axi_awsize
            .s_axi_awburst        (q2_axi_awburst   [jj] ),  //  input wire [1 : 0] s_axi_awburst
            .s_axi_awlock         (DEF_AWLOCK            ),  //  input wire [1 : 0] s_axi_awlock
            .s_axi_awcache        (DEF_AWCACHE           ),  //  input wire [3 : 0] s_axi_awcache
            .s_axi_awprot         (DEF_AWPROT            ),  //  input wire [2 : 0] s_axi_awprot
            .s_axi_awqos          (DEF_AWQOS             ),  //  input wire [3 : 0] s_axi_awqos
            .s_axi_awvalid        (q2_axi_awvalid   [jj] ),  //  input wire s_axi_awvalid
            .s_axi_awready        (q2_axi_awready   [jj] ),  //  output wire s_axi_awready
            .s_axi_wid            (6'd0                  ),  //  input wire [5 : 0] s_axi_wid
            .s_axi_wdata          (q2_axi_wdata     [jj] ),  //  input wire [255 : 0] s_axi_wdata
            .s_axi_wstrb          (q2_axi_wstrb     [jj] ),  //  input wire [31 : 0] s_axi_wstrb
            .s_axi_wlast          (q2_axi_wlast     [jj] ),  //  input wire s_axi_wlast
            .s_axi_wvalid         (q2_axi_wvalid    [jj] ),  //  input wire s_axi_wvalid
            .s_axi_wready         (q2_axi_wready    [jj] ),  //  output wire s_axi_wready
            .s_axi_bid            (q2_axi_bid       [jj] ),  //  output wire [5 : 0] s_axi_bid
            .s_axi_bresp          (q2_axi_bresp     [jj] ),  //  output wire [1 : 0] s_axi_bresp
            .s_axi_bvalid         (q2_axi_bvalid    [jj] ),  //  output wire s_axi_bvalid
            .s_axi_bready         (q2_axi_bready    [jj] ),  //  input wire s_axi_bready
            .s_axi_arid           (q2_axi_arid      [jj] ),  //  input wire [5 : 0] s_axi_arid
            .s_axi_araddr         (q2_axi_araddr    [jj] ),  //  input wire [33 : 0] s_axi_araddr
            .s_axi_arlen          (q2_axi_arlen     [jj] ),  //  input wire [3 : 0] s_axi_arlen
            .s_axi_arsize         (q2_axi_arsize    [jj] ),  //  input wire [2 : 0] s_axi_arsize
            .s_axi_arburst        (DEF_AWBURST           ),  //  input wire [1 : 0] s_axi_arburst
            .s_axi_arlock         (DEF_AWLOCK            ),  //  input wire [1 : 0] s_axi_arlock
            .s_axi_arcache        (DEF_AWCACHE           ),  //  input wire [3 : 0] s_axi_arcache
            .s_axi_arprot         (DEF_AWPROT            ),  //  input wire [2 : 0] s_axi_arprot
            .s_axi_arqos          (DEF_AWQOS             ),  //  input wire [3 : 0] s_axi_arqos
            .s_axi_arvalid        (q2_axi_arvalid   [jj] ),  //  input wire s_axi_arvalid
            .s_axi_arready        (q2_axi_arready   [jj] ),  //  output wire s_axi_arready
            .s_axi_rid            (q2_axi_rid       [jj] ),  //  output wire [5 : 0] s_axi_rid
            .s_axi_rdata          (q2_axi_rdata     [jj] ),  //  output wire [255 : 0] s_axi_rdata
            .s_axi_rresp          (q2_axi_rresp     [jj] ),  //  output wire [1 : 0] s_axi_rresp
            .s_axi_rlast          (q2_axi_rlast     [jj] ),  //  output wire s_axi_rlast
            .s_axi_rvalid         (q2_axi_rvalid    [jj] ),  //  output wire s_axi_rvalid
            .s_axi_rready         (q2_axi_rready    [jj] ),  //  input wire s_axi_rready
            .m_axi_awid           (o_axi_awid       [jj] ),  //  output wire [5 : 0] m_axi_awid
            .m_axi_awaddr         (o_axi_awaddr     [jj] ),  //  output wire [33 : 0] m_axi_awaddr
            .m_axi_awlen          (o_axi_awlen      [jj] ),  //  output wire [3 : 0] m_axi_awlen
            .m_axi_awsize         (o_axi_awsize     [jj] ),  //  output wire [2 : 0] m_axi_awsize
            .m_axi_awburst        (o_axi_awburst    [jj] ),  //  output wire [1 : 0] m_axi_awburst
            .m_axi_awlock         (                      ),  //  output wire [1 : 0] m_axi_awlock
            .m_axi_awcache        (                      ),  //  output wire [3 : 0] m_axi_awcache
            .m_axi_awprot         (                      ),  //  output wire [2 : 0] m_axi_awprot
            .m_axi_awqos          (                      ),  //  output wire [3 : 0] m_axi_awqos
            .m_axi_awvalid        (o_axi_awvalid    [jj] ),  //  output wire m_axi_awvalid
            .m_axi_awready        (i_axi_awready    [jj] ),  //  input wire m_axi_awready
            .m_axi_wid            (                      ),  //  output wire [5 : 0] m_axi_wid
            .m_axi_wdata          (o_axi_wdata      [jj] ),  //  output wire [255 : 0] m_axi_wdata
            .m_axi_wstrb          (o_axi_wstrb      [jj] ),  //  output wire [31 : 0] m_axi_wstrb
            .m_axi_wlast          (o_axi_wlast      [jj] ),  //  output wire m_axi_wlast
            .m_axi_wvalid         (o_axi_wvalid     [jj] ),  //  output wire m_axi_wvalid
            .m_axi_wready         (i_axi_wready     [jj] ),  //  input wire m_axi_wready
            .m_axi_bid            (i_axi_bid        [jj] ),  //  input wire [5 : 0] m_axi_bid
            .m_axi_bresp          (i_axi_bresp      [jj] ),  //  input wire [1 : 0] m_axi_bresp
            .m_axi_bvalid         (i_axi_bvalid     [jj] ),  //  input wire m_axi_bvalid
            .m_axi_bready         (o_axi_bready     [jj] ),  //  output wire m_axi_bready
            .m_axi_arid           (o_axi_arid       [jj] ),  //  output wire [5 : 0] m_axi_arid
            .m_axi_araddr         (o_axi_araddr     [jj] ),  //  output wire [33 : 0] m_axi_araddr
            .m_axi_arlen          (o_axi_arlen      [jj] ),  //  output wire [3 : 0] m_axi_arlen
            .m_axi_arsize         (o_axi_arsize     [jj] ),  //  output wire [2 : 0] m_axi_arsize
            .m_axi_arburst        (o_axi_arburst    [jj] ),  //  output wire [1 : 0] m_axi_arburst
            .m_axi_arlock         (                      ),  //  output wire [1 : 0] m_axi_arlock
            .m_axi_arcache        (                      ),  //  output wire [3 : 0] m_axi_arcache
            .m_axi_arprot         (                      ),  //  output wire [2 : 0] m_axi_arprot
            .m_axi_arqos          (                      ),  //  output wire [3 : 0] m_axi_arqos
            .m_axi_arvalid        (o_axi_arvalid    [jj] ),  //  output wire m_axi_arvalid
            .m_axi_arready        (i_axi_arready    [jj] ),  //  input wire m_axi_arready
            .m_axi_rid            (i_axi_rid        [jj] ),  //  input wire [5 : 0] m_axi_rid
            .m_axi_rdata          (i_axi_rdata      [jj] ),  //  input wire [255 : 0] m_axi_rdata
            .m_axi_rresp          (i_axi_rresp      [jj] ),  //  input wire [1 : 0] m_axi_rresp
            .m_axi_rlast          (i_axi_rlast      [jj] ),  //  input wire m_axi_rlast
            .m_axi_rvalid         (i_axi_rvalid     [jj] ),  //  input wire m_axi_rvalid
            .m_axi_rready         (o_axi_rready     [jj] )   //  output wire m_axi_rready
            );
      end : HBM_AXI3_I //}
   endgenerate //}

endmodule // cl_hbm_perf_kernel
