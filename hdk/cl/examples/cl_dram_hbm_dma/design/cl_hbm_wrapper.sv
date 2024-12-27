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


// ============================================================================
// HBM Wrapper
// - Wraper for HBM IP
// - Implements an MMCM to generate 100MHz and 450MHz clock for the HBM IP.
// - AXI interface run @450MHz.
// - Parameterized number of AXI interfaces.
//   User can choose to connect upto 32 AXI interfaces to the HBM.
// - User can connect using AXI4 Protocol, and leverage AXI4-to-AXI3 protocol convertor
//   by setting parameter AXI4_INTERFACE=1
// - Unused HBM ports are automatically tied off.
// - Stats interface to reset the HBM, status check for HBM initialization.
//------------------------------------------
// HBM Stats Interface Reset Routine:
// // Issue HBM soft reset
// write 0x1 @ addr 0x00
// write 0x0 @ addr 0x00
// // Poll for lock
// poll bits[3:1] = 3'b111 @ addr 0x00
// ============================================================================

module cl_hbm_wrapper
  #(
    parameter NUM_OF_AXI_PORTS           = 1,                        // Number of AXI ports to connect to the HBM
    parameter AXI4_INTERFACE             = 0,                        // 1 = Instantiate Xilinx AXI4-to-AXI3 Protocol Convertor.
    parameter AXLEN_WIDTH                = AXI4_INTERFACE ? 8 : 4    // width of axlen. For AXI4 interface this must be 8, for AXI3 interface this must be 4.
    )
   (
    input logic                          apb_clk,       // Input clk 100 MHz

    input logic                          i_clk_250m,   // Input clk 250 MHz
    input logic                          i_rst_250m_n, // Input reset syncd to i_clk_250m

    output logic                         o_clk_450m,   // Output clk 450MHz. This is the clock for AXI interfaces.
    output logic                         o_rst_450m_n, // Output reset syncd to o_clk_450m

    output logic                         o_clk_100m,   // Output clk 100Mhz. This is the APB clock used by HBM's APB interface.
    output logic                         o_rst_100m_n, // Output clk 100Mhz. Reset synchronized to 100MHz clock

    // AXI3/4 bus to HBM. These must be in o_clk_450m clk domain
    input  logic  [33 : 0]               i_axi_araddr   [0:NUM_OF_AXI_PORTS-1],
    input  logic  [1 : 0]                i_axi_arburst  [0:NUM_OF_AXI_PORTS-1],
    input  logic  [5 : 0]                i_axi_arid     [0:NUM_OF_AXI_PORTS-1],
    input  logic  [AXLEN_WIDTH-1 : 0]    i_axi_arlen    [0:NUM_OF_AXI_PORTS-1],
    input  logic  [2 : 0]                i_axi_arsize   [0:NUM_OF_AXI_PORTS-1],
    input  logic                         i_axi_arvalid  [0:NUM_OF_AXI_PORTS-1],
    input  logic  [33 : 0]               i_axi_awaddr   [0:NUM_OF_AXI_PORTS-1],
    input  logic  [1 : 0]                i_axi_awburst  [0:NUM_OF_AXI_PORTS-1],
    input  logic  [5 : 0]                i_axi_awid     [0:NUM_OF_AXI_PORTS-1],
    input  logic  [AXLEN_WIDTH-1 : 0]    i_axi_awlen    [0:NUM_OF_AXI_PORTS-1],
    input  logic  [2 : 0]                i_axi_awsize   [0:NUM_OF_AXI_PORTS-1],
    input  logic                         i_axi_awvalid  [0:NUM_OF_AXI_PORTS-1],
    input  logic                         i_axi_rready   [0:NUM_OF_AXI_PORTS-1],
    input  logic                         i_axi_bready   [0:NUM_OF_AXI_PORTS-1],
    input  logic  [255 : 0]              i_axi_wdata    [0:NUM_OF_AXI_PORTS-1],
    input  logic                         i_axi_wlast    [0:NUM_OF_AXI_PORTS-1],
    input  logic  [31 : 0]               i_axi_wstrb    [0:NUM_OF_AXI_PORTS-1],
    input  logic                         i_axi_wvalid   [0:NUM_OF_AXI_PORTS-1],
    output logic                         o_axi_arready  [0:NUM_OF_AXI_PORTS-1],
    output logic                         o_axi_awready  [0:NUM_OF_AXI_PORTS-1],
    output logic  [255 : 0]              o_axi_rdata    [0:NUM_OF_AXI_PORTS-1],
    output logic  [5 : 0]                o_axi_rid      [0:NUM_OF_AXI_PORTS-1],
    output logic                         o_axi_rlast    [0:NUM_OF_AXI_PORTS-1],
    output logic  [1 : 0]                o_axi_rresp    [0:NUM_OF_AXI_PORTS-1],
    output logic                         o_axi_rvalid   [0:NUM_OF_AXI_PORTS-1],
    output logic                         o_axi_wready   [0:NUM_OF_AXI_PORTS-1],
    output logic  [5 : 0]                o_axi_bid      [0:NUM_OF_AXI_PORTS-1],
    output logic  [1 : 0]                o_axi_bresp    [0:NUM_OF_AXI_PORTS-1],
    output logic                         o_axi_bvalid   [0:NUM_OF_AXI_PORTS-1],

    // Required per-stack APB interfaces to the shell
    input logic                          i_hbm_apb_preset_n_1,
    output logic [21:0]                  o_hbm_apb_paddr_1,
    output logic [2:0]                   o_hbm_apb_pprot_1,
    output logic                         o_hbm_apb_psel_1,
    output logic                         o_hbm_apb_penable_1,
    output logic                         o_hbm_apb_pwrite_1,
    output logic [31:0]                  o_hbm_apb_pwdata_1,
    output logic [3:0]                   o_hbm_apb_pstrb_1,
    output logic                         o_hbm_apb_pready_1,
    output logic [31:0]                  o_hbm_apb_prdata_1,
    output logic                         o_hbm_apb_pslverr_1,

    input logic                          i_hbm_apb_preset_n_0,
    output logic [21:0]                  o_hbm_apb_paddr_0,
    output logic [2:0]                   o_hbm_apb_pprot_0,
    output logic                         o_hbm_apb_psel_0,
    output logic                         o_hbm_apb_penable_0,
    output logic                         o_hbm_apb_pwrite_0,
    output logic [31:0]                  o_hbm_apb_pwdata_0,
    output logic [3:0]                   o_hbm_apb_pstrb_0,
    output logic                         o_hbm_apb_pready_0,
    output logic [31:0]                  o_hbm_apb_prdata_0,
    output logic                         o_hbm_apb_pslverr_0,

    cfg_bus_t.slave                      hbm_stat_bus,                          // CFG Stats bus to HBM (in i_clk_250m domain)
    output logic [7:0]                   o_cl_sh_hbm_stat_int = '0,             // output [7:0] No interrupts from HBM
    output logic                         o_hbm_ready = '0                       // output HBM Init Ready (in clk 250mhz domain)
   );

   //==================================================================
   // local signals
   //==================================================================
   localparam   HBM_DATA_WIDTH  = 256;
   localparam   ADDR_WIDTH      = 34;
   localparam   ID_WIDTH        = 6;

   localparam   DEF_AWLOCK      = 1'd0;
   localparam   DEF_AWCACHE     = 4'h1; // Device bufferable, non-cacheable
   localparam   DEF_AWPROT      = 3'd0;
   localparam   DEF_AWREGION    = 4'd0;
   localparam   DEF_AWQOS       = 4'd0;

   localparam   DEF_AXSIZE      = 3'($clog2(HBM_DATA_WIDTH/8));
   localparam   DEF_PARITY      = 32'd0;

   logic        mmcm_lock;
   logic        cfg_hbm_reset = '0;
   logic [1:0]  hbm_ready_q;
   logic [1:0]  apb_complete;

  //=================================================================
  // Pipe reset for better timing
  //=================================================================
  logic axi_clk;
  logic rst_n;
  logic rst_250m_n_pipe;

  lib_pipe #(.WIDTH(1), .STAGES(4)) SLR0_PIPE_RST_N (.clk(clk), .rst_n(1'b1), .in_bus(i_rst_250m_n), .out_bus(rst_250m_n_pipe));

  assign clk = i_clk_250m;
  assign rst_n = rst_250m_n_pipe;

  //==================================================================
  // Synchronize resets
  //===================================================================
  logic apb_rst_sync_n;
  logic apb_rst_n;
  logic axi_rst_sync_n;
  logic axi_rst_n;

  // APB clock reset synchronization
  xpm_cdc_async_rst
  #(
    .DEST_SYNC_FF   (4),
    .INIT_SYNC_FF   (0),
    .RST_ACTIVE_HIGH(0)
  )
  CDC_ASYNC_RST_APB_N
  (
    .src_arst       (rst_n & ~cfg_hbm_reset),
    .dest_clk       (apb_clk),
    .dest_arst      (apb_rst_sync_n)
  );

  lib_pipe #(.WIDTH(1), .STAGES(4)) PIPE_APB_RST_N (.clk(apb_clk), .rst_n(1'b1), .in_bus(apb_rst_sync_n), .out_bus(apb_rst_n));

  // AXI clock reset synchronization
  xpm_cdc_async_rst
  #(
    .DEST_SYNC_FF   (4),
    .INIT_SYNC_FF   (0),
    .RST_ACTIVE_HIGH(0)
  )
  CDC_ASYNC_RST_AXI_N
  (
    .src_arst       (apb_rst_sync_n),
    .dest_clk       (axi_clk),
    .dest_arst      (axi_rst_sync_n)
  );

  lib_pipe #(.WIDTH(1), .STAGES(4)) SLR0_AXI_RST_N (.clk(axi_clk), .rst_n(1'b1), .in_bus(axi_rst_sync_n), .out_bus(axi_rst_n));

  //==================================================================
  // HBM requires following clocks:
  // - 100 MHz REF CLK, AND APB CLOCKS
  // - 450 MHz AXI CLK
  //==================================================================
  cl_hbm_mmcm HBM_MMCM_I
  (
    .clk_in1  (apb_clk         ),     // input clk_in1
    .clk_out1 (axi_clk         ),     // output clk_out1 = 450MHz
    .locked   (mmcm_lock       )      // output locked
  );

  //
  // Clock and reset outputs
  //
  always_comb begin : CLK_OUT
    o_clk_450m   = axi_clk;
    o_rst_450m_n = axi_rst_n;
    o_clk_100m   = apb_clk;
    o_rst_100m_n = apb_rst_n;
  end : CLK_OUT

   //==================================================================
   // HBM CSRs
   //==================================================================
   //HBM CFG BUS
   cfg_bus_t hbm_cfg_bus_q();
   always_ff @(posedge clk)
     if (!rst_n) begin
        hbm_cfg_bus_q.wr  <= 1'd0;
        hbm_cfg_bus_q.rd  <= 1'd0;
        hbm_cfg_bus_q.ack <= 1'd0;
     end
     else begin
        hbm_cfg_bus_q.wr    <= hbm_stat_bus.wr;
        hbm_cfg_bus_q.rd    <= hbm_stat_bus.rd;
        hbm_cfg_bus_q.ack   <= (hbm_cfg_bus_q.wr | hbm_cfg_bus_q.rd);
        hbm_cfg_bus_q.addr  <= hbm_stat_bus.addr;
        hbm_cfg_bus_q.wdata <= hbm_stat_bus.wdata;
     end // else: !if(!sync_rst_n)

   assign hbm_stat_bus.ack = hbm_cfg_bus_q.ack;
   assign hbm_stat_bus.rdata = hbm_cfg_bus_q.rdata;

   //
   // HBM CSRs :
   // 0x00 : bit[0]   = SW reset for HBM (R/W)
   //                   1: Assert Reset for HBM
   //                   0: Deassert Reset for HBM
   //        bit[2:1] = HBM initialized (R/O)
   //        bit[3]   = 100MHz MMCM locked (R/O)
   //
   always_ff @(posedge clk)
     if (hbm_cfg_bus_q.wr && !hbm_cfg_bus_q.ack && (hbm_cfg_bus_q.addr[7:0] == '0))
       cfg_hbm_reset <= hbm_cfg_bus_q.wdata[0];

   // HBM CSR Read datapath
   always_ff @(posedge clk)
     if (hbm_cfg_bus_q.addr[7:0] == '0)
       hbm_cfg_bus_q.rdata <= 32'({1'b0,       // bit[3]
                                   hbm_ready_q,     // bit[2:1]
                                   cfg_hbm_reset}); // bit[0]
     else
       hbm_cfg_bus_q.rdata <= 32'hdead_dead;

   //==================================================================
   // Structure for AXI4/AXI3 bus
   //==================================================================
   typedef struct {
      logic [ADDR_WIDTH-1 : 0]  araddr  ;
      logic [1 : 0]             arburst ;
      logic [ID_WIDTH-1 : 0]    arid    ;
      logic [AXLEN_WIDTH-1 : 0] arlen   ;
      logic [2 : 0]             arsize  ;
      logic                     arvalid ;
      logic [ADDR_WIDTH-1 : 0]  awaddr  ;
      logic [1 : 0]             awburst ;
      logic [ID_WIDTH-1 : 0]    awid    ;
      logic [AXLEN_WIDTH-1 : 0] awlen   ;
      logic [2 : 0]             awsize  ;
      logic                     awvalid ;
      logic                     rready  ;
      logic                     bready  ;
      logic [ID_WIDTH-1:0]      wid;
      logic [255 : 0]           wdata   ;
      logic                     wlast   ;
      logic [31 : 0]            wstrb   ;
      logic                     wvalid  ;
      logic                     arready ;
      logic                     awready ;
      logic [255 : 0]           rdata   ;
      logic [ID_WIDTH-1 : 0]    rid     ;
      logic                     rlast   ;
      logic [1 : 0]             rresp   ;
      logic                     rvalid  ;
      logic                     wready  ;
      logic [ID_WIDTH-1 : 0]    bid     ;
      logic [1 : 0]             bresp   ;
      logic                     bvalid  ;
   } st_axi_bus_t;


   //==========================================================================
   // AXI4 to AXI3 Protocol convertor
   //==========================================================================
   st_axi_bus_t st_axi3_bus [0:NUM_OF_AXI_PORTS-1];
   st_axi_bus_t st_hbm_axi3[0:31];

   genvar                       gg;
   generate //{
      //
      // Convert input/output axi bus to structure for convenience
      //
      st_axi_bus_t st_axi_bus [0:NUM_OF_AXI_PORTS-1];
      for (gg = 0; gg < NUM_OF_AXI_PORTS; gg++) begin : CNV_TO_AXI_STRUCT_I //{
         assign st_axi_bus[gg].araddr    = i_axi_araddr  [gg];
         assign st_axi_bus[gg].arburst   = i_axi_arburst [gg];
         assign st_axi_bus[gg].arid      = i_axi_arid    [gg];
         assign st_axi_bus[gg].arlen     = i_axi_arlen   [gg];
         assign st_axi_bus[gg].arsize    = i_axi_arsize  [gg];
         assign st_axi_bus[gg].arvalid   = i_axi_arvalid [gg];
         assign st_axi_bus[gg].awaddr    = i_axi_awaddr  [gg];
         assign st_axi_bus[gg].awburst   = i_axi_awburst [gg];
         assign st_axi_bus[gg].awid      = i_axi_awid    [gg];
         assign st_axi_bus[gg].awlen     = i_axi_awlen   [gg];
         assign st_axi_bus[gg].awsize    = i_axi_awsize  [gg];
         assign st_axi_bus[gg].awvalid   = i_axi_awvalid [gg];
         assign st_axi_bus[gg].rready    = i_axi_rready  [gg];
         assign st_axi_bus[gg].bready    = i_axi_bready  [gg];
         assign st_axi_bus[gg].wdata     = i_axi_wdata   [gg];
         assign st_axi_bus[gg].wlast     = i_axi_wlast   [gg];
         assign st_axi_bus[gg].wstrb     = i_axi_wstrb   [gg];
         assign st_axi_bus[gg].wvalid    = i_axi_wvalid  [gg];
         assign o_axi_arready [gg]       = st_axi_bus[gg].arready;
         assign o_axi_awready [gg]       = st_axi_bus[gg].awready;
         assign o_axi_rdata   [gg]       = st_axi_bus[gg].rdata;
         assign o_axi_rid     [gg]       = st_axi_bus[gg].rid;
         assign o_axi_rlast   [gg]       = st_axi_bus[gg].rlast;
         assign o_axi_rresp   [gg]       = st_axi_bus[gg].rresp;
         assign o_axi_rvalid  [gg]       = st_axi_bus[gg].rvalid;
         assign o_axi_wready  [gg]       = st_axi_bus[gg].wready;
         assign o_axi_bid     [gg]       = st_axi_bus[gg].bid;
         assign o_axi_bresp   [gg]       = st_axi_bus[gg].bresp;
         assign o_axi_bvalid  [gg]       = st_axi_bus[gg].bvalid;
      end  : CNV_TO_AXI_STRUCT_I //}

      if (AXI4_INTERFACE == 1) begin : AXI4_INTERFACE_EQ_1 //{
         // Instantiate Protocol Convertors for all the AXI3 ports
         for (gg = 0; gg < NUM_OF_AXI_PORTS; gg++) begin : AXI4_TO_AXI3_CONV_I //{

            // Adding behavioral delay for the AWxxx output of AXI4-AXI3 converter due to the
            // HBM's simulation model have timing modelling issue that break the simulation.
            // This delay shall be removed in the future once Xilinx provide the HBM's
            // simulation model's fix.

            wire  [ADDR_WIDTH-1:0]  axi3_awaddr;
            wire  [1:0]             axi3_awburst;
            wire  [ID_WIDTH-1:0]    axi3_awid;
            wire  [AXLEN_WIDTH-1:0] axi3_awlen;
            wire  [2:0]             axi3_awsize;
            wire                    axi3_awvalid;

`ifdef AWS_SIM
            assign #200ps st_axi3_bus[gg].awaddr     = axi3_awaddr;
            assign #200ps st_axi3_bus[gg].awburst    = axi3_awburst;
            assign #200ps st_axi3_bus[gg].awid       = axi3_awid;
            assign #200ps st_axi3_bus[gg].awlen[3:0] = axi3_awlen;
            assign #200ps st_axi3_bus[gg].awsize     = axi3_awsize;
            assign #200ps st_axi3_bus[gg].awvalid    = axi3_awvalid;
`else
            assign st_axi3_bus[gg].awaddr            = axi3_awaddr;
            assign st_axi3_bus[gg].awburst           = axi3_awburst;
            assign st_axi3_bus[gg].awid              = axi3_awid;
            assign st_axi3_bus[gg].awlen[3:0]        = axi3_awlen;
            assign st_axi3_bus[gg].awsize            = axi3_awsize;
            assign st_axi3_bus[gg].awvalid           = axi3_awvalid;
`endif

            cl_axi4_to_axi3_conv CL_AXI4_TO_AXI3_CONV_I
                   (
                    .aclk                (axi_clk                     ),    // input wire aclk
                    .aresetn             (axi_rst_n                   ),    // input wire aresetn
                    .s_axi_awid          (st_axi_bus[gg].awid         ),    // input wire [5 : 0] s_axi_awid
                    .s_axi_awaddr        (st_axi_bus[gg].awaddr       ),    // input wire [33 : 0] s_axi_awaddr
                    .s_axi_awlen         (st_axi_bus[gg].awlen        ),    // input wire [7 : 0] s_axi_awlen
                    .s_axi_awsize        (st_axi_bus[gg].awsize       ),    // input wire [2 : 0] s_axi_awsize
                    .s_axi_awburst       (st_axi_bus[gg].awburst      ),    // input wire [1 : 0] s_axi_awburst
                    .s_axi_awlock        (DEF_AWLOCK                  ),    // input wire [0 : 0] s_axi_awlock
                    .s_axi_awcache       (DEF_AWCACHE                 ),    // input wire [3 : 0] s_axi_awcache
                    .s_axi_awprot        (DEF_AWPROT                  ),    // input wire [2 : 0] s_axi_awprot
                    .s_axi_awregion      (DEF_AWREGION                ),    // input wire [3 : 0] s_axi_awregion
                    .s_axi_awqos         (DEF_AWQOS                   ),    // input wire [3 : 0] s_axi_awqos
                    .s_axi_awvalid       (st_axi_bus[gg].awvalid      ),    // input wire s_axi_awvalid
                    .s_axi_awready       (st_axi_bus[gg].awready      ),    // output wire s_axi_awready
                    .s_axi_wdata         (st_axi_bus[gg].wdata        ),    // input wire [255 : 0] s_axi_wdata
                    .s_axi_wstrb         (st_axi_bus[gg].wstrb        ),    // input wire [31 : 0] s_axi_wstrb
                    .s_axi_wlast         (st_axi_bus[gg].wlast        ),    // input wire s_axi_wlast
                    .s_axi_wvalid        (st_axi_bus[gg].wvalid       ),    // input wire s_axi_wvalid
                    .s_axi_wready        (st_axi_bus[gg].wready       ),    // output wire s_axi_wready
                    .s_axi_bid           (st_axi_bus[gg].bid          ),    // output wire [5 : 0] s_axi_bid
                    .s_axi_bresp         (st_axi_bus[gg].bresp        ),    // output wire [1 : 0] s_axi_bresp
                    .s_axi_bvalid        (st_axi_bus[gg].bvalid       ),    // output wire s_axi_bvalid
                    .s_axi_bready        (st_axi_bus[gg].bready       ),    // input wire s_axi_bready
                    .s_axi_arid          (st_axi_bus[gg].arid         ),    // input wire [5 : 0] s_axi_arid
                    .s_axi_araddr        (st_axi_bus[gg].araddr       ),    // input wire [33 : 0] s_axi_araddr
                    .s_axi_arlen         (st_axi_bus[gg].arlen        ),    // input wire [7 : 0] s_axi_arlen
                    .s_axi_arsize        (st_axi_bus[gg].arsize       ),    // input wire [2 : 0] s_axi_arsize
                    .s_axi_arburst       (st_axi_bus[gg].arburst      ),    // input wire [1 : 0] s_axi_arburst
                    .s_axi_arlock        (DEF_AWLOCK                  ),    // input wire [0 : 0] s_axi_arlock
                    .s_axi_arcache       (DEF_AWCACHE                 ),    // input wire [3 : 0] s_axi_arcache
                    .s_axi_arprot        (DEF_AWPROT                  ),    // input wire [2 : 0] s_axi_arprot
                    .s_axi_arregion      (DEF_AWREGION                ),    // input wire [3 : 0] s_axi_arregion
                    .s_axi_arqos         (DEF_AWQOS                   ),    // input wire [3 : 0] s_axi_arqos
                    .s_axi_arvalid       (st_axi_bus[gg].arvalid      ),    // input wire s_axi_arvalid
                    .s_axi_arready       (st_axi_bus[gg].arready      ),    // output wire s_axi_arready
                    .s_axi_rid           (st_axi_bus[gg].rid          ),    // output wire [5 : 0] s_axi_rid
                    .s_axi_rdata         (st_axi_bus[gg].rdata        ),    // output wire [255 : 0] s_axi_rdata
                    .s_axi_rresp         (st_axi_bus[gg].rresp        ),    // output wire [1 : 0] s_axi_rresp
                    .s_axi_rlast         (st_axi_bus[gg].rlast        ),    // output wire s_axi_rlast
                    .s_axi_rvalid        (st_axi_bus[gg].rvalid       ),    // output wire s_axi_rvalid
                    .s_axi_rready        (st_axi_bus[gg].rready       ),    // input wire s_axi_rready
                    .m_axi_awid          (axi3_awid                   ),    // output wire [5 : 0] m_axi_awid
                    .m_axi_awaddr        (axi3_awaddr                 ),    // output wire [33 : 0] m_axi_awaddr
                    .m_axi_awlen         (axi3_awlen[3:0]             ),    // output wire [3 : 0] m_axi_awlen
                    .m_axi_awsize        (axi3_awsize                 ),    // output wire [2 : 0] m_axi_awsize
                    .m_axi_awburst       (axi3_awburst                ),    // output wire [1 : 0] m_axi_awburst
                    .m_axi_awlock        (                            ),    // output wire [1 : 0] m_axi_awlock
                    .m_axi_awcache       (                            ),    // output wire [3 : 0] m_axi_awcache
                    .m_axi_awprot        (                            ),    // output wire [2 : 0] m_axi_awprot
                    .m_axi_awqos         (                            ),    // output wire [3 : 0] m_axi_awqos
                    .m_axi_awvalid       (axi3_awvalid                ),    // output wire m_axi_awvalid
                    .m_axi_awready       (st_axi3_bus[gg].awready     ),    // input wire m_axi_awready
                    .m_axi_wid           (st_axi3_bus[gg].wid         ),    // output wire [5 : 0] m_axi_wid
                    .m_axi_wdata         (st_axi3_bus[gg].wdata       ),    // output wire [255 : 0] m_axi_wdata
                    .m_axi_wstrb         (st_axi3_bus[gg].wstrb       ),    // output wire [31 : 0] m_axi_wstrb
                    .m_axi_wlast         (st_axi3_bus[gg].wlast       ),    // output wire m_axi_wlast
                    .m_axi_wvalid        (st_axi3_bus[gg].wvalid      ),    // output wire m_axi_wvalid
                    .m_axi_wready        (st_axi3_bus[gg].wready      ),    // input wire m_axi_wready
                    .m_axi_bid           (st_axi3_bus[gg].bid         ),    // input wire [5 : 0] m_axi_bid
                    .m_axi_bresp         (st_axi3_bus[gg].bresp       ),    // input wire [1 : 0] m_axi_bresp
                    .m_axi_bvalid        (st_axi3_bus[gg].bvalid      ),    // input wire m_axi_bvalid
                    .m_axi_bready        (st_axi3_bus[gg].bready      ),    // output wire m_axi_bready
                    .m_axi_arid          (st_axi3_bus[gg].arid        ),    // output wire [5 : 0] m_axi_arid
                    .m_axi_araddr        (st_axi3_bus[gg].araddr      ),    // output wire [33 : 0] m_axi_araddr
                    .m_axi_arlen         (st_axi3_bus[gg].arlen[3:0]  ),    // output wire [3 : 0] m_axi_arlen
                    .m_axi_arsize        (st_axi3_bus[gg].arsize      ),    // output wire [2 : 0] m_axi_arsize
                    .m_axi_arburst       (st_axi3_bus[gg].arburst     ),    // output wire [1 : 0] m_axi_arburst
                    .m_axi_arlock        (                            ),    // output wire [1 : 0] m_axi_arlock
                    .m_axi_arcache       (                            ),    // output wire [3 : 0] m_axi_arcache
                    .m_axi_arprot        (                            ),    // output wire [2 : 0] m_axi_arprot
                    .m_axi_arqos         (                            ),    // output wire [3 : 0] m_axi_arqos
                    .m_axi_arvalid       (st_axi3_bus[gg].arvalid     ),    // output wire m_axi_arvalid
                    .m_axi_arready       (st_axi3_bus[gg].arready     ),    // input wire m_axi_arready
                    .m_axi_rid           (st_axi3_bus[gg].rid         ),    // input wire [5 : 0] m_axi_rid
                    .m_axi_rdata         (st_axi3_bus[gg].rdata       ),    // input wire [255 : 0] m_axi_rdata
                    .m_axi_rresp         (st_axi3_bus[gg].rresp       ),    // input wire [1 : 0] m_axi_rresp
                    .m_axi_rlast         (st_axi3_bus[gg].rlast       ),    // input wire m_axi_rlast
                    .m_axi_rvalid        (st_axi3_bus[gg].rvalid      ),    // input wire m_axi_rvalid
                    .m_axi_rready        (st_axi3_bus[gg].rready      )     // output wire m_axi_rready

                    );
         end : AXI4_TO_AXI3_CONV_I //}
      end : AXI4_INTERFACE_EQ_1 //}

      else begin : AXI4_INTERFACE_EQ_0 //{
         // No need for protocol convertor if the input is already in AXI3
         for (gg = 0; gg < NUM_OF_AXI_PORTS; gg++) begin : NO_PROT_CONV_I //{
               assign st_axi3_bus[gg].araddr    = st_axi_bus[gg].araddr;
               assign st_axi3_bus[gg].arburst   = st_axi_bus[gg].arburst;
               assign st_axi3_bus[gg].arid      = st_axi_bus[gg].arid;
               assign st_axi3_bus[gg].arlen     = st_axi_bus[gg].arlen;
               assign st_axi3_bus[gg].arsize    = st_axi_bus[gg].arsize;
               assign st_axi3_bus[gg].arvalid   = st_axi_bus[gg].arvalid;
               assign st_axi3_bus[gg].awaddr    = st_axi_bus[gg].awaddr;
               assign st_axi3_bus[gg].awburst   = st_axi_bus[gg].awburst;
               assign st_axi3_bus[gg].awid      = st_axi_bus[gg].awid;
               assign st_axi3_bus[gg].awlen     = st_axi_bus[gg].awlen;
               assign st_axi3_bus[gg].awsize    = st_axi_bus[gg].awsize;
               assign st_axi3_bus[gg].awvalid   = st_axi_bus[gg].awvalid;
               assign st_axi3_bus[gg].rready    = st_axi_bus[gg].rready;
               assign st_axi3_bus[gg].bready    = st_axi_bus[gg].bready;
               assign st_axi3_bus[gg].wdata     = st_axi_bus[gg].wdata;
               assign st_axi3_bus[gg].wlast     = st_axi_bus[gg].wlast;
               assign st_axi3_bus[gg].wstrb     = st_axi_bus[gg].wstrb;
               assign st_axi3_bus[gg].wvalid    = st_axi_bus[gg].wvalid;
               assign st_axi_bus[gg].arready    = st_axi3_bus[gg].arready;
               assign st_axi_bus[gg].awready    = st_axi3_bus[gg].awready;
               assign st_axi_bus[gg].rdata      = st_axi3_bus[gg].rdata;
               assign st_axi_bus[gg].rid        = st_axi3_bus[gg].rid;
               assign st_axi_bus[gg].rlast      = st_axi3_bus[gg].rlast;
               assign st_axi_bus[gg].rresp      = st_axi3_bus[gg].rresp;
               assign st_axi_bus[gg].rvalid     = st_axi3_bus[gg].rvalid;
               assign st_axi_bus[gg].wready     = st_axi3_bus[gg].wready;
               assign st_axi_bus[gg].bid        = st_axi3_bus[gg].bid;
               assign st_axi_bus[gg].bresp      = st_axi3_bus[gg].bresp;
               assign st_axi_bus[gg].bvalid     = st_axi3_bus[gg].bvalid;
         end : NO_PROT_CONV_I //}
      end : AXI4_INTERFACE_EQ_0 //}

     //==================================================================
     // HBM AXI ports mapping
     //==================================================================
     for (gg = 0; gg < 16; gg++) begin : HBM_STACK_0_MAPPING
      if (gg < NUM_OF_AXI_PORTS) begin
        assign st_hbm_axi3[15-gg].araddr  = st_axi3_bus[gg].araddr;
        assign st_hbm_axi3[15-gg].arburst = st_axi3_bus[gg].arburst;
        assign st_hbm_axi3[15-gg].arid    = st_axi3_bus[gg].arid;
        assign st_hbm_axi3[15-gg].arlen   = st_axi3_bus[gg].arlen;
        assign st_hbm_axi3[15-gg].arsize  = st_axi3_bus[gg].arsize;
        assign st_hbm_axi3[15-gg].arvalid = st_axi3_bus[gg].arvalid;
        assign st_hbm_axi3[15-gg].awaddr  = st_axi3_bus[gg].awaddr;
        assign st_hbm_axi3[15-gg].awburst = st_axi3_bus[gg].awburst;
        assign st_hbm_axi3[15-gg].awid    = st_axi3_bus[gg].awid;
        assign st_hbm_axi3[15-gg].awlen   = st_axi3_bus[gg].awlen;
        assign st_hbm_axi3[15-gg].awsize  = st_axi3_bus[gg].awsize;
        assign st_hbm_axi3[15-gg].awvalid = st_axi3_bus[gg].awvalid;
        assign st_hbm_axi3[15-gg].rready  = st_axi3_bus[gg].rready;
        assign st_hbm_axi3[15-gg].bready  = st_axi3_bus[gg].bready;
        assign st_hbm_axi3[15-gg].wdata   = st_axi3_bus[gg].wdata;
        assign st_hbm_axi3[15-gg].wlast   = st_axi3_bus[gg].wlast;
        assign st_hbm_axi3[15-gg].wstrb   = st_axi3_bus[gg].wstrb;
        assign st_hbm_axi3[15-gg].wvalid  = st_axi3_bus[gg].wvalid;

        assign st_axi3_bus[gg].arready    = st_hbm_axi3[15-gg].arready;
        assign st_axi3_bus[gg].awready    = st_hbm_axi3[15-gg].awready;
        assign st_axi3_bus[gg].rdata      = st_hbm_axi3[15-gg].rdata;
        assign st_axi3_bus[gg].rid        = st_hbm_axi3[15-gg].rid;
        assign st_axi3_bus[gg].rlast      = st_hbm_axi3[15-gg].rlast;
        assign st_axi3_bus[gg].rresp      = st_hbm_axi3[15-gg].rresp;
        assign st_axi3_bus[gg].rvalid     = st_hbm_axi3[15-gg].rvalid;
        assign st_axi3_bus[gg].wready     = st_hbm_axi3[15-gg].wready;
        assign st_axi3_bus[gg].bid        = st_hbm_axi3[15-gg].bid;
        assign st_axi3_bus[gg].bresp      = st_hbm_axi3[15-gg].bresp;
        assign st_axi3_bus[gg].bvalid     = st_hbm_axi3[15-gg].bvalid;
      end else begin
        assign st_hbm_axi3[15-gg].araddr  = '0;
        assign st_hbm_axi3[15-gg].arburst = '0;
        assign st_hbm_axi3[15-gg].arid    = '0;
        assign st_hbm_axi3[15-gg].arlen   = '0;
        assign st_hbm_axi3[15-gg].arsize  = '0;
        assign st_hbm_axi3[15-gg].arvalid = '0;
        assign st_hbm_axi3[15-gg].awaddr  = '0;
        assign st_hbm_axi3[15-gg].awburst = '0;
        assign st_hbm_axi3[15-gg].awid    = '0;
        assign st_hbm_axi3[15-gg].awlen   = '0;
        assign st_hbm_axi3[15-gg].awsize  = '0;
        assign st_hbm_axi3[15-gg].awvalid = '0;
        assign st_hbm_axi3[15-gg].rready  = '0;
        assign st_hbm_axi3[15-gg].bready  = '0;
        assign st_hbm_axi3[15-gg].wdata   = '0;
        assign st_hbm_axi3[15-gg].wlast   = '0;
        assign st_hbm_axi3[15-gg].wstrb   = '0;
        assign st_hbm_axi3[15-gg].wvalid  = '0;
      end
    end : HBM_STACK_0_MAPPING

    for (gg = 16; gg < 32; gg++) begin : HBM_STACK_1_MAPPING
      if (gg < NUM_OF_AXI_PORTS) begin
        assign st_hbm_axi3[gg].araddr  = st_axi3_bus[gg].araddr;
        assign st_hbm_axi3[gg].arburst = st_axi3_bus[gg].arburst;
        assign st_hbm_axi3[gg].arid    = st_axi3_bus[gg].arid;
        assign st_hbm_axi3[gg].arlen   = st_axi3_bus[gg].arlen;
        assign st_hbm_axi3[gg].arsize  = st_axi3_bus[gg].arsize;
        assign st_hbm_axi3[gg].arvalid = st_axi3_bus[gg].arvalid;
        assign st_hbm_axi3[gg].awaddr  = st_axi3_bus[gg].awaddr;
        assign st_hbm_axi3[gg].awburst = st_axi3_bus[gg].awburst;
        assign st_hbm_axi3[gg].awid    = st_axi3_bus[gg].awid;
        assign st_hbm_axi3[gg].awlen   = st_axi3_bus[gg].awlen;
        assign st_hbm_axi3[gg].awsize  = st_axi3_bus[gg].awsize;
        assign st_hbm_axi3[gg].awvalid = st_axi3_bus[gg].awvalid;
        assign st_hbm_axi3[gg].rready  = st_axi3_bus[gg].rready;
        assign st_hbm_axi3[gg].bready  = st_axi3_bus[gg].bready;
        assign st_hbm_axi3[gg].wdata   = st_axi3_bus[gg].wdata;
        assign st_hbm_axi3[gg].wlast   = st_axi3_bus[gg].wlast;
        assign st_hbm_axi3[gg].wstrb   = st_axi3_bus[gg].wstrb;
        assign st_hbm_axi3[gg].wvalid  = st_axi3_bus[gg].wvalid;

        assign st_axi3_bus[gg].arready = st_hbm_axi3[gg].arready;
        assign st_axi3_bus[gg].awready = st_hbm_axi3[gg].awready;
        assign st_axi3_bus[gg].rdata   = st_hbm_axi3[gg].rdata;
        assign st_axi3_bus[gg].rid     = st_hbm_axi3[gg].rid;
        assign st_axi3_bus[gg].rlast   = st_hbm_axi3[gg].rlast;
        assign st_axi3_bus[gg].rresp   = st_hbm_axi3[gg].rresp;
        assign st_axi3_bus[gg].rvalid  = st_hbm_axi3[gg].rvalid;
        assign st_axi3_bus[gg].wready  = st_hbm_axi3[gg].wready;
        assign st_axi3_bus[gg].bid     = st_hbm_axi3[gg].bid;
        assign st_axi3_bus[gg].bresp   = st_hbm_axi3[gg].bresp;
        assign st_axi3_bus[gg].bvalid  = st_hbm_axi3[gg].bvalid;
      end else begin
        assign st_hbm_axi3[gg].araddr  = '0;
        assign st_hbm_axi3[gg].arburst = '0;
        assign st_hbm_axi3[gg].arid    = '0;
        assign st_hbm_axi3[gg].arlen   = '0;
        assign st_hbm_axi3[gg].arsize  = '0;
        assign st_hbm_axi3[gg].arvalid = '0;
        assign st_hbm_axi3[gg].awaddr  = '0;
        assign st_hbm_axi3[gg].awburst = '0;
        assign st_hbm_axi3[gg].awid    = '0;
        assign st_hbm_axi3[gg].awlen   = '0;
        assign st_hbm_axi3[gg].awsize  = '0;
        assign st_hbm_axi3[gg].awvalid = '0;
        assign st_hbm_axi3[gg].rready  = '0;
        assign st_hbm_axi3[gg].bready  = '0;
        assign st_hbm_axi3[gg].wdata   = '0;
        assign st_hbm_axi3[gg].wlast   = '0;
        assign st_hbm_axi3[gg].wstrb   = '0;
        assign st_hbm_axi3[gg].wvalid  = '0;
      end
    end : HBM_STACK_1_MAPPING


   endgenerate //}

`ifndef AWS_SIM

// `ifdef HBM_CHIPSCOPE_DEBUG

// `define HBM_PORT_NUMBER 0

//    logic          ila_probe0;
//    logic [ 25:0]  ila_probe1;
//    logic [ 34:0]  ila_probe2;
//    logic [  3:0]  ila_probe3;
//    logic [ 25:0]  ila_probe4;
//    logic [  4:0]  ila_probe5;
//    logic [255:0]  ila_probe6;
//    logic [255:0]  ila_probe7;


//    assign ila_probe0 = {st_hbm_axi3[`HBM_PORT_NUMBER].awvalid};

//    assign ila_probe1 = {st_hbm_axi3[`HBM_PORT_NUMBER].awvalid,
//                         st_hbm_axi3[`HBM_PORT_NUMBER].awready,
//                         st_hbm_axi3[`HBM_PORT_NUMBER].awlen[3:0],
//                         st_hbm_axi3[`HBM_PORT_NUMBER].awaddr[19:0] // LSB 20 bits
//                        };

//    assign ila_probe2 = {st_hbm_axi3[`HBM_PORT_NUMBER].wvalid,
//                         st_hbm_axi3[`HBM_PORT_NUMBER].wready,
//                         st_hbm_axi3[`HBM_PORT_NUMBER].wlast,
//                         st_hbm_axi3[`HBM_PORT_NUMBER].wstrb
//                        };

//    assign ila_probe3 = {st_hbm_axi3[`HBM_PORT_NUMBER].bvalid,
//                         st_hbm_axi3[`HBM_PORT_NUMBER].bready,
//                         st_hbm_axi3[`HBM_PORT_NUMBER].bresp
//                        };

//    assign ila_probe4 = {st_hbm_axi3[`HBM_PORT_NUMBER].arvalid,
//                         st_hbm_axi3[`HBM_PORT_NUMBER].arready,
//                         st_hbm_axi3[`HBM_PORT_NUMBER].arlen[3:0],
//                         st_hbm_axi3[`HBM_PORT_NUMBER].araddr[19:0] // LSB 20 bits
//                        };

//    assign ila_probe5 = {st_hbm_axi3[`HBM_PORT_NUMBER].rvalid,
//                         st_hbm_axi3[`HBM_PORT_NUMBER].rready,
//                         st_hbm_axi3[`HBM_PORT_NUMBER].rlast,
//                         st_hbm_axi3[`HBM_PORT_NUMBER].rresp
//                        };

//    assign ila_probe6 = {st_hbm_axi3[`HBM_PORT_NUMBER].wdata};

//    assign ila_probe7 = {st_hbm_axi3[`HBM_PORT_NUMBER].rdata};

//    cl_ila_hbm CL_ILA_HBM_I (
//            .clk   (axi_clk),    // input wire          clk
//            .probe0(ila_probe0), // input wire [  0:0]  probe0
//            .probe1(ila_probe1), // input wire [ 25:0]  probe1
//            .probe2(ila_probe2), // input wire [ 34:0]  probe2
//            .probe3(ila_probe3), // input wire [  3:0]  probe3
//            .probe4(ila_probe4), // input wire [ 25:0]  probe4
//            .probe5(ila_probe5)  // input wire [  4:0]  probe5
//    );

// `endif // HBM_CHIPSCOPE_DEBUG

`endif // AWS_SIM

   // NOTE Connecting PCIS bus into AXI_16_AWADDR port of HBM
   //================================================================================
   // HBM controller
   //================================================================================
   cl_hbm HBM_CORE_I
     (
      .HBM_REF_CLK_0                  (apb_clk                        ),  // input wire HBM_REF_CLK_0
      .HBM_REF_CLK_1                  (apb_clk                        ),  // input wire HBM_REF_CLK_1

      `define CONNECT_HBM_APB_MON(PP)\
        .MON_APB_``PP``_PRESET_N      (i_hbm_apb_preset_n_``PP``      ),\
        .APB_``PP``_PWDATA_MON        (o_hbm_apb_pwdata_``PP``        ),\
        .APB_``PP``_PADDR_MON         (o_hbm_apb_paddr_``PP``         ),\
        .APB_``PP``_PENABLE_MON       (o_hbm_apb_penable_``PP``       ),\
        .APB_``PP``_PSEL_MON          (o_hbm_apb_psel_``PP``          ),\
        .APB_``PP``_PWRITE_MON        (o_hbm_apb_pwrite_``PP``        ),\
        .APB_``PP``_PRDATA_MON        (o_hbm_apb_prdata_``PP``        ),\
        .APB_``PP``_PREADY_MON        (o_hbm_apb_pready_``PP``        ),\
        .APB_``PP``_PSLVERR_MON       (o_hbm_apb_pslverr_``PP``       ),

    `CONNECT_HBM_APB_MON(0)
    `CONNECT_HBM_APB_MON(1)

   `define CONNECT_AXI_HBM_CORE(P)\
      .AXI_``P``_ACLK                 (axi_clk                        ),  // input wire AXI_ACLK\
      .AXI_``P``_ARESET_N             (axi_rst_n                      ),  // input wire AXI_ARESET_N\
      .AXI_``P``_ARADDR               (st_hbm_axi3[P].araddr          ),  // input wire [33 : 0] AXI_ARADDR\
      .AXI_``P``_ARBURST              (st_hbm_axi3[P].arburst         ),  // input wire [1 : 0] AXI_ARBURST\
      .AXI_``P``_ARID                 (st_hbm_axi3[P].arid            ),  // input wire [5 : 0] AXI_ARID\
      .AXI_``P``_ARLEN                (st_hbm_axi3[P].arlen[3:0]      ),  // input wire [3 : 0] AXI_ARLEN\
      .AXI_``P``_ARSIZE               (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_ARSIZE\
      .AXI_``P``_ARVALID              (st_hbm_axi3[P].arvalid         ),  // input wire AXI_ARVALID\
      .AXI_``P``_AWADDR               (st_hbm_axi3[P].awaddr          ),  // input wire [33 : 0] AXI_AWADDR\
      .AXI_``P``_AWBURST              (st_hbm_axi3[P].awburst         ),  // input wire [1 : 0] AXI_AWBURST\
      .AXI_``P``_AWID                 (st_hbm_axi3[P].awid            ),  // input wire [5 : 0] AXI_AWID\
      .AXI_``P``_AWLEN                (st_hbm_axi3[P].awlen[3:0]      ),  // input wire [3 : 0] AXI_AWLEN\
      .AXI_``P``_AWSIZE               (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_AWSIZE\
      .AXI_``P``_AWVALID              (st_hbm_axi3[P].awvalid         ),  // input wire AXI_AWVALID\
      .AXI_``P``_RREADY               (st_hbm_axi3[P].rready          ),  // input wire AXI_RREADY\
      .AXI_``P``_BREADY               (st_hbm_axi3[P].bready          ),  // input wire AXI_BREADY\
      .AXI_``P``_WDATA                (st_hbm_axi3[P].wdata           ),  // input wire [255 : 0] AXI_WDATA\
      .AXI_``P``_WLAST                (st_hbm_axi3[P].wlast           ),  // input wire AXI_WLAST\
      .AXI_``P``_WSTRB                (st_hbm_axi3[P].wstrb           ),  // input wire [31 : 0] AXI_WSTRB\
      .AXI_``P``_WDATA_PARITY         (DEF_PARITY                     ),  // input wire [31 : 0] AXI_WDATA_PARITY\
      .AXI_``P``_WVALID               (st_hbm_axi3[P].wvalid          ),  // input wire AXI_WVALID\
      .AXI_``P``_ARREADY              (st_hbm_axi3[P].arready         ),  // output wire AXI_ARREADY\
      .AXI_``P``_AWREADY              (st_hbm_axi3[P].awready         ),  // output wire AXI_AWREADY\
      .AXI_``P``_RDATA_PARITY         (                               ),  // output wire [31 : 0] AXI_RDATA_PARITY\
      .AXI_``P``_RDATA                (st_hbm_axi3[P].rdata           ),  // output wire [255 : 0] AXI_RDATA\
      .AXI_``P``_RID                  (st_hbm_axi3[P].rid             ),  // output wire [5 : 0] AXI_RID\
      .AXI_``P``_RLAST                (st_hbm_axi3[P].rlast           ),  // output wire AXI_RLAST\
      .AXI_``P``_RRESP                (st_hbm_axi3[P].rresp           ),  // output wire [1 : 0] AXI_RRESP\
      .AXI_``P``_RVALID               (st_hbm_axi3[P].rvalid          ),  // output wire AXI_RVALID\
      .AXI_``P``_WREADY               (st_hbm_axi3[P].wready          ),  // output wire AXI_WREADY\
      .AXI_``P``_BID                  (st_hbm_axi3[P].bid             ),  // output wire [5 : 0] AXI_BID\
      .AXI_``P``_BRESP                (st_hbm_axi3[P].bresp           ),  // output wire [1 : 0] AXI_BRESP\
      .AXI_``P``_BVALID               (st_hbm_axi3[P].bvalid          ),  // output wire AXI_BVALID

      `CONNECT_AXI_HBM_CORE(00)
      `CONNECT_AXI_HBM_CORE(01)
      `CONNECT_AXI_HBM_CORE(02)
      `CONNECT_AXI_HBM_CORE(03)
      `CONNECT_AXI_HBM_CORE(04)
      `CONNECT_AXI_HBM_CORE(05)
      `CONNECT_AXI_HBM_CORE(06)
      `CONNECT_AXI_HBM_CORE(07)
      `CONNECT_AXI_HBM_CORE(08)
      `CONNECT_AXI_HBM_CORE(09)
      `CONNECT_AXI_HBM_CORE(10)
      `CONNECT_AXI_HBM_CORE(11)
      `CONNECT_AXI_HBM_CORE(12)
      `CONNECT_AXI_HBM_CORE(13)
      `CONNECT_AXI_HBM_CORE(14)
      `CONNECT_AXI_HBM_CORE(15)
      `CONNECT_AXI_HBM_CORE(16)
      `CONNECT_AXI_HBM_CORE(17)
      `CONNECT_AXI_HBM_CORE(18)
      `CONNECT_AXI_HBM_CORE(19)
      `CONNECT_AXI_HBM_CORE(20)
      `CONNECT_AXI_HBM_CORE(21)
      `CONNECT_AXI_HBM_CORE(22)
      `CONNECT_AXI_HBM_CORE(23)
      `CONNECT_AXI_HBM_CORE(24)
      `CONNECT_AXI_HBM_CORE(25)
      `CONNECT_AXI_HBM_CORE(26)
      `CONNECT_AXI_HBM_CORE(27)
      `CONNECT_AXI_HBM_CORE(28)
      `CONNECT_AXI_HBM_CORE(29)
      `CONNECT_AXI_HBM_CORE(30)
      `CONNECT_AXI_HBM_CORE(31)

      .APB_0_PWDATA                   (32'd0                          ),  // input wire [31 : 0] APB_0_PWDATA
      .APB_0_PADDR                    (22'd0                          ),  // input wire [21 : 0] APB_0_PADDR
      .APB_0_PCLK                     (apb_clk                        ),  // input wire APB_0_PCLK
      .APB_0_PENABLE                  (1'd0                           ),  // input wire APB_0_PENABLE
      .APB_0_PRESET_N                 (apb_rst_n                      ),  // input wire APB_0_PRESET_N
      .APB_0_PSEL                     (1'd0                           ),  // input wire APB_0_PSEL
      .APB_0_PWRITE                   (1'd0                           ),  // input wire APB_0_PWRITE
      .APB_0_PRDATA                   (                               ),  // output wire [31 : 0] APB_0_PRDATA
      .APB_0_PREADY                   (                               ),  // output wire APB_0_PREADY
      .APB_0_PSLVERR                  (                               ),  // output wire APB_0_PSLVERR

      .APB_1_PWDATA                   (32'd0                          ),  // input wire [31 : 0] APB_1_PWDATA
      .APB_1_PADDR                    (22'd0                          ),  // input wire [21 : 0] APB_1_PADDR
      .APB_1_PCLK                     (apb_clk                        ),  // input wire APB_1_PCLK
      .APB_1_PENABLE                  (1'd0                           ),  // input wire APB_1_PENABLE
      .APB_1_PRESET_N                 (apb_rst_n                      ),  // input wire APB_1_PRESET_N
      .APB_1_PSEL                     (1'd0                           ),  // input wire APB_1_PSEL
      .APB_1_PWRITE                   (1'd0                           ),  // input wire APB_1_PWRITE
      .APB_1_PRDATA                   (                               ),  // output wire [31 : 0] APB_1_PRDATA
      .APB_1_PREADY                   (                               ),  // output wire APB_1_PREADY
      .APB_1_PSLVERR                  (                               ),  // output wire APB_1_PSLVERR

      .apb_complete_0                 (apb_complete[0]                ),  // output wire apb_complete_0
      .apb_complete_1                 (apb_complete[1]                ),  // output wire apb_complete_1

      .DRAM_0_STAT_CATTRIP            (                               ),  // output wire DRAM_0_STAT_CATTRIP
      .DRAM_0_STAT_TEMP               (                               ),  // output wire [6 : 0] DRAM_0_STAT_TEMP
      .DRAM_1_STAT_CATTRIP            (                               ),  // output wire DRAM_1_STAT_CATTRIP
      .DRAM_1_STAT_TEMP               (                               )   // output wire [6 : 0] DRAM_1_STAT_TEMP
      );

   //
   // bring apb_complete into clk domain
   //
   sync
     #(
       .WIDTH($bits(apb_complete))
       )
   SYNC_HBM_INIT_TO_ACLK
     (
      .clk      (clk               ),
      .rst_n    (1'b1              ),
      .in       (apb_complete      ),
      .sync_out (hbm_ready_q       )
      );

   always_ff @(posedge clk)
     o_hbm_ready <= &hbm_ready_q;

endmodule // cl_hbm_wrapper
