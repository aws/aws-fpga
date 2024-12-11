//-------------------------------------------------------------------------------------------------------------------------------
// Amazon FPGA Hardware Development Kit
//
// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
// Restricted NDA Material
//-------------------------------------------------------------------------------------------------------------------------------
//===============================================================================================================================
// HBM Wrapper
// - Wrapper for HBM IP
// - Implements an MMCM to generate 100MHz and 450MHz clock for the HBM IP.
// - AXI interface run @450MHz.
// - Parameterized number of AXI interfaces.
//   User can choose to connect upto 32 AXI interfaces to the HBM.
// - User can connect using AXI4 Protocol, and leverage AXI4-to-AXI3 protocol convertor
//   by setting parameter AXI4_INTERFACE=1
// - Unused HBM ports are automatically tied off.
// - Stats interface to reset the HBM, status check for HBM initialization.
//
//------------------------------------------
// HBM Stats Interface Reset Routine:
// // Issue HBM soft reset
// write 0x1 @ addr 0x00
// write 0x0 @ addr 0x00
// // Poll for lock
// poll bits[3:1] = 3'b111 @ addr 0x00
//
//
//===============================================================================================================================

module hbm_wrapper
  #(
    parameter NUM_OF_AXI_PORTS           = 1,                        // Number of AXI ports to connect to the HBM
    parameter AXI4_INTERFACE             = 0,                        // 1 = Instantiate Xilinx AXI4-to-AXI3 Protocol Convertor.
    parameter AXLEN_WIDTH                = AXI4_INTERFACE ? 8 : 4    // width of axlen. For AXI4 interface this must be 8, for AXI3 interface this must be 4.
    )
   (
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

   localparam   DEF_AWLOCK      = 32'd0;
   localparam   DEF_AWCACHE     = 4'h1; // Device bufferable, non-cacheable
   localparam   DEF_AWPROT      = 32'd0;
   localparam   DEF_AWREGION    = 32'd0;
   localparam   DEF_AWQOS       = 32'd0;

   localparam   DEF_AXSIZE      = 3'($clog2(HBM_DATA_WIDTH/8));
   localparam   DEF_PARITY      = 32'd0;

   logic        apb_clk;
   logic        axi_clk;
   logic        mmcm_lock;
   logic        cfg_hbm_reset = '0;
   logic [1:0]  hbm_ready_q;
   logic [1:0]  apb_complete;


   //=================================================================
   // Pipe reset for better timing
   //=================================================================
   logic        sync_rst_n;

   assign clk = i_clk_250m;
   always_ff @(posedge clk)
     sync_rst_n <= i_rst_250m_n;

   // PIPE for resets into SLR0
   logic slr0_sync_rst_n;
   lib_pipe #(.WIDTH(1), .STAGES(4)) SLR0_PIPE_RST_N (.clk(clk), .rst_n(1'b1), .in_bus(sync_rst_n), .out_bus(slr0_sync_rst_n));

   //==================================================================
   // Synchronize resets
   //===================================================================
   logic hbm_rst_q;
   lib_pipe
     #(
       .WIDTH  (1),
       .STAGES (4)
       )
   SLR0_PIPE_HBM_RST_N
     (
      .clk     (clk),
      .rst_n   (1'b1),
      .in_bus  (slr0_sync_rst_n & ~cfg_hbm_reset),
      .out_bus (hbm_rst_q)
      );

   // reset in apb_clk domain
   logic apb_rst_sync_n;
   sync
     #(
       .WIDTH($bits(apb_rst_sync_n))
       )
   SYNC_RST_APB_CLK
     (
      .clk      (apb_clk        ),
      .rst_n    (hbm_rst_q      ),
      .in       (1'd1           ),
      .sync_out (apb_rst_sync_n )
      );

   logic apb_rst_n;
   lib_pipe #(.WIDTH(1), .STAGES(4)) SLR0_APB_RST_N (.clk(apb_clk), .rst_n(1'b1), .in_bus(apb_rst_sync_n), .out_bus(apb_rst_n));

   // reset in axi_clk domain
   logic axi_rst_sync_n;
   sync
     #(
       .WIDTH($bits(axi_rst_sync_n))
       )
   SYNC_RST_AXI_CLK
     (
      .clk      (axi_clk        ),
      .rst_n    (hbm_rst_q      ),
      .in       (1'd1           ),
      .sync_out (axi_rst_sync_n )
      );

   logic axi_rst_n;
   lib_pipe #(.WIDTH(1), .STAGES(4)) SLR0_AXI_RST_N (.clk(axi_clk), .rst_n(1'b1), .in_bus(axi_rst_sync_n), .out_bus(axi_rst_n));

   //==================================================================
   // HBM CSRs
   //==================================================================
   //HBM CFG BUS
   cfg_bus_t hbm_cfg_bus_q();
   always_ff @(posedge clk)
     if (!slr0_sync_rst_n) begin
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
   // 0x00 : bit[0] = SW reset for HBM (R/W)
   //                 1: Assert Reset for HBM
   //                 0: Deassert Reset for HBM
   //        bit[2:1] = HBM initialized (R/O)
   //        bit[3]   = 100MHz MMCM locked (R/O)
   //
   always_ff @(posedge clk)
     if (hbm_cfg_bus_q.wr && !hbm_cfg_bus_q.ack && (hbm_cfg_bus_q.addr[7:0] == '0))
       cfg_hbm_reset <= hbm_cfg_bus_q.wdata[0];

   // HBM CSR Read datapath
   always_ff @(posedge clk)
     if (hbm_cfg_bus_q.addr[7:0] == '0)
       hbm_cfg_bus_q.rdata <= 32'({mmcm_lock,       // bit[3]
                                   hbm_ready_q,     // bit[2:1]
                                   cfg_hbm_reset}); // bit[0]
     else
       hbm_cfg_bus_q.rdata <= 32'hdead_dead;


   //==================================================================
   // HBM requires following clocks:
   // - 100 MHz REF CLK, AND APB CLOCKS
   // - 450 MHz AXI CLK
   //==================================================================
   cl_hbm_mmcm HBM_MMCM_I
     (
      .clk_out1 (apb_clk         ),     // output clk_out1 = 100MHz
      .clk_out2 (axi_clk         ),     // output clk_out2 = 450MHz
      .resetn   (slr0_sync_rst_n ),     // input resetn
      .locked   (mmcm_lock       ),     // output locked
      .clk_in1  (clk             )      // input clk_in1
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

   //
   // Convert input/output axi bus to structure for convenience
   //
   st_axi_bus_t st_axi_bus [0:NUM_OF_AXI_PORTS-1];
   always_comb begin : CNV_TO_AXI_STRUCT_I //{
      for (int ii = 0; ii < NUM_OF_AXI_PORTS; ii++) begin //{
         st_axi_bus[ii].araddr    = i_axi_araddr  [ii];
         st_axi_bus[ii].arburst   = i_axi_arburst [ii];
         st_axi_bus[ii].arid      = i_axi_arid    [ii];
         st_axi_bus[ii].arlen     = i_axi_arlen   [ii];
         st_axi_bus[ii].arsize    = i_axi_arsize  [ii];
         st_axi_bus[ii].arvalid   = i_axi_arvalid [ii];
         st_axi_bus[ii].awaddr    = i_axi_awaddr  [ii];
         st_axi_bus[ii].awburst   = i_axi_awburst [ii];
         st_axi_bus[ii].awid      = i_axi_awid    [ii];
         st_axi_bus[ii].awlen     = i_axi_awlen   [ii];
         st_axi_bus[ii].awsize    = i_axi_awsize  [ii];
         st_axi_bus[ii].awvalid   = i_axi_awvalid [ii];
         st_axi_bus[ii].rready    = i_axi_rready  [ii];
         st_axi_bus[ii].bready    = i_axi_bready  [ii];
         st_axi_bus[ii].wdata     = i_axi_wdata   [ii];
         st_axi_bus[ii].wlast     = i_axi_wlast   [ii];
         st_axi_bus[ii].wstrb     = i_axi_wstrb   [ii];
         st_axi_bus[ii].wvalid    = i_axi_wvalid  [ii];
         o_axi_arready [ii]       = st_axi_bus[ii].arready;
         o_axi_awready [ii]       = st_axi_bus[ii].awready;
         o_axi_rdata   [ii]       = st_axi_bus[ii].rdata;
         o_axi_rid     [ii]       = st_axi_bus[ii].rid;
         o_axi_rlast   [ii]       = st_axi_bus[ii].rlast;
         o_axi_rresp   [ii]       = st_axi_bus[ii].rresp;
         o_axi_rvalid  [ii]       = st_axi_bus[ii].rvalid;
         o_axi_wready  [ii]       = st_axi_bus[ii].wready;
         o_axi_bid     [ii]       = st_axi_bus[ii].bid;
         o_axi_bresp   [ii]       = st_axi_bus[ii].bresp;
         o_axi_bvalid  [ii]       = st_axi_bus[ii].bvalid;
      end //}
   end : CNV_TO_AXI_STRUCT_I //}


   //==========================================================================
   // AXI4 to AXI3 Protocol convertor
   //==========================================================================
   st_axi_bus_t st_axi3_bus [0:NUM_OF_AXI_PORTS-1];

   genvar                       gg;
   generate //{
      if (AXI4_INTERFACE == 1) begin : AXI4_INTERFACE_EQ_1 //{
         // Instantiate Protocol Convertors for all the AXI3 ports
         for (gg = 0; gg < NUM_OF_AXI_PORTS; gg++) begin : AXI4_TO_AXI3_CONV_I //{
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
                    .m_axi_awid          (st_axi3_bus[gg].awid        ),    // output wire [5 : 0] m_axi_awid
                    .m_axi_awaddr        (st_axi3_bus[gg].awaddr      ),    // output wire [33 : 0] m_axi_awaddr
                    .m_axi_awlen         (st_axi3_bus[gg].awlen       ),    // output wire [3 : 0] m_axi_awlen
                    .m_axi_awsize        (st_axi3_bus[gg].awsize      ),    // output wire [2 : 0] m_axi_awsize
                    .m_axi_awburst       (st_axi3_bus[gg].awburst     ),    // output wire [1 : 0] m_axi_awburst
                    .m_axi_awlock        (                            ),    // output wire [1 : 0] m_axi_awlock
                    .m_axi_awcache       (                            ),    // output wire [3 : 0] m_axi_awcache
                    .m_axi_awprot        (                            ),    // output wire [2 : 0] m_axi_awprot
                    .m_axi_awqos         (                            ),    // output wire [3 : 0] m_axi_awqos
                    .m_axi_awvalid       (st_axi3_bus[gg].awvalid     ),    // output wire m_axi_awvalid
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
                    .m_axi_arlen         (st_axi3_bus[gg].arlen       ),    // output wire [3 : 0] m_axi_arlen
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
         always_comb begin : NO_PROT_CONV_I //{
            // No need for protocol convertor if the input is already in AXI3
            for (int ii = 0; ii < NUM_OF_AXI_PORTS; ii++) begin //{
               st_axi3_bus[ii].araddr    = st_axi_bus[ii].araddr;
               st_axi3_bus[ii].arburst   = st_axi_bus[ii].arburst;
               st_axi3_bus[ii].arid      = st_axi_bus[ii].arid;
               st_axi3_bus[ii].arlen     = st_axi_bus[ii].arlen;
               st_axi3_bus[ii].arsize    = st_axi_bus[ii].arsize;
               st_axi3_bus[ii].arvalid   = st_axi_bus[ii].arvalid;
               st_axi3_bus[ii].awaddr    = st_axi_bus[ii].awaddr;
               st_axi3_bus[ii].awburst   = st_axi_bus[ii].awburst;
               st_axi3_bus[ii].awid      = st_axi_bus[ii].awid;
               st_axi3_bus[ii].awlen     = st_axi_bus[ii].awlen;
               st_axi3_bus[ii].awsize    = st_axi_bus[ii].awsize;
               st_axi3_bus[ii].awvalid   = st_axi_bus[ii].awvalid;
               st_axi3_bus[ii].rready    = st_axi_bus[ii].rready;
               st_axi3_bus[ii].bready    = st_axi_bus[ii].bready;
               st_axi3_bus[ii].wdata     = st_axi_bus[ii].wdata;
               st_axi3_bus[ii].wlast     = st_axi_bus[ii].wlast;
               st_axi3_bus[ii].wstrb     = st_axi_bus[ii].wstrb;
               st_axi3_bus[ii].wvalid    = st_axi_bus[ii].wvalid;
               st_axi_bus[ii].arready    = st_axi3_bus[ii].arready;
               st_axi_bus[ii].awready    = st_axi3_bus[ii].awready;
               st_axi_bus[ii].rdata      = st_axi3_bus[ii].rdata;
               st_axi_bus[ii].rid        = st_axi3_bus[ii].rid;
               st_axi_bus[ii].rlast      = st_axi3_bus[ii].rlast;
               st_axi_bus[ii].rresp      = st_axi3_bus[ii].rresp;
               st_axi_bus[ii].rvalid     = st_axi3_bus[ii].rvalid;
               st_axi_bus[ii].wready     = st_axi3_bus[ii].wready;
               st_axi_bus[ii].bid        = st_axi3_bus[ii].bid;
               st_axi_bus[ii].bresp      = st_axi3_bus[ii].bresp;
               st_axi_bus[ii].bvalid     = st_axi3_bus[ii].bvalid;
            end //}
         end : NO_PROT_CONV_I //}
      end : AXI4_INTERFACE_EQ_0 //}
   endgenerate //}

   //==================================================================
   // HBM AXI ports tieoff
   //==================================================================
   st_axi_bus_t st_hbm_axi3[0:31];

   always_comb begin : HBM_TIEOFF_I //{
      for (int ii = 0; ii < 32; ii++) begin //{
         if (ii < NUM_OF_AXI_PORTS) begin //{
            st_hbm_axi3[ii].araddr    = st_axi3_bus[ii].araddr;
            st_hbm_axi3[ii].arburst   = st_axi3_bus[ii].arburst;
            st_hbm_axi3[ii].arid      = st_axi3_bus[ii].arid;
            st_hbm_axi3[ii].arlen     = st_axi3_bus[ii].arlen;
            st_hbm_axi3[ii].arsize    = st_axi3_bus[ii].arsize;
            st_hbm_axi3[ii].arvalid   = st_axi3_bus[ii].arvalid;
            st_hbm_axi3[ii].awaddr    = st_axi3_bus[ii].awaddr;
            st_hbm_axi3[ii].awburst   = st_axi3_bus[ii].awburst;
            st_hbm_axi3[ii].awid      = st_axi3_bus[ii].awid;
            st_hbm_axi3[ii].awlen     = st_axi3_bus[ii].awlen;
            st_hbm_axi3[ii].awsize    = st_axi3_bus[ii].awsize;
            st_hbm_axi3[ii].awvalid   = st_axi3_bus[ii].awvalid;
            st_hbm_axi3[ii].rready    = st_axi3_bus[ii].rready;
            st_hbm_axi3[ii].bready    = st_axi3_bus[ii].bready;
            st_hbm_axi3[ii].wdata     = st_axi3_bus[ii].wdata;
            st_hbm_axi3[ii].wlast     = st_axi3_bus[ii].wlast;
            st_hbm_axi3[ii].wstrb     = st_axi3_bus[ii].wstrb;
            st_hbm_axi3[ii].wvalid    = st_axi3_bus[ii].wvalid;
            st_axi3_bus[ii].arready   = st_hbm_axi3[ii].arready;
            st_axi3_bus[ii].awready   = st_hbm_axi3[ii].awready;
            st_axi3_bus[ii].rdata     = st_hbm_axi3[ii].rdata;
            st_axi3_bus[ii].rid       = st_hbm_axi3[ii].rid;
            st_axi3_bus[ii].rlast     = st_hbm_axi3[ii].rlast;
            st_axi3_bus[ii].rresp     = st_hbm_axi3[ii].rresp;
            st_axi3_bus[ii].rvalid    = st_hbm_axi3[ii].rvalid;
            st_axi3_bus[ii].wready    = st_hbm_axi3[ii].wready;
            st_axi3_bus[ii].bid       = st_hbm_axi3[ii].bid;
            st_axi3_bus[ii].bresp     = st_hbm_axi3[ii].bresp;
            st_axi3_bus[ii].bvalid    = st_hbm_axi3[ii].bvalid;
         end //}
         else begin //{
            st_hbm_axi3[ii].araddr    = '0;
            st_hbm_axi3[ii].arburst   = '0;
            st_hbm_axi3[ii].arid      = '0;
            st_hbm_axi3[ii].arlen     = '0;
            st_hbm_axi3[ii].arsize    = '0;
            st_hbm_axi3[ii].arvalid   = '0;
            st_hbm_axi3[ii].awaddr    = '0;
            st_hbm_axi3[ii].awburst   = '0;
            st_hbm_axi3[ii].awid      = '0;
            st_hbm_axi3[ii].awlen     = '0;
            st_hbm_axi3[ii].awsize    = '0;
            st_hbm_axi3[ii].awvalid   = '0;
            st_hbm_axi3[ii].rready    = '0;
            st_hbm_axi3[ii].bready    = '0;
            st_hbm_axi3[ii].wdata     = '0;
            st_hbm_axi3[ii].wlast     = '0;
            st_hbm_axi3[ii].wstrb     = '0;
            st_hbm_axi3[ii].wvalid    = '0;
         end //}
      end //}
   end : HBM_TIEOFF_I //}


   // NOTE Connecting PCIS bus into AXI_16_AWADDR port of HBM
   //================================================================================
   // HBM controller
   //================================================================================
   cl_hbm HBM_CORE_I
     (
      .HBM_REF_CLK_0                  (apb_clk                        ),  // input wire HBM_REF_CLK_0
      .HBM_REF_CLK_1                  (apb_clk                        ),  // input wire HBM_REF_CLK_1

      .AXI_00_ACLK                    (axi_clk                        ),  // input wire AXI_00_ACLK
      .AXI_00_ARESET_N                (axi_rst_n                      ),  // input wire AXI_00_ARESET_N
      .AXI_00_ARADDR                  (st_hbm_axi3[00].araddr         ),  // input wire [33 : 0] AXI_00_ARADDR
      .AXI_00_ARBURST                 (st_hbm_axi3[00].arburst        ),  // input wire [1 : 0] AXI_00_ARBURST
      .AXI_00_ARID                    (st_hbm_axi3[00].arid           ),  // input wire [5 : 0] AXI_00_ARID
      .AXI_00_ARLEN                   (st_hbm_axi3[00].arlen          ),  // input wire [3 : 0] AXI_00_ARLEN
      .AXI_00_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_00_ARSIZE
      .AXI_00_ARVALID                 (st_hbm_axi3[00].arvalid        ),  // input wire AXI_00_ARVALID
      .AXI_00_AWADDR                  (st_hbm_axi3[00].awaddr         ),  // input wire [33 : 0] AXI_00_AWADDR
      .AXI_00_AWBURST                 (st_hbm_axi3[00].awburst        ),  // input wire [1 : 0] AXI_00_AWBURST
      .AXI_00_AWID                    (st_hbm_axi3[00].awid           ),  // input wire [5 : 0] AXI_00_AWID
      .AXI_00_AWLEN                   (st_hbm_axi3[00].awlen          ),  // input wire [3 : 0] AXI_00_AWLEN
      .AXI_00_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_00_AWSIZE
      .AXI_00_AWVALID                 (st_hbm_axi3[00].awvalid        ),  // input wire AXI_00_AWVALID
      .AXI_00_RREADY                  (st_hbm_axi3[00].rready         ),  // input wire AXI_00_RREADY
      .AXI_00_BREADY                  (st_hbm_axi3[00].bready         ),  // input wire AXI_00_BREADY
      .AXI_00_WDATA                   (st_hbm_axi3[00].wdata          ),  // input wire [255 : 0] AXI_00_WDATA
      .AXI_00_WLAST                   (st_hbm_axi3[00].wlast          ),  // input wire AXI_00_WLAST
      .AXI_00_WSTRB                   (st_hbm_axi3[00].wstrb          ),  // input wire [31 : 0] AXI_00_WSTRB
      .AXI_00_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_00_WDATA_PARITY
      .AXI_00_WVALID                  (st_hbm_axi3[00].wvalid         ),  // input wire AXI_00_WVALID
      .AXI_00_ARREADY                 (st_hbm_axi3[00].arready        ),  // output wire AXI_00_ARREADY
      .AXI_00_AWREADY                 (st_hbm_axi3[00].awready        ),  // output wire AXI_00_AWREADY
      .AXI_00_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_00_RDATA_PARITY
      .AXI_00_RDATA                   (st_hbm_axi3[00].rdata          ),  // output wire [255 : 0] AXI_00_RDATA
      .AXI_00_RID                     (st_hbm_axi3[00].rid            ),  // output wire [5 : 0] AXI_00_RID
      .AXI_00_RLAST                   (st_hbm_axi3[00].rlast          ),  // output wire AXI_00_RLAST
      .AXI_00_RRESP                   (st_hbm_axi3[00].rresp          ),  // output wire [1 : 0] AXI_00_RRESP
      .AXI_00_RVALID                  (st_hbm_axi3[00].rvalid         ),  // output wire AXI_00_RVALID
      .AXI_00_WREADY                  (st_hbm_axi3[00].wready         ),  // output wire AXI_00_WREADY
      .AXI_00_BID                     (st_hbm_axi3[00].bid            ),  // output wire [5 : 0] AXI_00_BID
      .AXI_00_BRESP                   (st_hbm_axi3[00].bresp          ),  // output wire [1 : 0] AXI_00_BRESP
      .AXI_00_BVALID                  (st_hbm_axi3[00].bvalid         ),  // output wire AXI_00_BVALID

      .AXI_01_ACLK                    (axi_clk                        ),  // input wire AXI_01_ACLK
      .AXI_01_ARESET_N                (axi_rst_n                      ),  // input wire AXI_01_ARESET_N
      .AXI_01_ARADDR                  (st_hbm_axi3[01].araddr         ),  // input wire [33 : 0] AXI_01_ARADDR
      .AXI_01_ARBURST                 (st_hbm_axi3[01].arburst        ),  // input wire [1 : 0] AXI_01_ARBURST
      .AXI_01_ARID                    (st_hbm_axi3[01].arid           ),  // input wire [5 : 0] AXI_01_ARID
      .AXI_01_ARLEN                   (st_hbm_axi3[01].arlen          ),  // input wire [3 : 0] AXI_01_ARLEN
      .AXI_01_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_01_ARSIZE
      .AXI_01_ARVALID                 (st_hbm_axi3[01].arvalid        ),  // input wire AXI_01_ARVALID
      .AXI_01_AWADDR                  (st_hbm_axi3[01].awaddr         ),  // input wire [33 : 0] AXI_01_AWADDR
      .AXI_01_AWBURST                 (st_hbm_axi3[01].awburst        ),  // input wire [1 : 0] AXI_01_AWBURST
      .AXI_01_AWID                    (st_hbm_axi3[01].awid           ),  // input wire [5 : 0] AXI_01_AWID
      .AXI_01_AWLEN                   (st_hbm_axi3[01].awlen          ),  // input wire [3 : 0] AXI_01_AWLEN
      .AXI_01_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_01_AWSIZE
      .AXI_01_AWVALID                 (st_hbm_axi3[01].awvalid        ),  // input wire AXI_01_AWVALID
      .AXI_01_RREADY                  (st_hbm_axi3[01].rready         ),  // input wire AXI_01_RREADY
      .AXI_01_BREADY                  (st_hbm_axi3[01].bready         ),  // input wire AXI_01_BREADY
      .AXI_01_WDATA                   (st_hbm_axi3[01].wdata          ),  // input wire [255 : 0] AXI_01_WDATA
      .AXI_01_WLAST                   (st_hbm_axi3[01].wlast          ),  // input wire AXI_01_WLAST
      .AXI_01_WSTRB                   (st_hbm_axi3[01].wstrb          ),  // input wire [31 : 0] AXI_01_WSTRB
      .AXI_01_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_01_WDATA_PARITY
      .AXI_01_WVALID                  (st_hbm_axi3[01].wvalid         ),  // input wire AXI_01_WVALID
      .AXI_01_ARREADY                 (st_hbm_axi3[01].arready        ),  // output wire AXI_01_ARREADY
      .AXI_01_AWREADY                 (st_hbm_axi3[01].awready        ),  // output wire AXI_01_AWREADY
      .AXI_01_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_01_RDATA_PARITY
      .AXI_01_RDATA                   (st_hbm_axi3[01].rdata          ),  // output wire [255 : 0] AXI_01_RDATA
      .AXI_01_RID                     (st_hbm_axi3[01].rid            ),  // output wire [5 : 0] AXI_01_RID
      .AXI_01_RLAST                   (st_hbm_axi3[01].rlast          ),  // output wire AXI_01_RLAST
      .AXI_01_RRESP                   (st_hbm_axi3[01].rresp          ),  // output wire [1 : 0] AXI_01_RRESP
      .AXI_01_RVALID                  (st_hbm_axi3[01].rvalid         ),  // output wire AXI_01_RVALID
      .AXI_01_WREADY                  (st_hbm_axi3[01].wready         ),  // output wire AXI_01_WREADY
      .AXI_01_BID                     (st_hbm_axi3[01].bid            ),  // output wire [5 : 0] AXI_01_BID
      .AXI_01_BRESP                   (st_hbm_axi3[01].bresp          ),  // output wire [1 : 0] AXI_01_BRESP
      .AXI_01_BVALID                  (st_hbm_axi3[01].bvalid         ),  // output wire AXI_01_BVALID

      .AXI_02_ACLK                    (axi_clk                        ),  // input wire AXI_02_ACLK
      .AXI_02_ARESET_N                (axi_rst_n                      ),  // input wire AXI_02_ARESET_N
      .AXI_02_ARADDR                  (st_hbm_axi3[02].araddr         ),  // input wire [33 : 0] AXI_02_ARADDR
      .AXI_02_ARBURST                 (st_hbm_axi3[02].arburst        ),  // input wire [1 : 0] AXI_02_ARBURST
      .AXI_02_ARID                    (st_hbm_axi3[02].arid           ),  // input wire [5 : 0] AXI_02_ARID
      .AXI_02_ARLEN                   (st_hbm_axi3[02].arlen          ),  // input wire [3 : 0] AXI_02_ARLEN
      .AXI_02_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_02_ARSIZE
      .AXI_02_ARVALID                 (st_hbm_axi3[02].arvalid        ),  // input wire AXI_02_ARVALID
      .AXI_02_AWADDR                  (st_hbm_axi3[02].awaddr         ),  // input wire [33 : 0] AXI_02_AWADDR
      .AXI_02_AWBURST                 (st_hbm_axi3[02].awburst        ),  // input wire [1 : 0] AXI_02_AWBURST
      .AXI_02_AWID                    (st_hbm_axi3[02].awid           ),  // input wire [5 : 0] AXI_02_AWID
      .AXI_02_AWLEN                   (st_hbm_axi3[02].awlen          ),  // input wire [3 : 0] AXI_02_AWLEN
      .AXI_02_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_02_AWSIZE
      .AXI_02_AWVALID                 (st_hbm_axi3[02].awvalid        ),  // input wire AXI_02_AWVALID
      .AXI_02_RREADY                  (st_hbm_axi3[02].rready         ),  // input wire AXI_02_RREADY
      .AXI_02_BREADY                  (st_hbm_axi3[02].bready         ),  // input wire AXI_02_BREADY
      .AXI_02_WDATA                   (st_hbm_axi3[02].wdata          ),  // input wire [255 : 0] AXI_02_WDATA
      .AXI_02_WLAST                   (st_hbm_axi3[02].wlast          ),  // input wire AXI_02_WLAST
      .AXI_02_WSTRB                   (st_hbm_axi3[02].wstrb          ),  // input wire [31 : 0] AXI_02_WSTRB
      .AXI_02_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_02_WDATA_PARITY
      .AXI_02_WVALID                  (st_hbm_axi3[02].wvalid         ),  // input wire AXI_02_WVALID
      .AXI_02_ARREADY                 (st_hbm_axi3[02].arready        ),  // output wire AXI_02_ARREADY
      .AXI_02_AWREADY                 (st_hbm_axi3[02].awready        ),  // output wire AXI_02_AWREADY
      .AXI_02_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_02_RDATA_PARITY
      .AXI_02_RDATA                   (st_hbm_axi3[02].rdata          ),  // output wire [255 : 0] AXI_02_RDATA
      .AXI_02_RID                     (st_hbm_axi3[02].rid            ),  // output wire [5 : 0] AXI_02_RID
      .AXI_02_RLAST                   (st_hbm_axi3[02].rlast          ),  // output wire AXI_02_RLAST
      .AXI_02_RRESP                   (st_hbm_axi3[02].rresp          ),  // output wire [1 : 0] AXI_02_RRESP
      .AXI_02_RVALID                  (st_hbm_axi3[02].rvalid         ),  // output wire AXI_02_RVALID
      .AXI_02_WREADY                  (st_hbm_axi3[02].wready         ),  // output wire AXI_02_WREADY
      .AXI_02_BID                     (st_hbm_axi3[02].bid            ),  // output wire [5 : 0] AXI_02_BID
      .AXI_02_BRESP                   (st_hbm_axi3[02].bresp          ),  // output wire [1 : 0] AXI_02_BRESP
      .AXI_02_BVALID                  (st_hbm_axi3[02].bvalid         ),  // output wire AXI_02_BVALID

      .AXI_03_ACLK                    (axi_clk                        ),  // input wire AXI_03_ACLK
      .AXI_03_ARESET_N                (axi_rst_n                      ),  // input wire AXI_03_ARESET_N
      .AXI_03_ARADDR                  (st_hbm_axi3[03].araddr         ),  // input wire [33 : 0] AXI_03_ARADDR
      .AXI_03_ARBURST                 (st_hbm_axi3[03].arburst        ),  // input wire [1 : 0] AXI_03_ARBURST
      .AXI_03_ARID                    (st_hbm_axi3[03].arid           ),  // input wire [5 : 0] AXI_03_ARID
      .AXI_03_ARLEN                   (st_hbm_axi3[03].arlen          ),  // input wire [3 : 0] AXI_03_ARLEN
      .AXI_03_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_03_ARSIZE
      .AXI_03_ARVALID                 (st_hbm_axi3[03].arvalid        ),  // input wire AXI_03_ARVALID
      .AXI_03_AWADDR                  (st_hbm_axi3[03].awaddr         ),  // input wire [33 : 0] AXI_03_AWADDR
      .AXI_03_AWBURST                 (st_hbm_axi3[03].awburst        ),  // input wire [1 : 0] AXI_03_AWBURST
      .AXI_03_AWID                    (st_hbm_axi3[03].awid           ),  // input wire [5 : 0] AXI_03_AWID
      .AXI_03_AWLEN                   (st_hbm_axi3[03].awlen          ),  // input wire [3 : 0] AXI_03_AWLEN
      .AXI_03_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_03_AWSIZE
      .AXI_03_AWVALID                 (st_hbm_axi3[03].awvalid        ),  // input wire AXI_03_AWVALID
      .AXI_03_RREADY                  (st_hbm_axi3[03].rready         ),  // input wire AXI_03_RREADY
      .AXI_03_BREADY                  (st_hbm_axi3[03].bready         ),  // input wire AXI_03_BREADY
      .AXI_03_WDATA                   (st_hbm_axi3[03].wdata          ),  // input wire [255 : 0] AXI_03_WDATA
      .AXI_03_WLAST                   (st_hbm_axi3[03].wlast          ),  // input wire AXI_03_WLAST
      .AXI_03_WSTRB                   (st_hbm_axi3[03].wstrb          ),  // input wire [31 : 0] AXI_03_WSTRB
      .AXI_03_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_03_WDATA_PARITY
      .AXI_03_WVALID                  (st_hbm_axi3[03].wvalid         ),  // input wire AXI_03_WVALID
      .AXI_03_ARREADY                 (st_hbm_axi3[03].arready        ),  // output wire AXI_03_ARREADY
      .AXI_03_AWREADY                 (st_hbm_axi3[03].awready        ),  // output wire AXI_03_AWREADY
      .AXI_03_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_03_RDATA_PARITY
      .AXI_03_RDATA                   (st_hbm_axi3[03].rdata          ),  // output wire [255 : 0] AXI_03_RDATA
      .AXI_03_RID                     (st_hbm_axi3[03].rid            ),  // output wire [5 : 0] AXI_03_RID
      .AXI_03_RLAST                   (st_hbm_axi3[03].rlast          ),  // output wire AXI_03_RLAST
      .AXI_03_RRESP                   (st_hbm_axi3[03].rresp          ),  // output wire [1 : 0] AXI_03_RRESP
      .AXI_03_RVALID                  (st_hbm_axi3[03].rvalid         ),  // output wire AXI_03_RVALID
      .AXI_03_WREADY                  (st_hbm_axi3[03].wready         ),  // output wire AXI_03_WREADY
      .AXI_03_BID                     (st_hbm_axi3[03].bid            ),  // output wire [5 : 0] AXI_03_BID
      .AXI_03_BRESP                   (st_hbm_axi3[03].bresp          ),  // output wire [1 : 0] AXI_03_BRESP
      .AXI_03_BVALID                  (st_hbm_axi3[03].bvalid         ),  // output wire AXI_03_BVALID

      .AXI_04_ACLK                    (axi_clk                        ),  // input wire AXI_04_ACLK
      .AXI_04_ARESET_N                (axi_rst_n                      ),  // input wire AXI_04_ARESET_N
      .AXI_04_ARADDR                  (st_hbm_axi3[04].araddr         ),  // input wire [33 : 0] AXI_04_ARADDR
      .AXI_04_ARBURST                 (st_hbm_axi3[04].arburst        ),  // input wire [1 : 0] AXI_04_ARBURST
      .AXI_04_ARID                    (st_hbm_axi3[04].arid           ),  // input wire [5 : 0] AXI_04_ARID
      .AXI_04_ARLEN                   (st_hbm_axi3[04].arlen          ),  // input wire [3 : 0] AXI_04_ARLEN
      .AXI_04_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_04_ARSIZE
      .AXI_04_ARVALID                 (st_hbm_axi3[04].arvalid        ),  // input wire AXI_04_ARVALID
      .AXI_04_AWADDR                  (st_hbm_axi3[04].awaddr         ),  // input wire [33 : 0] AXI_04_AWADDR
      .AXI_04_AWBURST                 (st_hbm_axi3[04].awburst        ),  // input wire [1 : 0] AXI_04_AWBURST
      .AXI_04_AWID                    (st_hbm_axi3[04].awid           ),  // input wire [5 : 0] AXI_04_AWID
      .AXI_04_AWLEN                   (st_hbm_axi3[04].awlen          ),  // input wire [3 : 0] AXI_04_AWLEN
      .AXI_04_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_04_AWSIZE
      .AXI_04_AWVALID                 (st_hbm_axi3[04].awvalid        ),  // input wire AXI_04_AWVALID
      .AXI_04_RREADY                  (st_hbm_axi3[04].rready         ),  // input wire AXI_04_RREADY
      .AXI_04_BREADY                  (st_hbm_axi3[04].bready         ),  // input wire AXI_04_BREADY
      .AXI_04_WDATA                   (st_hbm_axi3[04].wdata          ),  // input wire [255 : 0] AXI_04_WDATA
      .AXI_04_WLAST                   (st_hbm_axi3[04].wlast          ),  // input wire AXI_04_WLAST
      .AXI_04_WSTRB                   (st_hbm_axi3[04].wstrb          ),  // input wire [31 : 0] AXI_04_WSTRB
      .AXI_04_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_04_WDATA_PARITY
      .AXI_04_WVALID                  (st_hbm_axi3[04].wvalid         ),  // input wire AXI_04_WVALID
      .AXI_04_ARREADY                 (st_hbm_axi3[04].arready        ),  // output wire AXI_04_ARREADY
      .AXI_04_AWREADY                 (st_hbm_axi3[04].awready        ),  // output wire AXI_04_AWREADY
      .AXI_04_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_04_RDATA_PARITY
      .AXI_04_RDATA                   (st_hbm_axi3[04].rdata          ),  // output wire [255 : 0] AXI_04_RDATA
      .AXI_04_RID                     (st_hbm_axi3[04].rid            ),  // output wire [5 : 0] AXI_04_RID
      .AXI_04_RLAST                   (st_hbm_axi3[04].rlast          ),  // output wire AXI_04_RLAST
      .AXI_04_RRESP                   (st_hbm_axi3[04].rresp          ),  // output wire [1 : 0] AXI_04_RRESP
      .AXI_04_RVALID                  (st_hbm_axi3[04].rvalid         ),  // output wire AXI_04_RVALID
      .AXI_04_WREADY                  (st_hbm_axi3[04].wready         ),  // output wire AXI_04_WREADY
      .AXI_04_BID                     (st_hbm_axi3[04].bid            ),  // output wire [5 : 0] AXI_04_BID
      .AXI_04_BRESP                   (st_hbm_axi3[04].bresp          ),  // output wire [1 : 0] AXI_04_BRESP
      .AXI_04_BVALID                  (st_hbm_axi3[04].bvalid         ),  // output wire AXI_04_BVALID

      .AXI_05_ACLK                    (axi_clk                        ),  // input wire AXI_05_ACLK
      .AXI_05_ARESET_N                (axi_rst_n                      ),  // input wire AXI_05_ARESET_N
      .AXI_05_ARADDR                  (st_hbm_axi3[05].araddr         ),  // input wire [33 : 0] AXI_05_ARADDR
      .AXI_05_ARBURST                 (st_hbm_axi3[05].arburst        ),  // input wire [1 : 0] AXI_05_ARBURST
      .AXI_05_ARID                    (st_hbm_axi3[05].arid           ),  // input wire [5 : 0] AXI_05_ARID
      .AXI_05_ARLEN                   (st_hbm_axi3[05].arlen          ),  // input wire [3 : 0] AXI_05_ARLEN
      .AXI_05_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_05_ARSIZE
      .AXI_05_ARVALID                 (st_hbm_axi3[05].arvalid        ),  // input wire AXI_05_ARVALID
      .AXI_05_AWADDR                  (st_hbm_axi3[05].awaddr         ),  // input wire [33 : 0] AXI_05_AWADDR
      .AXI_05_AWBURST                 (st_hbm_axi3[05].awburst        ),  // input wire [1 : 0] AXI_05_AWBURST
      .AXI_05_AWID                    (st_hbm_axi3[05].awid           ),  // input wire [5 : 0] AXI_05_AWID
      .AXI_05_AWLEN                   (st_hbm_axi3[05].awlen          ),  // input wire [3 : 0] AXI_05_AWLEN
      .AXI_05_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_05_AWSIZE
      .AXI_05_AWVALID                 (st_hbm_axi3[05].awvalid        ),  // input wire AXI_05_AWVALID
      .AXI_05_RREADY                  (st_hbm_axi3[05].rready         ),  // input wire AXI_05_RREADY
      .AXI_05_BREADY                  (st_hbm_axi3[05].bready         ),  // input wire AXI_05_BREADY
      .AXI_05_WDATA                   (st_hbm_axi3[05].wdata          ),  // input wire [255 : 0] AXI_05_WDATA
      .AXI_05_WLAST                   (st_hbm_axi3[05].wlast          ),  // input wire AXI_05_WLAST
      .AXI_05_WSTRB                   (st_hbm_axi3[05].wstrb          ),  // input wire [31 : 0] AXI_05_WSTRB
      .AXI_05_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_05_WDATA_PARITY
      .AXI_05_WVALID                  (st_hbm_axi3[05].wvalid         ),  // input wire AXI_05_WVALID
      .AXI_05_ARREADY                 (st_hbm_axi3[05].arready        ),  // output wire AXI_05_ARREADY
      .AXI_05_AWREADY                 (st_hbm_axi3[05].awready        ),  // output wire AXI_05_AWREADY
      .AXI_05_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_05_RDATA_PARITY
      .AXI_05_RDATA                   (st_hbm_axi3[05].rdata          ),  // output wire [255 : 0] AXI_05_RDATA
      .AXI_05_RID                     (st_hbm_axi3[05].rid            ),  // output wire [5 : 0] AXI_05_RID
      .AXI_05_RLAST                   (st_hbm_axi3[05].rlast          ),  // output wire AXI_05_RLAST
      .AXI_05_RRESP                   (st_hbm_axi3[05].rresp          ),  // output wire [1 : 0] AXI_05_RRESP
      .AXI_05_RVALID                  (st_hbm_axi3[05].rvalid         ),  // output wire AXI_05_RVALID
      .AXI_05_WREADY                  (st_hbm_axi3[05].wready         ),  // output wire AXI_05_WREADY
      .AXI_05_BID                     (st_hbm_axi3[05].bid            ),  // output wire [5 : 0] AXI_05_BID
      .AXI_05_BRESP                   (st_hbm_axi3[05].bresp          ),  // output wire [1 : 0] AXI_05_BRESP
      .AXI_05_BVALID                  (st_hbm_axi3[05].bvalid         ),  // output wire AXI_05_BVALID

      .AXI_06_ACLK                    (axi_clk                        ),  // input wire AXI_06_ACLK
      .AXI_06_ARESET_N                (axi_rst_n                      ),  // input wire AXI_06_ARESET_N
      .AXI_06_ARADDR                  (st_hbm_axi3[06].araddr         ),  // input wire [33 : 0] AXI_06_ARADDR
      .AXI_06_ARBURST                 (st_hbm_axi3[06].arburst        ),  // input wire [1 : 0] AXI_06_ARBURST
      .AXI_06_ARID                    (st_hbm_axi3[06].arid           ),  // input wire [5 : 0] AXI_06_ARID
      .AXI_06_ARLEN                   (st_hbm_axi3[06].arlen          ),  // input wire [3 : 0] AXI_06_ARLEN
      .AXI_06_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_06_ARSIZE
      .AXI_06_ARVALID                 (st_hbm_axi3[06].arvalid        ),  // input wire AXI_06_ARVALID
      .AXI_06_AWADDR                  (st_hbm_axi3[06].awaddr         ),  // input wire [33 : 0] AXI_06_AWADDR
      .AXI_06_AWBURST                 (st_hbm_axi3[06].awburst        ),  // input wire [1 : 0] AXI_06_AWBURST
      .AXI_06_AWID                    (st_hbm_axi3[06].awid           ),  // input wire [5 : 0] AXI_06_AWID
      .AXI_06_AWLEN                   (st_hbm_axi3[06].awlen          ),  // input wire [3 : 0] AXI_06_AWLEN
      .AXI_06_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_06_AWSIZE
      .AXI_06_AWVALID                 (st_hbm_axi3[06].awvalid        ),  // input wire AXI_06_AWVALID
      .AXI_06_RREADY                  (st_hbm_axi3[06].rready         ),  // input wire AXI_06_RREADY
      .AXI_06_BREADY                  (st_hbm_axi3[06].bready         ),  // input wire AXI_06_BREADY
      .AXI_06_WDATA                   (st_hbm_axi3[06].wdata          ),  // input wire [255 : 0] AXI_06_WDATA
      .AXI_06_WLAST                   (st_hbm_axi3[06].wlast          ),  // input wire AXI_06_WLAST
      .AXI_06_WSTRB                   (st_hbm_axi3[06].wstrb          ),  // input wire [31 : 0] AXI_06_WSTRB
      .AXI_06_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_06_WDATA_PARITY
      .AXI_06_WVALID                  (st_hbm_axi3[06].wvalid         ),  // input wire AXI_06_WVALID
      .AXI_06_ARREADY                 (st_hbm_axi3[06].arready        ),  // output wire AXI_06_ARREADY
      .AXI_06_AWREADY                 (st_hbm_axi3[06].awready        ),  // output wire AXI_06_AWREADY
      .AXI_06_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_06_RDATA_PARITY
      .AXI_06_RDATA                   (st_hbm_axi3[06].rdata          ),  // output wire [255 : 0] AXI_06_RDATA
      .AXI_06_RID                     (st_hbm_axi3[06].rid            ),  // output wire [5 : 0] AXI_06_RID
      .AXI_06_RLAST                   (st_hbm_axi3[06].rlast          ),  // output wire AXI_06_RLAST
      .AXI_06_RRESP                   (st_hbm_axi3[06].rresp          ),  // output wire [1 : 0] AXI_06_RRESP
      .AXI_06_RVALID                  (st_hbm_axi3[06].rvalid         ),  // output wire AXI_06_RVALID
      .AXI_06_WREADY                  (st_hbm_axi3[06].wready         ),  // output wire AXI_06_WREADY
      .AXI_06_BID                     (st_hbm_axi3[06].bid            ),  // output wire [5 : 0] AXI_06_BID
      .AXI_06_BRESP                   (st_hbm_axi3[06].bresp          ),  // output wire [1 : 0] AXI_06_BRESP
      .AXI_06_BVALID                  (st_hbm_axi3[06].bvalid         ),  // output wire AXI_06_BVALID

      .AXI_07_ACLK                    (axi_clk                        ),  // input wire AXI_07_ACLK
      .AXI_07_ARESET_N                (axi_rst_n                      ),  // input wire AXI_07_ARESET_N
      .AXI_07_ARADDR                  (st_hbm_axi3[07].araddr         ),  // input wire [33 : 0] AXI_07_ARADDR
      .AXI_07_ARBURST                 (st_hbm_axi3[07].arburst        ),  // input wire [1 : 0] AXI_07_ARBURST
      .AXI_07_ARID                    (st_hbm_axi3[07].arid           ),  // input wire [5 : 0] AXI_07_ARID
      .AXI_07_ARLEN                   (st_hbm_axi3[07].arlen          ),  // input wire [3 : 0] AXI_07_ARLEN
      .AXI_07_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_07_ARSIZE
      .AXI_07_ARVALID                 (st_hbm_axi3[07].arvalid        ),  // input wire AXI_07_ARVALID
      .AXI_07_AWADDR                  (st_hbm_axi3[07].awaddr         ),  // input wire [33 : 0] AXI_07_AWADDR
      .AXI_07_AWBURST                 (st_hbm_axi3[07].awburst        ),  // input wire [1 : 0] AXI_07_AWBURST
      .AXI_07_AWID                    (st_hbm_axi3[07].awid           ),  // input wire [5 : 0] AXI_07_AWID
      .AXI_07_AWLEN                   (st_hbm_axi3[07].awlen          ),  // input wire [3 : 0] AXI_07_AWLEN
      .AXI_07_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_07_AWSIZE
      .AXI_07_AWVALID                 (st_hbm_axi3[07].awvalid        ),  // input wire AXI_07_AWVALID
      .AXI_07_RREADY                  (st_hbm_axi3[07].rready         ),  // input wire AXI_07_RREADY
      .AXI_07_BREADY                  (st_hbm_axi3[07].bready         ),  // input wire AXI_07_BREADY
      .AXI_07_WDATA                   (st_hbm_axi3[07].wdata          ),  // input wire [255 : 0] AXI_07_WDATA
      .AXI_07_WLAST                   (st_hbm_axi3[07].wlast          ),  // input wire AXI_07_WLAST
      .AXI_07_WSTRB                   (st_hbm_axi3[07].wstrb          ),  // input wire [31 : 0] AXI_07_WSTRB
      .AXI_07_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_07_WDATA_PARITY
      .AXI_07_WVALID                  (st_hbm_axi3[07].wvalid         ),  // input wire AXI_07_WVALID
      .AXI_07_ARREADY                 (st_hbm_axi3[07].arready        ),  // output wire AXI_07_ARREADY
      .AXI_07_AWREADY                 (st_hbm_axi3[07].awready        ),  // output wire AXI_07_AWREADY
      .AXI_07_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_07_RDATA_PARITY
      .AXI_07_RDATA                   (st_hbm_axi3[07].rdata          ),  // output wire [255 : 0] AXI_07_RDATA
      .AXI_07_RID                     (st_hbm_axi3[07].rid            ),  // output wire [5 : 0] AXI_07_RID
      .AXI_07_RLAST                   (st_hbm_axi3[07].rlast          ),  // output wire AXI_07_RLAST
      .AXI_07_RRESP                   (st_hbm_axi3[07].rresp          ),  // output wire [1 : 0] AXI_07_RRESP
      .AXI_07_RVALID                  (st_hbm_axi3[07].rvalid         ),  // output wire AXI_07_RVALID
      .AXI_07_WREADY                  (st_hbm_axi3[07].wready         ),  // output wire AXI_07_WREADY
      .AXI_07_BID                     (st_hbm_axi3[07].bid            ),  // output wire [5 : 0] AXI_07_BID
      .AXI_07_BRESP                   (st_hbm_axi3[07].bresp          ),  // output wire [1 : 0] AXI_07_BRESP
      .AXI_07_BVALID                  (st_hbm_axi3[07].bvalid         ),  // output wire AXI_07_BVALID

      .AXI_08_ACLK                    (axi_clk                        ),  // input wire AXI_08_ACLK
      .AXI_08_ARESET_N                (axi_rst_n                      ),  // input wire AXI_08_ARESET_N
      .AXI_08_ARADDR                  (st_hbm_axi3[08].araddr         ),  // input wire [33 : 0] AXI_08_ARADDR
      .AXI_08_ARBURST                 (st_hbm_axi3[08].arburst        ),  // input wire [1 : 0] AXI_08_ARBURST
      .AXI_08_ARID                    (st_hbm_axi3[08].arid           ),  // input wire [5 : 0] AXI_08_ARID
      .AXI_08_ARLEN                   (st_hbm_axi3[08].arlen          ),  // input wire [3 : 0] AXI_08_ARLEN
      .AXI_08_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_08_ARSIZE
      .AXI_08_ARVALID                 (st_hbm_axi3[08].arvalid        ),  // input wire AXI_08_ARVALID
      .AXI_08_AWADDR                  (st_hbm_axi3[08].awaddr         ),  // input wire [33 : 0] AXI_08_AWADDR
      .AXI_08_AWBURST                 (st_hbm_axi3[08].awburst        ),  // input wire [1 : 0] AXI_08_AWBURST
      .AXI_08_AWID                    (st_hbm_axi3[08].awid           ),  // input wire [5 : 0] AXI_08_AWID
      .AXI_08_AWLEN                   (st_hbm_axi3[08].awlen          ),  // input wire [3 : 0] AXI_08_AWLEN
      .AXI_08_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_08_AWSIZE
      .AXI_08_AWVALID                 (st_hbm_axi3[08].awvalid        ),  // input wire AXI_08_AWVALID
      .AXI_08_RREADY                  (st_hbm_axi3[08].rready         ),  // input wire AXI_08_RREADY
      .AXI_08_BREADY                  (st_hbm_axi3[08].bready         ),  // input wire AXI_08_BREADY
      .AXI_08_WDATA                   (st_hbm_axi3[08].wdata          ),  // input wire [255 : 0] AXI_08_WDATA
      .AXI_08_WLAST                   (st_hbm_axi3[08].wlast          ),  // input wire AXI_08_WLAST
      .AXI_08_WSTRB                   (st_hbm_axi3[08].wstrb          ),  // input wire [31 : 0] AXI_08_WSTRB
      .AXI_08_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_08_WDATA_PARITY
      .AXI_08_WVALID                  (st_hbm_axi3[08].wvalid         ),  // input wire AXI_08_WVALID
      .AXI_08_ARREADY                 (st_hbm_axi3[08].arready        ),  // output wire AXI_08_ARREADY
      .AXI_08_AWREADY                 (st_hbm_axi3[08].awready        ),  // output wire AXI_08_AWREADY
      .AXI_08_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_08_RDATA_PARITY
      .AXI_08_RDATA                   (st_hbm_axi3[08].rdata          ),  // output wire [255 : 0] AXI_08_RDATA
      .AXI_08_RID                     (st_hbm_axi3[08].rid            ),  // output wire [5 : 0] AXI_08_RID
      .AXI_08_RLAST                   (st_hbm_axi3[08].rlast          ),  // output wire AXI_08_RLAST
      .AXI_08_RRESP                   (st_hbm_axi3[08].rresp          ),  // output wire [1 : 0] AXI_08_RRESP
      .AXI_08_RVALID                  (st_hbm_axi3[08].rvalid         ),  // output wire AXI_08_RVALID
      .AXI_08_WREADY                  (st_hbm_axi3[08].wready         ),  // output wire AXI_08_WREADY
      .AXI_08_BID                     (st_hbm_axi3[08].bid            ),  // output wire [5 : 0] AXI_08_BID
      .AXI_08_BRESP                   (st_hbm_axi3[08].bresp          ),  // output wire [1 : 0] AXI_08_BRESP
      .AXI_08_BVALID                  (st_hbm_axi3[08].bvalid         ),  // output wire AXI_08_BVALID

      .AXI_09_ACLK                    (axi_clk                        ),  // input wire AXI_09_ACLK
      .AXI_09_ARESET_N                (axi_rst_n                      ),  // input wire AXI_09_ARESET_N
      .AXI_09_ARADDR                  (st_hbm_axi3[09].araddr         ),  // input wire [33 : 0] AXI_09_ARADDR
      .AXI_09_ARBURST                 (st_hbm_axi3[09].arburst        ),  // input wire [1 : 0] AXI_09_ARBURST
      .AXI_09_ARID                    (st_hbm_axi3[09].arid           ),  // input wire [5 : 0] AXI_09_ARID
      .AXI_09_ARLEN                   (st_hbm_axi3[09].arlen          ),  // input wire [3 : 0] AXI_09_ARLEN
      .AXI_09_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_09_ARSIZE
      .AXI_09_ARVALID                 (st_hbm_axi3[09].arvalid        ),  // input wire AXI_09_ARVALID
      .AXI_09_AWADDR                  (st_hbm_axi3[09].awaddr         ),  // input wire [33 : 0] AXI_09_AWADDR
      .AXI_09_AWBURST                 (st_hbm_axi3[09].awburst        ),  // input wire [1 : 0] AXI_09_AWBURST
      .AXI_09_AWID                    (st_hbm_axi3[09].awid           ),  // input wire [5 : 0] AXI_09_AWID
      .AXI_09_AWLEN                   (st_hbm_axi3[09].awlen          ),  // input wire [3 : 0] AXI_09_AWLEN
      .AXI_09_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_09_AWSIZE
      .AXI_09_AWVALID                 (st_hbm_axi3[09].awvalid        ),  // input wire AXI_09_AWVALID
      .AXI_09_RREADY                  (st_hbm_axi3[09].rready         ),  // input wire AXI_09_RREADY
      .AXI_09_BREADY                  (st_hbm_axi3[09].bready         ),  // input wire AXI_09_BREADY
      .AXI_09_WDATA                   (st_hbm_axi3[09].wdata          ),  // input wire [255 : 0] AXI_09_WDATA
      .AXI_09_WLAST                   (st_hbm_axi3[09].wlast          ),  // input wire AXI_09_WLAST
      .AXI_09_WSTRB                   (st_hbm_axi3[09].wstrb          ),  // input wire [31 : 0] AXI_09_WSTRB
      .AXI_09_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_09_WDATA_PARITY
      .AXI_09_WVALID                  (st_hbm_axi3[09].wvalid         ),  // input wire AXI_09_WVALID
      .AXI_09_ARREADY                 (st_hbm_axi3[09].arready        ),  // output wire AXI_09_ARREADY
      .AXI_09_AWREADY                 (st_hbm_axi3[09].awready        ),  // output wire AXI_09_AWREADY
      .AXI_09_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_09_RDATA_PARITY
      .AXI_09_RDATA                   (st_hbm_axi3[09].rdata          ),  // output wire [255 : 0] AXI_09_RDATA
      .AXI_09_RID                     (st_hbm_axi3[09].rid            ),  // output wire [5 : 0] AXI_09_RID
      .AXI_09_RLAST                   (st_hbm_axi3[09].rlast          ),  // output wire AXI_09_RLAST
      .AXI_09_RRESP                   (st_hbm_axi3[09].rresp          ),  // output wire [1 : 0] AXI_09_RRESP
      .AXI_09_RVALID                  (st_hbm_axi3[09].rvalid         ),  // output wire AXI_09_RVALID
      .AXI_09_WREADY                  (st_hbm_axi3[09].wready         ),  // output wire AXI_09_WREADY
      .AXI_09_BID                     (st_hbm_axi3[09].bid            ),  // output wire [5 : 0] AXI_09_BID
      .AXI_09_BRESP                   (st_hbm_axi3[09].bresp          ),  // output wire [1 : 0] AXI_09_BRESP
      .AXI_09_BVALID                  (st_hbm_axi3[09].bvalid         ),  // output wire AXI_09_BVALID

      .AXI_10_ACLK                    (axi_clk                        ),  // input wire AXI_10_ACLK
      .AXI_10_ARESET_N                (axi_rst_n                      ),  // input wire AXI_10_ARESET_N
      .AXI_10_ARADDR                  (st_hbm_axi3[10].araddr         ),  // input wire [33 : 0] AXI_10_ARADDR
      .AXI_10_ARBURST                 (st_hbm_axi3[10].arburst        ),  // input wire [1 : 0] AXI_10_ARBURST
      .AXI_10_ARID                    (st_hbm_axi3[10].arid           ),  // input wire [5 : 0] AXI_10_ARID
      .AXI_10_ARLEN                   (st_hbm_axi3[10].arlen          ),  // input wire [3 : 0] AXI_10_ARLEN
      .AXI_10_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_10_ARSIZE
      .AXI_10_ARVALID                 (st_hbm_axi3[10].arvalid        ),  // input wire AXI_10_ARVALID
      .AXI_10_AWADDR                  (st_hbm_axi3[10].awaddr         ),  // input wire [33 : 0] AXI_10_AWADDR
      .AXI_10_AWBURST                 (st_hbm_axi3[10].awburst        ),  // input wire [1 : 0] AXI_10_AWBURST
      .AXI_10_AWID                    (st_hbm_axi3[10].awid           ),  // input wire [5 : 0] AXI_10_AWID
      .AXI_10_AWLEN                   (st_hbm_axi3[10].awlen          ),  // input wire [3 : 0] AXI_10_AWLEN
      .AXI_10_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_10_AWSIZE
      .AXI_10_AWVALID                 (st_hbm_axi3[10].awvalid        ),  // input wire AXI_10_AWVALID
      .AXI_10_RREADY                  (st_hbm_axi3[10].rready         ),  // input wire AXI_10_RREADY
      .AXI_10_BREADY                  (st_hbm_axi3[10].bready         ),  // input wire AXI_10_BREADY
      .AXI_10_WDATA                   (st_hbm_axi3[10].wdata          ),  // input wire [255 : 0] AXI_10_WDATA
      .AXI_10_WLAST                   (st_hbm_axi3[10].wlast          ),  // input wire AXI_10_WLAST
      .AXI_10_WSTRB                   (st_hbm_axi3[10].wstrb          ),  // input wire [31 : 0] AXI_10_WSTRB
      .AXI_10_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_10_WDATA_PARITY
      .AXI_10_WVALID                  (st_hbm_axi3[10].wvalid         ),  // input wire AXI_10_WVALID
      .AXI_10_ARREADY                 (st_hbm_axi3[10].arready        ),  // output wire AXI_10_ARREADY
      .AXI_10_AWREADY                 (st_hbm_axi3[10].awready        ),  // output wire AXI_10_AWREADY
      .AXI_10_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_10_RDATA_PARITY
      .AXI_10_RDATA                   (st_hbm_axi3[10].rdata          ),  // output wire [255 : 0] AXI_10_RDATA
      .AXI_10_RID                     (st_hbm_axi3[10].rid            ),  // output wire [5 : 0] AXI_10_RID
      .AXI_10_RLAST                   (st_hbm_axi3[10].rlast          ),  // output wire AXI_10_RLAST
      .AXI_10_RRESP                   (st_hbm_axi3[10].rresp          ),  // output wire [1 : 0] AXI_10_RRESP
      .AXI_10_RVALID                  (st_hbm_axi3[10].rvalid         ),  // output wire AXI_10_RVALID
      .AXI_10_WREADY                  (st_hbm_axi3[10].wready         ),  // output wire AXI_10_WREADY
      .AXI_10_BID                     (st_hbm_axi3[10].bid            ),  // output wire [5 : 0] AXI_10_BID
      .AXI_10_BRESP                   (st_hbm_axi3[10].bresp          ),  // output wire [1 : 0] AXI_10_BRESP
      .AXI_10_BVALID                  (st_hbm_axi3[10].bvalid         ),  // output wire AXI_10_BVALID

      .AXI_11_ACLK                    (axi_clk                        ),  // input wire AXI_11_ACLK
      .AXI_11_ARESET_N                (axi_rst_n                      ),  // input wire AXI_11_ARESET_N
      .AXI_11_ARADDR                  (st_hbm_axi3[11].araddr         ),  // input wire [33 : 0] AXI_11_ARADDR
      .AXI_11_ARBURST                 (st_hbm_axi3[11].arburst        ),  // input wire [1 : 0] AXI_11_ARBURST
      .AXI_11_ARID                    (st_hbm_axi3[11].arid           ),  // input wire [5 : 0] AXI_11_ARID
      .AXI_11_ARLEN                   (st_hbm_axi3[11].arlen          ),  // input wire [3 : 0] AXI_11_ARLEN
      .AXI_11_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_11_ARSIZE
      .AXI_11_ARVALID                 (st_hbm_axi3[11].arvalid        ),  // input wire AXI_11_ARVALID
      .AXI_11_AWADDR                  (st_hbm_axi3[11].awaddr         ),  // input wire [33 : 0] AXI_11_AWADDR
      .AXI_11_AWBURST                 (st_hbm_axi3[11].awburst        ),  // input wire [1 : 0] AXI_11_AWBURST
      .AXI_11_AWID                    (st_hbm_axi3[11].awid           ),  // input wire [5 : 0] AXI_11_AWID
      .AXI_11_AWLEN                   (st_hbm_axi3[11].awlen          ),  // input wire [3 : 0] AXI_11_AWLEN
      .AXI_11_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_11_AWSIZE
      .AXI_11_AWVALID                 (st_hbm_axi3[11].awvalid        ),  // input wire AXI_11_AWVALID
      .AXI_11_RREADY                  (st_hbm_axi3[11].rready         ),  // input wire AXI_11_RREADY
      .AXI_11_BREADY                  (st_hbm_axi3[11].bready         ),  // input wire AXI_11_BREADY
      .AXI_11_WDATA                   (st_hbm_axi3[11].wdata          ),  // input wire [255 : 0] AXI_11_WDATA
      .AXI_11_WLAST                   (st_hbm_axi3[11].wlast          ),  // input wire AXI_11_WLAST
      .AXI_11_WSTRB                   (st_hbm_axi3[11].wstrb          ),  // input wire [31 : 0] AXI_11_WSTRB
      .AXI_11_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_11_WDATA_PARITY
      .AXI_11_WVALID                  (st_hbm_axi3[11].wvalid         ),  // input wire AXI_11_WVALID
      .AXI_11_ARREADY                 (st_hbm_axi3[11].arready        ),  // output wire AXI_11_ARREADY
      .AXI_11_AWREADY                 (st_hbm_axi3[11].awready        ),  // output wire AXI_11_AWREADY
      .AXI_11_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_11_RDATA_PARITY
      .AXI_11_RDATA                   (st_hbm_axi3[11].rdata          ),  // output wire [255 : 0] AXI_11_RDATA
      .AXI_11_RID                     (st_hbm_axi3[11].rid            ),  // output wire [5 : 0] AXI_11_RID
      .AXI_11_RLAST                   (st_hbm_axi3[11].rlast          ),  // output wire AXI_11_RLAST
      .AXI_11_RRESP                   (st_hbm_axi3[11].rresp          ),  // output wire [1 : 0] AXI_11_RRESP
      .AXI_11_RVALID                  (st_hbm_axi3[11].rvalid         ),  // output wire AXI_11_RVALID
      .AXI_11_WREADY                  (st_hbm_axi3[11].wready         ),  // output wire AXI_11_WREADY
      .AXI_11_BID                     (st_hbm_axi3[11].bid            ),  // output wire [5 : 0] AXI_11_BID
      .AXI_11_BRESP                   (st_hbm_axi3[11].bresp          ),  // output wire [1 : 0] AXI_11_BRESP
      .AXI_11_BVALID                  (st_hbm_axi3[11].bvalid         ),  // output wire AXI_11_BVALID

      .AXI_12_ACLK                    (axi_clk                        ),  // input wire AXI_12_ACLK
      .AXI_12_ARESET_N                (axi_rst_n                      ),  // input wire AXI_12_ARESET_N
      .AXI_12_ARADDR                  (st_hbm_axi3[12].araddr         ),  // input wire [33 : 0] AXI_12_ARADDR
      .AXI_12_ARBURST                 (st_hbm_axi3[12].arburst        ),  // input wire [1 : 0] AXI_12_ARBURST
      .AXI_12_ARID                    (st_hbm_axi3[12].arid           ),  // input wire [5 : 0] AXI_12_ARID
      .AXI_12_ARLEN                   (st_hbm_axi3[12].arlen          ),  // input wire [3 : 0] AXI_12_ARLEN
      .AXI_12_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_12_ARSIZE
      .AXI_12_ARVALID                 (st_hbm_axi3[12].arvalid        ),  // input wire AXI_12_ARVALID
      .AXI_12_AWADDR                  (st_hbm_axi3[12].awaddr         ),  // input wire [33 : 0] AXI_12_AWADDR
      .AXI_12_AWBURST                 (st_hbm_axi3[12].awburst        ),  // input wire [1 : 0] AXI_12_AWBURST
      .AXI_12_AWID                    (st_hbm_axi3[12].awid           ),  // input wire [5 : 0] AXI_12_AWID
      .AXI_12_AWLEN                   (st_hbm_axi3[12].awlen          ),  // input wire [3 : 0] AXI_12_AWLEN
      .AXI_12_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_12_AWSIZE
      .AXI_12_AWVALID                 (st_hbm_axi3[12].awvalid        ),  // input wire AXI_12_AWVALID
      .AXI_12_RREADY                  (st_hbm_axi3[12].rready         ),  // input wire AXI_12_RREADY
      .AXI_12_BREADY                  (st_hbm_axi3[12].bready         ),  // input wire AXI_12_BREADY
      .AXI_12_WDATA                   (st_hbm_axi3[12].wdata          ),  // input wire [255 : 0] AXI_12_WDATA
      .AXI_12_WLAST                   (st_hbm_axi3[12].wlast          ),  // input wire AXI_12_WLAST
      .AXI_12_WSTRB                   (st_hbm_axi3[12].wstrb          ),  // input wire [31 : 0] AXI_12_WSTRB
      .AXI_12_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_12_WDATA_PARITY
      .AXI_12_WVALID                  (st_hbm_axi3[12].wvalid         ),  // input wire AXI_12_WVALID
      .AXI_12_ARREADY                 (st_hbm_axi3[12].arready        ),  // output wire AXI_12_ARREADY
      .AXI_12_AWREADY                 (st_hbm_axi3[12].awready        ),  // output wire AXI_12_AWREADY
      .AXI_12_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_12_RDATA_PARITY
      .AXI_12_RDATA                   (st_hbm_axi3[12].rdata          ),  // output wire [255 : 0] AXI_12_RDATA
      .AXI_12_RID                     (st_hbm_axi3[12].rid            ),  // output wire [5 : 0] AXI_12_RID
      .AXI_12_RLAST                   (st_hbm_axi3[12].rlast          ),  // output wire AXI_12_RLAST
      .AXI_12_RRESP                   (st_hbm_axi3[12].rresp          ),  // output wire [1 : 0] AXI_12_RRESP
      .AXI_12_RVALID                  (st_hbm_axi3[12].rvalid         ),  // output wire AXI_12_RVALID
      .AXI_12_WREADY                  (st_hbm_axi3[12].wready         ),  // output wire AXI_12_WREADY
      .AXI_12_BID                     (st_hbm_axi3[12].bid            ),  // output wire [5 : 0] AXI_12_BID
      .AXI_12_BRESP                   (st_hbm_axi3[12].bresp          ),  // output wire [1 : 0] AXI_12_BRESP
      .AXI_12_BVALID                  (st_hbm_axi3[12].bvalid         ),  // output wire AXI_12_BVALID

      .AXI_13_ACLK                    (axi_clk                        ),  // input wire AXI_13_ACLK
      .AXI_13_ARESET_N                (axi_rst_n                      ),  // input wire AXI_13_ARESET_N
      .AXI_13_ARADDR                  (st_hbm_axi3[13].araddr         ),  // input wire [33 : 0] AXI_13_ARADDR
      .AXI_13_ARBURST                 (st_hbm_axi3[13].arburst        ),  // input wire [1 : 0] AXI_13_ARBURST
      .AXI_13_ARID                    (st_hbm_axi3[13].arid           ),  // input wire [5 : 0] AXI_13_ARID
      .AXI_13_ARLEN                   (st_hbm_axi3[13].arlen          ),  // input wire [3 : 0] AXI_13_ARLEN
      .AXI_13_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_13_ARSIZE
      .AXI_13_ARVALID                 (st_hbm_axi3[13].arvalid        ),  // input wire AXI_13_ARVALID
      .AXI_13_AWADDR                  (st_hbm_axi3[13].awaddr         ),  // input wire [33 : 0] AXI_13_AWADDR
      .AXI_13_AWBURST                 (st_hbm_axi3[13].awburst        ),  // input wire [1 : 0] AXI_13_AWBURST
      .AXI_13_AWID                    (st_hbm_axi3[13].awid           ),  // input wire [5 : 0] AXI_13_AWID
      .AXI_13_AWLEN                   (st_hbm_axi3[13].awlen          ),  // input wire [3 : 0] AXI_13_AWLEN
      .AXI_13_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_13_AWSIZE
      .AXI_13_AWVALID                 (st_hbm_axi3[13].awvalid        ),  // input wire AXI_13_AWVALID
      .AXI_13_RREADY                  (st_hbm_axi3[13].rready         ),  // input wire AXI_13_RREADY
      .AXI_13_BREADY                  (st_hbm_axi3[13].bready         ),  // input wire AXI_13_BREADY
      .AXI_13_WDATA                   (st_hbm_axi3[13].wdata          ),  // input wire [255 : 0] AXI_13_WDATA
      .AXI_13_WLAST                   (st_hbm_axi3[13].wlast          ),  // input wire AXI_13_WLAST
      .AXI_13_WSTRB                   (st_hbm_axi3[13].wstrb          ),  // input wire [31 : 0] AXI_13_WSTRB
      .AXI_13_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_13_WDATA_PARITY
      .AXI_13_WVALID                  (st_hbm_axi3[13].wvalid         ),  // input wire AXI_13_WVALID
      .AXI_13_ARREADY                 (st_hbm_axi3[13].arready        ),  // output wire AXI_13_ARREADY
      .AXI_13_AWREADY                 (st_hbm_axi3[13].awready        ),  // output wire AXI_13_AWREADY
      .AXI_13_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_13_RDATA_PARITY
      .AXI_13_RDATA                   (st_hbm_axi3[13].rdata          ),  // output wire [255 : 0] AXI_13_RDATA
      .AXI_13_RID                     (st_hbm_axi3[13].rid            ),  // output wire [5 : 0] AXI_13_RID
      .AXI_13_RLAST                   (st_hbm_axi3[13].rlast          ),  // output wire AXI_13_RLAST
      .AXI_13_RRESP                   (st_hbm_axi3[13].rresp          ),  // output wire [1 : 0] AXI_13_RRESP
      .AXI_13_RVALID                  (st_hbm_axi3[13].rvalid         ),  // output wire AXI_13_RVALID
      .AXI_13_WREADY                  (st_hbm_axi3[13].wready         ),  // output wire AXI_13_WREADY
      .AXI_13_BID                     (st_hbm_axi3[13].bid            ),  // output wire [5 : 0] AXI_13_BID
      .AXI_13_BRESP                   (st_hbm_axi3[13].bresp          ),  // output wire [1 : 0] AXI_13_BRESP
      .AXI_13_BVALID                  (st_hbm_axi3[13].bvalid         ),  // output wire AXI_13_BVALID

      .AXI_14_ACLK                    (axi_clk                        ),  // input wire AXI_14_ACLK
      .AXI_14_ARESET_N                (axi_rst_n                      ),  // input wire AXI_14_ARESET_N
      .AXI_14_ARADDR                  (st_hbm_axi3[14].araddr         ),  // input wire [33 : 0] AXI_14_ARADDR
      .AXI_14_ARBURST                 (st_hbm_axi3[14].arburst        ),  // input wire [1 : 0] AXI_14_ARBURST
      .AXI_14_ARID                    (st_hbm_axi3[14].arid           ),  // input wire [5 : 0] AXI_14_ARID
      .AXI_14_ARLEN                   (st_hbm_axi3[14].arlen          ),  // input wire [3 : 0] AXI_14_ARLEN
      .AXI_14_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_14_ARSIZE
      .AXI_14_ARVALID                 (st_hbm_axi3[14].arvalid        ),  // input wire AXI_14_ARVALID
      .AXI_14_AWADDR                  (st_hbm_axi3[14].awaddr         ),  // input wire [33 : 0] AXI_14_AWADDR
      .AXI_14_AWBURST                 (st_hbm_axi3[14].awburst        ),  // input wire [1 : 0] AXI_14_AWBURST
      .AXI_14_AWID                    (st_hbm_axi3[14].awid           ),  // input wire [5 : 0] AXI_14_AWID
      .AXI_14_AWLEN                   (st_hbm_axi3[14].awlen          ),  // input wire [3 : 0] AXI_14_AWLEN
      .AXI_14_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_14_AWSIZE
      .AXI_14_AWVALID                 (st_hbm_axi3[14].awvalid        ),  // input wire AXI_14_AWVALID
      .AXI_14_RREADY                  (st_hbm_axi3[14].rready         ),  // input wire AXI_14_RREADY
      .AXI_14_BREADY                  (st_hbm_axi3[14].bready         ),  // input wire AXI_14_BREADY
      .AXI_14_WDATA                   (st_hbm_axi3[14].wdata          ),  // input wire [255 : 0] AXI_14_WDATA
      .AXI_14_WLAST                   (st_hbm_axi3[14].wlast          ),  // input wire AXI_14_WLAST
      .AXI_14_WSTRB                   (st_hbm_axi3[14].wstrb          ),  // input wire [31 : 0] AXI_14_WSTRB
      .AXI_14_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_14_WDATA_PARITY
      .AXI_14_WVALID                  (st_hbm_axi3[14].wvalid         ),  // input wire AXI_14_WVALID
      .AXI_14_ARREADY                 (st_hbm_axi3[14].arready        ),  // output wire AXI_14_ARREADY
      .AXI_14_AWREADY                 (st_hbm_axi3[14].awready        ),  // output wire AXI_14_AWREADY
      .AXI_14_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_14_RDATA_PARITY
      .AXI_14_RDATA                   (st_hbm_axi3[14].rdata          ),  // output wire [255 : 0] AXI_14_RDATA
      .AXI_14_RID                     (st_hbm_axi3[14].rid            ),  // output wire [5 : 0] AXI_14_RID
      .AXI_14_RLAST                   (st_hbm_axi3[14].rlast          ),  // output wire AXI_14_RLAST
      .AXI_14_RRESP                   (st_hbm_axi3[14].rresp          ),  // output wire [1 : 0] AXI_14_RRESP
      .AXI_14_RVALID                  (st_hbm_axi3[14].rvalid         ),  // output wire AXI_14_RVALID
      .AXI_14_WREADY                  (st_hbm_axi3[14].wready         ),  // output wire AXI_14_WREADY
      .AXI_14_BID                     (st_hbm_axi3[14].bid            ),  // output wire [5 : 0] AXI_14_BID
      .AXI_14_BRESP                   (st_hbm_axi3[14].bresp          ),  // output wire [1 : 0] AXI_14_BRESP
      .AXI_14_BVALID                  (st_hbm_axi3[14].bvalid         ),  // output wire AXI_14_BVALID

      .AXI_15_ACLK                    (axi_clk                        ),  // input wire AXI_15_ACLK
      .AXI_15_ARESET_N                (axi_rst_n                      ),  // input wire AXI_15_ARESET_N
      .AXI_15_ARADDR                  (st_hbm_axi3[15].araddr         ),  // input wire [33 : 0] AXI_15_ARADDR
      .AXI_15_ARBURST                 (st_hbm_axi3[15].arburst        ),  // input wire [1 : 0] AXI_15_ARBURST
      .AXI_15_ARID                    (st_hbm_axi3[15].arid           ),  // input wire [5 : 0] AXI_15_ARID
      .AXI_15_ARLEN                   (st_hbm_axi3[15].arlen          ),  // input wire [3 : 0] AXI_15_ARLEN
      .AXI_15_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_15_ARSIZE
      .AXI_15_ARVALID                 (st_hbm_axi3[15].arvalid        ),  // input wire AXI_15_ARVALID
      .AXI_15_AWADDR                  (st_hbm_axi3[15].awaddr         ),  // input wire [33 : 0] AXI_15_AWADDR
      .AXI_15_AWBURST                 (st_hbm_axi3[15].awburst        ),  // input wire [1 : 0] AXI_15_AWBURST
      .AXI_15_AWID                    (st_hbm_axi3[15].awid           ),  // input wire [5 : 0] AXI_15_AWID
      .AXI_15_AWLEN                   (st_hbm_axi3[15].awlen          ),  // input wire [3 : 0] AXI_15_AWLEN
      .AXI_15_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_15_AWSIZE
      .AXI_15_AWVALID                 (st_hbm_axi3[15].awvalid        ),  // input wire AXI_15_AWVALID
      .AXI_15_RREADY                  (st_hbm_axi3[15].rready         ),  // input wire AXI_15_RREADY
      .AXI_15_BREADY                  (st_hbm_axi3[15].bready         ),  // input wire AXI_15_BREADY
      .AXI_15_WDATA                   (st_hbm_axi3[15].wdata          ),  // input wire [255 : 0] AXI_15_WDATA
      .AXI_15_WLAST                   (st_hbm_axi3[15].wlast          ),  // input wire AXI_15_WLAST
      .AXI_15_WSTRB                   (st_hbm_axi3[15].wstrb          ),  // input wire [31 : 0] AXI_15_WSTRB
      .AXI_15_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_15_WDATA_PARITY
      .AXI_15_WVALID                  (st_hbm_axi3[15].wvalid         ),  // input wire AXI_15_WVALID
      .AXI_15_ARREADY                 (st_hbm_axi3[15].arready        ),  // output wire AXI_15_ARREADY
      .AXI_15_AWREADY                 (st_hbm_axi3[15].awready        ),  // output wire AXI_15_AWREADY
      .AXI_15_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_15_RDATA_PARITY
      .AXI_15_RDATA                   (st_hbm_axi3[15].rdata          ),  // output wire [255 : 0] AXI_15_RDATA
      .AXI_15_RID                     (st_hbm_axi3[15].rid            ),  // output wire [5 : 0] AXI_15_RID
      .AXI_15_RLAST                   (st_hbm_axi3[15].rlast          ),  // output wire AXI_15_RLAST
      .AXI_15_RRESP                   (st_hbm_axi3[15].rresp          ),  // output wire [1 : 0] AXI_15_RRESP
      .AXI_15_RVALID                  (st_hbm_axi3[15].rvalid         ),  // output wire AXI_15_RVALID
      .AXI_15_WREADY                  (st_hbm_axi3[15].wready         ),  // output wire AXI_15_WREADY
      .AXI_15_BID                     (st_hbm_axi3[15].bid            ),  // output wire [5 : 0] AXI_15_BID
      .AXI_15_BRESP                   (st_hbm_axi3[15].bresp          ),  // output wire [1 : 0] AXI_15_BRESP
      .AXI_15_BVALID                  (st_hbm_axi3[15].bvalid         ),  // output wire AXI_15_BVALID

      .AXI_16_ACLK                    (axi_clk                        ),  // input wire AXI_16_ACLK
      .AXI_16_ARESET_N                (axi_rst_n                      ),  // input wire AXI_16_ARESET_N
      .AXI_16_ARADDR                  (st_hbm_axi3[16].araddr         ),  // input wire [33 : 0] AXI_16_ARADDR
      .AXI_16_ARBURST                 (st_hbm_axi3[16].arburst        ),  // input wire [1 : 0] AXI_16_ARBURST
      .AXI_16_ARID                    (st_hbm_axi3[16].arid           ),  // input wire [5 : 0] AXI_16_ARID
      .AXI_16_ARLEN                   (st_hbm_axi3[16].arlen          ),  // input wire [3 : 0] AXI_16_ARLEN
      .AXI_16_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_16_ARSIZE
      .AXI_16_ARVALID                 (st_hbm_axi3[16].arvalid        ),  // input wire AXI_16_ARVALID
      .AXI_16_AWADDR                  (st_hbm_axi3[16].awaddr         ),  // input wire [33 : 0] AXI_16_AWADDR
      .AXI_16_AWBURST                 (st_hbm_axi3[16].awburst        ),  // input wire [1 : 0] AXI_16_AWBURST
      .AXI_16_AWID                    (st_hbm_axi3[16].awid           ),  // input wire [5 : 0] AXI_16_AWID
      .AXI_16_AWLEN                   (st_hbm_axi3[16].awlen          ),  // input wire [3 : 0] AXI_16_AWLEN
      .AXI_16_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_16_AWSIZE
      .AXI_16_AWVALID                 (st_hbm_axi3[16].awvalid        ),  // input wire AXI_16_AWVALID
      .AXI_16_RREADY                  (st_hbm_axi3[16].rready         ),  // input wire AXI_16_RREADY
      .AXI_16_BREADY                  (st_hbm_axi3[16].bready         ),  // input wire AXI_16_BREADY
      .AXI_16_WDATA                   (st_hbm_axi3[16].wdata          ),  // input wire [255 : 0] AXI_16_WDATA
      .AXI_16_WLAST                   (st_hbm_axi3[16].wlast          ),  // input wire AXI_16_WLAST
      .AXI_16_WSTRB                   (st_hbm_axi3[16].wstrb          ),  // input wire [31 : 0] AXI_16_WSTRB
      .AXI_16_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_16_WDATA_PARITY
      .AXI_16_WVALID                  (st_hbm_axi3[16].wvalid         ),  // input wire AXI_16_WVALID
      .AXI_16_ARREADY                 (st_hbm_axi3[16].arready        ),  // output wire AXI_16_ARREADY
      .AXI_16_AWREADY                 (st_hbm_axi3[16].awready        ),  // output wire AXI_16_AWREADY
      .AXI_16_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_16_RDATA_PARITY
      .AXI_16_RDATA                   (st_hbm_axi3[16].rdata          ),  // output wire [255 : 0] AXI_16_RDATA
      .AXI_16_RID                     (st_hbm_axi3[16].rid            ),  // output wire [5 : 0] AXI_16_RID
      .AXI_16_RLAST                   (st_hbm_axi3[16].rlast          ),  // output wire AXI_16_RLAST
      .AXI_16_RRESP                   (st_hbm_axi3[16].rresp          ),  // output wire [1 : 0] AXI_16_RRESP
      .AXI_16_RVALID                  (st_hbm_axi3[16].rvalid         ),  // output wire AXI_16_RVALID
      .AXI_16_WREADY                  (st_hbm_axi3[16].wready         ),  // output wire AXI_16_WREADY
      .AXI_16_BID                     (st_hbm_axi3[16].bid            ),  // output wire [5 : 0] AXI_16_BID
      .AXI_16_BRESP                   (st_hbm_axi3[16].bresp          ),  // output wire [1 : 0] AXI_16_BRESP
      .AXI_16_BVALID                  (st_hbm_axi3[16].bvalid         ),  // output wire AXI_16_BVALID

      .AXI_17_ACLK                    (axi_clk                        ),  // input wire AXI_17_ACLK
      .AXI_17_ARESET_N                (axi_rst_n                      ),  // input wire AXI_17_ARESET_N
      .AXI_17_ARADDR                  (st_hbm_axi3[17].araddr         ),  // input wire [33 : 0] AXI_17_ARADDR
      .AXI_17_ARBURST                 (st_hbm_axi3[17].arburst        ),  // input wire [1 : 0] AXI_17_ARBURST
      .AXI_17_ARID                    (st_hbm_axi3[17].arid           ),  // input wire [5 : 0] AXI_17_ARID
      .AXI_17_ARLEN                   (st_hbm_axi3[17].arlen          ),  // input wire [3 : 0] AXI_17_ARLEN
      .AXI_17_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_17_ARSIZE
      .AXI_17_ARVALID                 (st_hbm_axi3[17].arvalid        ),  // input wire AXI_17_ARVALID
      .AXI_17_AWADDR                  (st_hbm_axi3[17].awaddr         ),  // input wire [33 : 0] AXI_17_AWADDR
      .AXI_17_AWBURST                 (st_hbm_axi3[17].awburst        ),  // input wire [1 : 0] AXI_17_AWBURST
      .AXI_17_AWID                    (st_hbm_axi3[17].awid           ),  // input wire [5 : 0] AXI_17_AWID
      .AXI_17_AWLEN                   (st_hbm_axi3[17].awlen          ),  // input wire [3 : 0] AXI_17_AWLEN
      .AXI_17_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_17_AWSIZE
      .AXI_17_AWVALID                 (st_hbm_axi3[17].awvalid        ),  // input wire AXI_17_AWVALID
      .AXI_17_RREADY                  (st_hbm_axi3[17].rready         ),  // input wire AXI_17_RREADY
      .AXI_17_BREADY                  (st_hbm_axi3[17].bready         ),  // input wire AXI_17_BREADY
      .AXI_17_WDATA                   (st_hbm_axi3[17].wdata          ),  // input wire [255 : 0] AXI_17_WDATA
      .AXI_17_WLAST                   (st_hbm_axi3[17].wlast          ),  // input wire AXI_17_WLAST
      .AXI_17_WSTRB                   (st_hbm_axi3[17].wstrb          ),  // input wire [31 : 0] AXI_17_WSTRB
      .AXI_17_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_17_WDATA_PARITY
      .AXI_17_WVALID                  (st_hbm_axi3[17].wvalid         ),  // input wire AXI_17_WVALID
      .AXI_17_ARREADY                 (st_hbm_axi3[17].arready        ),  // output wire AXI_17_ARREADY
      .AXI_17_AWREADY                 (st_hbm_axi3[17].awready        ),  // output wire AXI_17_AWREADY
      .AXI_17_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_17_RDATA_PARITY
      .AXI_17_RDATA                   (st_hbm_axi3[17].rdata          ),  // output wire [255 : 0] AXI_17_RDATA
      .AXI_17_RID                     (st_hbm_axi3[17].rid            ),  // output wire [5 : 0] AXI_17_RID
      .AXI_17_RLAST                   (st_hbm_axi3[17].rlast          ),  // output wire AXI_17_RLAST
      .AXI_17_RRESP                   (st_hbm_axi3[17].rresp          ),  // output wire [1 : 0] AXI_17_RRESP
      .AXI_17_RVALID                  (st_hbm_axi3[17].rvalid         ),  // output wire AXI_17_RVALID
      .AXI_17_WREADY                  (st_hbm_axi3[17].wready         ),  // output wire AXI_17_WREADY
      .AXI_17_BID                     (st_hbm_axi3[17].bid            ),  // output wire [5 : 0] AXI_17_BID
      .AXI_17_BRESP                   (st_hbm_axi3[17].bresp          ),  // output wire [1 : 0] AXI_17_BRESP
      .AXI_17_BVALID                  (st_hbm_axi3[17].bvalid         ),  // output wire AXI_17_BVALID

      .AXI_18_ACLK                    (axi_clk                        ),  // input wire AXI_18_ACLK
      .AXI_18_ARESET_N                (axi_rst_n                      ),  // input wire AXI_18_ARESET_N
      .AXI_18_ARADDR                  (st_hbm_axi3[18].araddr         ),  // input wire [33 : 0] AXI_18_ARADDR
      .AXI_18_ARBURST                 (st_hbm_axi3[18].arburst        ),  // input wire [1 : 0] AXI_18_ARBURST
      .AXI_18_ARID                    (st_hbm_axi3[18].arid           ),  // input wire [5 : 0] AXI_18_ARID
      .AXI_18_ARLEN                   (st_hbm_axi3[18].arlen          ),  // input wire [3 : 0] AXI_18_ARLEN
      .AXI_18_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_18_ARSIZE
      .AXI_18_ARVALID                 (st_hbm_axi3[18].arvalid        ),  // input wire AXI_18_ARVALID
      .AXI_18_AWADDR                  (st_hbm_axi3[18].awaddr         ),  // input wire [33 : 0] AXI_18_AWADDR
      .AXI_18_AWBURST                 (st_hbm_axi3[18].awburst        ),  // input wire [1 : 0] AXI_18_AWBURST
      .AXI_18_AWID                    (st_hbm_axi3[18].awid           ),  // input wire [5 : 0] AXI_18_AWID
      .AXI_18_AWLEN                   (st_hbm_axi3[18].awlen          ),  // input wire [3 : 0] AXI_18_AWLEN
      .AXI_18_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_18_AWSIZE
      .AXI_18_AWVALID                 (st_hbm_axi3[18].awvalid        ),  // input wire AXI_18_AWVALID
      .AXI_18_RREADY                  (st_hbm_axi3[18].rready         ),  // input wire AXI_18_RREADY
      .AXI_18_BREADY                  (st_hbm_axi3[18].bready         ),  // input wire AXI_18_BREADY
      .AXI_18_WDATA                   (st_hbm_axi3[18].wdata          ),  // input wire [255 : 0] AXI_18_WDATA
      .AXI_18_WLAST                   (st_hbm_axi3[18].wlast          ),  // input wire AXI_18_WLAST
      .AXI_18_WSTRB                   (st_hbm_axi3[18].wstrb          ),  // input wire [31 : 0] AXI_18_WSTRB
      .AXI_18_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_18_WDATA_PARITY
      .AXI_18_WVALID                  (st_hbm_axi3[18].wvalid         ),  // input wire AXI_18_WVALID
      .AXI_18_ARREADY                 (st_hbm_axi3[18].arready        ),  // output wire AXI_18_ARREADY
      .AXI_18_AWREADY                 (st_hbm_axi3[18].awready        ),  // output wire AXI_18_AWREADY
      .AXI_18_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_18_RDATA_PARITY
      .AXI_18_RDATA                   (st_hbm_axi3[18].rdata          ),  // output wire [255 : 0] AXI_18_RDATA
      .AXI_18_RID                     (st_hbm_axi3[18].rid            ),  // output wire [5 : 0] AXI_18_RID
      .AXI_18_RLAST                   (st_hbm_axi3[18].rlast          ),  // output wire AXI_18_RLAST
      .AXI_18_RRESP                   (st_hbm_axi3[18].rresp          ),  // output wire [1 : 0] AXI_18_RRESP
      .AXI_18_RVALID                  (st_hbm_axi3[18].rvalid         ),  // output wire AXI_18_RVALID
      .AXI_18_WREADY                  (st_hbm_axi3[18].wready         ),  // output wire AXI_18_WREADY
      .AXI_18_BID                     (st_hbm_axi3[18].bid            ),  // output wire [5 : 0] AXI_18_BID
      .AXI_18_BRESP                   (st_hbm_axi3[18].bresp          ),  // output wire [1 : 0] AXI_18_BRESP
      .AXI_18_BVALID                  (st_hbm_axi3[18].bvalid         ),  // output wire AXI_18_BVALID

      .AXI_19_ACLK                    (axi_clk                        ),  // input wire AXI_19_ACLK
      .AXI_19_ARESET_N                (axi_rst_n                      ),  // input wire AXI_19_ARESET_N
      .AXI_19_ARADDR                  (st_hbm_axi3[19].araddr         ),  // input wire [33 : 0] AXI_19_ARADDR
      .AXI_19_ARBURST                 (st_hbm_axi3[19].arburst        ),  // input wire [1 : 0] AXI_19_ARBURST
      .AXI_19_ARID                    (st_hbm_axi3[19].arid           ),  // input wire [5 : 0] AXI_19_ARID
      .AXI_19_ARLEN                   (st_hbm_axi3[19].arlen          ),  // input wire [3 : 0] AXI_19_ARLEN
      .AXI_19_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_19_ARSIZE
      .AXI_19_ARVALID                 (st_hbm_axi3[19].arvalid        ),  // input wire AXI_19_ARVALID
      .AXI_19_AWADDR                  (st_hbm_axi3[19].awaddr         ),  // input wire [33 : 0] AXI_19_AWADDR
      .AXI_19_AWBURST                 (st_hbm_axi3[19].awburst        ),  // input wire [1 : 0] AXI_19_AWBURST
      .AXI_19_AWID                    (st_hbm_axi3[19].awid           ),  // input wire [5 : 0] AXI_19_AWID
      .AXI_19_AWLEN                   (st_hbm_axi3[19].awlen          ),  // input wire [3 : 0] AXI_19_AWLEN
      .AXI_19_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_19_AWSIZE
      .AXI_19_AWVALID                 (st_hbm_axi3[19].awvalid        ),  // input wire AXI_19_AWVALID
      .AXI_19_RREADY                  (st_hbm_axi3[19].rready         ),  // input wire AXI_19_RREADY
      .AXI_19_BREADY                  (st_hbm_axi3[19].bready         ),  // input wire AXI_19_BREADY
      .AXI_19_WDATA                   (st_hbm_axi3[19].wdata          ),  // input wire [255 : 0] AXI_19_WDATA
      .AXI_19_WLAST                   (st_hbm_axi3[19].wlast          ),  // input wire AXI_19_WLAST
      .AXI_19_WSTRB                   (st_hbm_axi3[19].wstrb          ),  // input wire [31 : 0] AXI_19_WSTRB
      .AXI_19_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_19_WDATA_PARITY
      .AXI_19_WVALID                  (st_hbm_axi3[19].wvalid         ),  // input wire AXI_19_WVALID
      .AXI_19_ARREADY                 (st_hbm_axi3[19].arready        ),  // output wire AXI_19_ARREADY
      .AXI_19_AWREADY                 (st_hbm_axi3[19].awready        ),  // output wire AXI_19_AWREADY
      .AXI_19_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_19_RDATA_PARITY
      .AXI_19_RDATA                   (st_hbm_axi3[19].rdata          ),  // output wire [255 : 0] AXI_19_RDATA
      .AXI_19_RID                     (st_hbm_axi3[19].rid            ),  // output wire [5 : 0] AXI_19_RID
      .AXI_19_RLAST                   (st_hbm_axi3[19].rlast          ),  // output wire AXI_19_RLAST
      .AXI_19_RRESP                   (st_hbm_axi3[19].rresp          ),  // output wire [1 : 0] AXI_19_RRESP
      .AXI_19_RVALID                  (st_hbm_axi3[19].rvalid         ),  // output wire AXI_19_RVALID
      .AXI_19_WREADY                  (st_hbm_axi3[19].wready         ),  // output wire AXI_19_WREADY
      .AXI_19_BID                     (st_hbm_axi3[19].bid            ),  // output wire [5 : 0] AXI_19_BID
      .AXI_19_BRESP                   (st_hbm_axi3[19].bresp          ),  // output wire [1 : 0] AXI_19_BRESP
      .AXI_19_BVALID                  (st_hbm_axi3[19].bvalid         ),  // output wire AXI_19_BVALID

      .AXI_20_ACLK                    (axi_clk                        ),  // input wire AXI_20_ACLK
      .AXI_20_ARESET_N                (axi_rst_n                      ),  // input wire AXI_20_ARESET_N
      .AXI_20_ARADDR                  (st_hbm_axi3[20].araddr         ),  // input wire [33 : 0] AXI_20_ARADDR
      .AXI_20_ARBURST                 (st_hbm_axi3[20].arburst        ),  // input wire [1 : 0] AXI_20_ARBURST
      .AXI_20_ARID                    (st_hbm_axi3[20].arid           ),  // input wire [5 : 0] AXI_20_ARID
      .AXI_20_ARLEN                   (st_hbm_axi3[20].arlen          ),  // input wire [3 : 0] AXI_20_ARLEN
      .AXI_20_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_20_ARSIZE
      .AXI_20_ARVALID                 (st_hbm_axi3[20].arvalid        ),  // input wire AXI_20_ARVALID
      .AXI_20_AWADDR                  (st_hbm_axi3[20].awaddr         ),  // input wire [33 : 0] AXI_20_AWADDR
      .AXI_20_AWBURST                 (st_hbm_axi3[20].awburst        ),  // input wire [1 : 0] AXI_20_AWBURST
      .AXI_20_AWID                    (st_hbm_axi3[20].awid           ),  // input wire [5 : 0] AXI_20_AWID
      .AXI_20_AWLEN                   (st_hbm_axi3[20].awlen          ),  // input wire [3 : 0] AXI_20_AWLEN
      .AXI_20_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_20_AWSIZE
      .AXI_20_AWVALID                 (st_hbm_axi3[20].awvalid        ),  // input wire AXI_20_AWVALID
      .AXI_20_RREADY                  (st_hbm_axi3[20].rready         ),  // input wire AXI_20_RREADY
      .AXI_20_BREADY                  (st_hbm_axi3[20].bready         ),  // input wire AXI_20_BREADY
      .AXI_20_WDATA                   (st_hbm_axi3[20].wdata          ),  // input wire [255 : 0] AXI_20_WDATA
      .AXI_20_WLAST                   (st_hbm_axi3[20].wlast          ),  // input wire AXI_20_WLAST
      .AXI_20_WSTRB                   (st_hbm_axi3[20].wstrb          ),  // input wire [31 : 0] AXI_20_WSTRB
      .AXI_20_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_20_WDATA_PARITY
      .AXI_20_WVALID                  (st_hbm_axi3[20].wvalid         ),  // input wire AXI_20_WVALID
      .AXI_20_ARREADY                 (st_hbm_axi3[20].arready        ),  // output wire AXI_20_ARREADY
      .AXI_20_AWREADY                 (st_hbm_axi3[20].awready        ),  // output wire AXI_20_AWREADY
      .AXI_20_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_20_RDATA_PARITY
      .AXI_20_RDATA                   (st_hbm_axi3[20].rdata          ),  // output wire [255 : 0] AXI_20_RDATA
      .AXI_20_RID                     (st_hbm_axi3[20].rid            ),  // output wire [5 : 0] AXI_20_RID
      .AXI_20_RLAST                   (st_hbm_axi3[20].rlast          ),  // output wire AXI_20_RLAST
      .AXI_20_RRESP                   (st_hbm_axi3[20].rresp          ),  // output wire [1 : 0] AXI_20_RRESP
      .AXI_20_RVALID                  (st_hbm_axi3[20].rvalid         ),  // output wire AXI_20_RVALID
      .AXI_20_WREADY                  (st_hbm_axi3[20].wready         ),  // output wire AXI_20_WREADY
      .AXI_20_BID                     (st_hbm_axi3[20].bid            ),  // output wire [5 : 0] AXI_20_BID
      .AXI_20_BRESP                   (st_hbm_axi3[20].bresp          ),  // output wire [1 : 0] AXI_20_BRESP
      .AXI_20_BVALID                  (st_hbm_axi3[20].bvalid         ),  // output wire AXI_20_BVALID

      .AXI_21_ACLK                    (axi_clk                        ),  // input wire AXI_21_ACLK
      .AXI_21_ARESET_N                (axi_rst_n                      ),  // input wire AXI_21_ARESET_N
      .AXI_21_ARADDR                  (st_hbm_axi3[21].araddr         ),  // input wire [33 : 0] AXI_21_ARADDR
      .AXI_21_ARBURST                 (st_hbm_axi3[21].arburst        ),  // input wire [1 : 0] AXI_21_ARBURST
      .AXI_21_ARID                    (st_hbm_axi3[21].arid           ),  // input wire [5 : 0] AXI_21_ARID
      .AXI_21_ARLEN                   (st_hbm_axi3[21].arlen          ),  // input wire [3 : 0] AXI_21_ARLEN
      .AXI_21_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_21_ARSIZE
      .AXI_21_ARVALID                 (st_hbm_axi3[21].arvalid        ),  // input wire AXI_21_ARVALID
      .AXI_21_AWADDR                  (st_hbm_axi3[21].awaddr         ),  // input wire [33 : 0] AXI_21_AWADDR
      .AXI_21_AWBURST                 (st_hbm_axi3[21].awburst        ),  // input wire [1 : 0] AXI_21_AWBURST
      .AXI_21_AWID                    (st_hbm_axi3[21].awid           ),  // input wire [5 : 0] AXI_21_AWID
      .AXI_21_AWLEN                   (st_hbm_axi3[21].awlen          ),  // input wire [3 : 0] AXI_21_AWLEN
      .AXI_21_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_21_AWSIZE
      .AXI_21_AWVALID                 (st_hbm_axi3[21].awvalid        ),  // input wire AXI_21_AWVALID
      .AXI_21_RREADY                  (st_hbm_axi3[21].rready         ),  // input wire AXI_21_RREADY
      .AXI_21_BREADY                  (st_hbm_axi3[21].bready         ),  // input wire AXI_21_BREADY
      .AXI_21_WDATA                   (st_hbm_axi3[21].wdata          ),  // input wire [255 : 0] AXI_21_WDATA
      .AXI_21_WLAST                   (st_hbm_axi3[21].wlast          ),  // input wire AXI_21_WLAST
      .AXI_21_WSTRB                   (st_hbm_axi3[21].wstrb          ),  // input wire [31 : 0] AXI_21_WSTRB
      .AXI_21_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_21_WDATA_PARITY
      .AXI_21_WVALID                  (st_hbm_axi3[21].wvalid         ),  // input wire AXI_21_WVALID
      .AXI_21_ARREADY                 (st_hbm_axi3[21].arready        ),  // output wire AXI_21_ARREADY
      .AXI_21_AWREADY                 (st_hbm_axi3[21].awready        ),  // output wire AXI_21_AWREADY
      .AXI_21_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_21_RDATA_PARITY
      .AXI_21_RDATA                   (st_hbm_axi3[21].rdata          ),  // output wire [255 : 0] AXI_21_RDATA
      .AXI_21_RID                     (st_hbm_axi3[21].rid            ),  // output wire [5 : 0] AXI_21_RID
      .AXI_21_RLAST                   (st_hbm_axi3[21].rlast          ),  // output wire AXI_21_RLAST
      .AXI_21_RRESP                   (st_hbm_axi3[21].rresp          ),  // output wire [1 : 0] AXI_21_RRESP
      .AXI_21_RVALID                  (st_hbm_axi3[21].rvalid         ),  // output wire AXI_21_RVALID
      .AXI_21_WREADY                  (st_hbm_axi3[21].wready         ),  // output wire AXI_21_WREADY
      .AXI_21_BID                     (st_hbm_axi3[21].bid            ),  // output wire [5 : 0] AXI_21_BID
      .AXI_21_BRESP                   (st_hbm_axi3[21].bresp          ),  // output wire [1 : 0] AXI_21_BRESP
      .AXI_21_BVALID                  (st_hbm_axi3[21].bvalid         ),  // output wire AXI_21_BVALID

      .AXI_22_ACLK                    (axi_clk                        ),  // input wire AXI_22_ACLK
      .AXI_22_ARESET_N                (axi_rst_n                      ),  // input wire AXI_22_ARESET_N
      .AXI_22_ARADDR                  (st_hbm_axi3[22].araddr         ),  // input wire [33 : 0] AXI_22_ARADDR
      .AXI_22_ARBURST                 (st_hbm_axi3[22].arburst        ),  // input wire [1 : 0] AXI_22_ARBURST
      .AXI_22_ARID                    (st_hbm_axi3[22].arid           ),  // input wire [5 : 0] AXI_22_ARID
      .AXI_22_ARLEN                   (st_hbm_axi3[22].arlen          ),  // input wire [3 : 0] AXI_22_ARLEN
      .AXI_22_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_22_ARSIZE
      .AXI_22_ARVALID                 (st_hbm_axi3[22].arvalid        ),  // input wire AXI_22_ARVALID
      .AXI_22_AWADDR                  (st_hbm_axi3[22].awaddr         ),  // input wire [33 : 0] AXI_22_AWADDR
      .AXI_22_AWBURST                 (st_hbm_axi3[22].awburst        ),  // input wire [1 : 0] AXI_22_AWBURST
      .AXI_22_AWID                    (st_hbm_axi3[22].awid           ),  // input wire [5 : 0] AXI_22_AWID
      .AXI_22_AWLEN                   (st_hbm_axi3[22].awlen          ),  // input wire [3 : 0] AXI_22_AWLEN
      .AXI_22_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_22_AWSIZE
      .AXI_22_AWVALID                 (st_hbm_axi3[22].awvalid        ),  // input wire AXI_22_AWVALID
      .AXI_22_RREADY                  (st_hbm_axi3[22].rready         ),  // input wire AXI_22_RREADY
      .AXI_22_BREADY                  (st_hbm_axi3[22].bready         ),  // input wire AXI_22_BREADY
      .AXI_22_WDATA                   (st_hbm_axi3[22].wdata          ),  // input wire [255 : 0] AXI_22_WDATA
      .AXI_22_WLAST                   (st_hbm_axi3[22].wlast          ),  // input wire AXI_22_WLAST
      .AXI_22_WSTRB                   (st_hbm_axi3[22].wstrb          ),  // input wire [31 : 0] AXI_22_WSTRB
      .AXI_22_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_22_WDATA_PARITY
      .AXI_22_WVALID                  (st_hbm_axi3[22].wvalid         ),  // input wire AXI_22_WVALID
      .AXI_22_ARREADY                 (st_hbm_axi3[22].arready        ),  // output wire AXI_22_ARREADY
      .AXI_22_AWREADY                 (st_hbm_axi3[22].awready        ),  // output wire AXI_22_AWREADY
      .AXI_22_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_22_RDATA_PARITY
      .AXI_22_RDATA                   (st_hbm_axi3[22].rdata          ),  // output wire [255 : 0] AXI_22_RDATA
      .AXI_22_RID                     (st_hbm_axi3[22].rid            ),  // output wire [5 : 0] AXI_22_RID
      .AXI_22_RLAST                   (st_hbm_axi3[22].rlast          ),  // output wire AXI_22_RLAST
      .AXI_22_RRESP                   (st_hbm_axi3[22].rresp          ),  // output wire [1 : 0] AXI_22_RRESP
      .AXI_22_RVALID                  (st_hbm_axi3[22].rvalid         ),  // output wire AXI_22_RVALID
      .AXI_22_WREADY                  (st_hbm_axi3[22].wready         ),  // output wire AXI_22_WREADY
      .AXI_22_BID                     (st_hbm_axi3[22].bid            ),  // output wire [5 : 0] AXI_22_BID
      .AXI_22_BRESP                   (st_hbm_axi3[22].bresp          ),  // output wire [1 : 0] AXI_22_BRESP
      .AXI_22_BVALID                  (st_hbm_axi3[22].bvalid         ),  // output wire AXI_22_BVALID

      .AXI_23_ACLK                    (axi_clk                        ),  // input wire AXI_23_ACLK
      .AXI_23_ARESET_N                (axi_rst_n                      ),  // input wire AXI_23_ARESET_N
      .AXI_23_ARADDR                  (st_hbm_axi3[23].araddr         ),  // input wire [33 : 0] AXI_23_ARADDR
      .AXI_23_ARBURST                 (st_hbm_axi3[23].arburst        ),  // input wire [1 : 0] AXI_23_ARBURST
      .AXI_23_ARID                    (st_hbm_axi3[23].arid           ),  // input wire [5 : 0] AXI_23_ARID
      .AXI_23_ARLEN                   (st_hbm_axi3[23].arlen          ),  // input wire [3 : 0] AXI_23_ARLEN
      .AXI_23_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_23_ARSIZE
      .AXI_23_ARVALID                 (st_hbm_axi3[23].arvalid        ),  // input wire AXI_23_ARVALID
      .AXI_23_AWADDR                  (st_hbm_axi3[23].awaddr         ),  // input wire [33 : 0] AXI_23_AWADDR
      .AXI_23_AWBURST                 (st_hbm_axi3[23].awburst        ),  // input wire [1 : 0] AXI_23_AWBURST
      .AXI_23_AWID                    (st_hbm_axi3[23].awid           ),  // input wire [5 : 0] AXI_23_AWID
      .AXI_23_AWLEN                   (st_hbm_axi3[23].awlen          ),  // input wire [3 : 0] AXI_23_AWLEN
      .AXI_23_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_23_AWSIZE
      .AXI_23_AWVALID                 (st_hbm_axi3[23].awvalid        ),  // input wire AXI_23_AWVALID
      .AXI_23_RREADY                  (st_hbm_axi3[23].rready         ),  // input wire AXI_23_RREADY
      .AXI_23_BREADY                  (st_hbm_axi3[23].bready         ),  // input wire AXI_23_BREADY
      .AXI_23_WDATA                   (st_hbm_axi3[23].wdata          ),  // input wire [255 : 0] AXI_23_WDATA
      .AXI_23_WLAST                   (st_hbm_axi3[23].wlast          ),  // input wire AXI_23_WLAST
      .AXI_23_WSTRB                   (st_hbm_axi3[23].wstrb          ),  // input wire [31 : 0] AXI_23_WSTRB
      .AXI_23_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_23_WDATA_PARITY
      .AXI_23_WVALID                  (st_hbm_axi3[23].wvalid         ),  // input wire AXI_23_WVALID
      .AXI_23_ARREADY                 (st_hbm_axi3[23].arready        ),  // output wire AXI_23_ARREADY
      .AXI_23_AWREADY                 (st_hbm_axi3[23].awready        ),  // output wire AXI_23_AWREADY
      .AXI_23_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_23_RDATA_PARITY
      .AXI_23_RDATA                   (st_hbm_axi3[23].rdata          ),  // output wire [255 : 0] AXI_23_RDATA
      .AXI_23_RID                     (st_hbm_axi3[23].rid            ),  // output wire [5 : 0] AXI_23_RID
      .AXI_23_RLAST                   (st_hbm_axi3[23].rlast          ),  // output wire AXI_23_RLAST
      .AXI_23_RRESP                   (st_hbm_axi3[23].rresp          ),  // output wire [1 : 0] AXI_23_RRESP
      .AXI_23_RVALID                  (st_hbm_axi3[23].rvalid         ),  // output wire AXI_23_RVALID
      .AXI_23_WREADY                  (st_hbm_axi3[23].wready         ),  // output wire AXI_23_WREADY
      .AXI_23_BID                     (st_hbm_axi3[23].bid            ),  // output wire [5 : 0] AXI_23_BID
      .AXI_23_BRESP                   (st_hbm_axi3[23].bresp          ),  // output wire [1 : 0] AXI_23_BRESP
      .AXI_23_BVALID                  (st_hbm_axi3[23].bvalid         ),  // output wire AXI_23_BVALID

      .AXI_24_ACLK                    (axi_clk                        ),  // input wire AXI_24_ACLK
      .AXI_24_ARESET_N                (axi_rst_n                      ),  // input wire AXI_24_ARESET_N
      .AXI_24_ARADDR                  (st_hbm_axi3[24].araddr         ),  // input wire [33 : 0] AXI_24_ARADDR
      .AXI_24_ARBURST                 (st_hbm_axi3[24].arburst        ),  // input wire [1 : 0] AXI_24_ARBURST
      .AXI_24_ARID                    (st_hbm_axi3[24].arid           ),  // input wire [5 : 0] AXI_24_ARID
      .AXI_24_ARLEN                   (st_hbm_axi3[24].arlen          ),  // input wire [3 : 0] AXI_24_ARLEN
      .AXI_24_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_24_ARSIZE
      .AXI_24_ARVALID                 (st_hbm_axi3[24].arvalid        ),  // input wire AXI_24_ARVALID
      .AXI_24_AWADDR                  (st_hbm_axi3[24].awaddr         ),  // input wire [33 : 0] AXI_24_AWADDR
      .AXI_24_AWBURST                 (st_hbm_axi3[24].awburst        ),  // input wire [1 : 0] AXI_24_AWBURST
      .AXI_24_AWID                    (st_hbm_axi3[24].awid           ),  // input wire [5 : 0] AXI_24_AWID
      .AXI_24_AWLEN                   (st_hbm_axi3[24].awlen          ),  // input wire [3 : 0] AXI_24_AWLEN
      .AXI_24_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_24_AWSIZE
      .AXI_24_AWVALID                 (st_hbm_axi3[24].awvalid        ),  // input wire AXI_24_AWVALID
      .AXI_24_RREADY                  (st_hbm_axi3[24].rready         ),  // input wire AXI_24_RREADY
      .AXI_24_BREADY                  (st_hbm_axi3[24].bready         ),  // input wire AXI_24_BREADY
      .AXI_24_WDATA                   (st_hbm_axi3[24].wdata          ),  // input wire [255 : 0] AXI_24_WDATA
      .AXI_24_WLAST                   (st_hbm_axi3[24].wlast          ),  // input wire AXI_24_WLAST
      .AXI_24_WSTRB                   (st_hbm_axi3[24].wstrb          ),  // input wire [31 : 0] AXI_24_WSTRB
      .AXI_24_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_24_WDATA_PARITY
      .AXI_24_WVALID                  (st_hbm_axi3[24].wvalid         ),  // input wire AXI_24_WVALID
      .AXI_24_ARREADY                 (st_hbm_axi3[24].arready        ),  // output wire AXI_24_ARREADY
      .AXI_24_AWREADY                 (st_hbm_axi3[24].awready        ),  // output wire AXI_24_AWREADY
      .AXI_24_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_24_RDATA_PARITY
      .AXI_24_RDATA                   (st_hbm_axi3[24].rdata          ),  // output wire [255 : 0] AXI_24_RDATA
      .AXI_24_RID                     (st_hbm_axi3[24].rid            ),  // output wire [5 : 0] AXI_24_RID
      .AXI_24_RLAST                   (st_hbm_axi3[24].rlast          ),  // output wire AXI_24_RLAST
      .AXI_24_RRESP                   (st_hbm_axi3[24].rresp          ),  // output wire [1 : 0] AXI_24_RRESP
      .AXI_24_RVALID                  (st_hbm_axi3[24].rvalid         ),  // output wire AXI_24_RVALID
      .AXI_24_WREADY                  (st_hbm_axi3[24].wready         ),  // output wire AXI_24_WREADY
      .AXI_24_BID                     (st_hbm_axi3[24].bid            ),  // output wire [5 : 0] AXI_24_BID
      .AXI_24_BRESP                   (st_hbm_axi3[24].bresp          ),  // output wire [1 : 0] AXI_24_BRESP
      .AXI_24_BVALID                  (st_hbm_axi3[24].bvalid         ),  // output wire AXI_24_BVALID

      .AXI_25_ACLK                    (axi_clk                        ),  // input wire AXI_25_ACLK
      .AXI_25_ARESET_N                (axi_rst_n                      ),  // input wire AXI_25_ARESET_N
      .AXI_25_ARADDR                  (st_hbm_axi3[25].araddr         ),  // input wire [33 : 0] AXI_25_ARADDR
      .AXI_25_ARBURST                 (st_hbm_axi3[25].arburst        ),  // input wire [1 : 0] AXI_25_ARBURST
      .AXI_25_ARID                    (st_hbm_axi3[25].arid           ),  // input wire [5 : 0] AXI_25_ARID
      .AXI_25_ARLEN                   (st_hbm_axi3[25].arlen          ),  // input wire [3 : 0] AXI_25_ARLEN
      .AXI_25_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_25_ARSIZE
      .AXI_25_ARVALID                 (st_hbm_axi3[25].arvalid        ),  // input wire AXI_25_ARVALID
      .AXI_25_AWADDR                  (st_hbm_axi3[25].awaddr         ),  // input wire [33 : 0] AXI_25_AWADDR
      .AXI_25_AWBURST                 (st_hbm_axi3[25].awburst        ),  // input wire [1 : 0] AXI_25_AWBURST
      .AXI_25_AWID                    (st_hbm_axi3[25].awid           ),  // input wire [5 : 0] AXI_25_AWID
      .AXI_25_AWLEN                   (st_hbm_axi3[25].awlen          ),  // input wire [3 : 0] AXI_25_AWLEN
      .AXI_25_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_25_AWSIZE
      .AXI_25_AWVALID                 (st_hbm_axi3[25].awvalid        ),  // input wire AXI_25_AWVALID
      .AXI_25_RREADY                  (st_hbm_axi3[25].rready         ),  // input wire AXI_25_RREADY
      .AXI_25_BREADY                  (st_hbm_axi3[25].bready         ),  // input wire AXI_25_BREADY
      .AXI_25_WDATA                   (st_hbm_axi3[25].wdata          ),  // input wire [255 : 0] AXI_25_WDATA
      .AXI_25_WLAST                   (st_hbm_axi3[25].wlast          ),  // input wire AXI_25_WLAST
      .AXI_25_WSTRB                   (st_hbm_axi3[25].wstrb          ),  // input wire [31 : 0] AXI_25_WSTRB
      .AXI_25_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_25_WDATA_PARITY
      .AXI_25_WVALID                  (st_hbm_axi3[25].wvalid         ),  // input wire AXI_25_WVALID
      .AXI_25_ARREADY                 (st_hbm_axi3[25].arready        ),  // output wire AXI_25_ARREADY
      .AXI_25_AWREADY                 (st_hbm_axi3[25].awready        ),  // output wire AXI_25_AWREADY
      .AXI_25_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_25_RDATA_PARITY
      .AXI_25_RDATA                   (st_hbm_axi3[25].rdata          ),  // output wire [255 : 0] AXI_25_RDATA
      .AXI_25_RID                     (st_hbm_axi3[25].rid            ),  // output wire [5 : 0] AXI_25_RID
      .AXI_25_RLAST                   (st_hbm_axi3[25].rlast          ),  // output wire AXI_25_RLAST
      .AXI_25_RRESP                   (st_hbm_axi3[25].rresp          ),  // output wire [1 : 0] AXI_25_RRESP
      .AXI_25_RVALID                  (st_hbm_axi3[25].rvalid         ),  // output wire AXI_25_RVALID
      .AXI_25_WREADY                  (st_hbm_axi3[25].wready         ),  // output wire AXI_25_WREADY
      .AXI_25_BID                     (st_hbm_axi3[25].bid            ),  // output wire [5 : 0] AXI_25_BID
      .AXI_25_BRESP                   (st_hbm_axi3[25].bresp          ),  // output wire [1 : 0] AXI_25_BRESP
      .AXI_25_BVALID                  (st_hbm_axi3[25].bvalid         ),  // output wire AXI_25_BVALID

      .AXI_26_ACLK                    (axi_clk                        ),  // input wire AXI_26_ACLK
      .AXI_26_ARESET_N                (axi_rst_n                      ),  // input wire AXI_26_ARESET_N
      .AXI_26_ARADDR                  (st_hbm_axi3[26].araddr         ),  // input wire [33 : 0] AXI_26_ARADDR
      .AXI_26_ARBURST                 (st_hbm_axi3[26].arburst        ),  // input wire [1 : 0] AXI_26_ARBURST
      .AXI_26_ARID                    (st_hbm_axi3[26].arid           ),  // input wire [5 : 0] AXI_26_ARID
      .AXI_26_ARLEN                   (st_hbm_axi3[26].arlen          ),  // input wire [3 : 0] AXI_26_ARLEN
      .AXI_26_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_26_ARSIZE
      .AXI_26_ARVALID                 (st_hbm_axi3[26].arvalid        ),  // input wire AXI_26_ARVALID
      .AXI_26_AWADDR                  (st_hbm_axi3[26].awaddr         ),  // input wire [33 : 0] AXI_26_AWADDR
      .AXI_26_AWBURST                 (st_hbm_axi3[26].awburst        ),  // input wire [1 : 0] AXI_26_AWBURST
      .AXI_26_AWID                    (st_hbm_axi3[26].awid           ),  // input wire [5 : 0] AXI_26_AWID
      .AXI_26_AWLEN                   (st_hbm_axi3[26].awlen          ),  // input wire [3 : 0] AXI_26_AWLEN
      .AXI_26_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_26_AWSIZE
      .AXI_26_AWVALID                 (st_hbm_axi3[26].awvalid        ),  // input wire AXI_26_AWVALID
      .AXI_26_RREADY                  (st_hbm_axi3[26].rready         ),  // input wire AXI_26_RREADY
      .AXI_26_BREADY                  (st_hbm_axi3[26].bready         ),  // input wire AXI_26_BREADY
      .AXI_26_WDATA                   (st_hbm_axi3[26].wdata          ),  // input wire [255 : 0] AXI_26_WDATA
      .AXI_26_WLAST                   (st_hbm_axi3[26].wlast          ),  // input wire AXI_26_WLAST
      .AXI_26_WSTRB                   (st_hbm_axi3[26].wstrb          ),  // input wire [31 : 0] AXI_26_WSTRB
      .AXI_26_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_26_WDATA_PARITY
      .AXI_26_WVALID                  (st_hbm_axi3[26].wvalid         ),  // input wire AXI_26_WVALID
      .AXI_26_ARREADY                 (st_hbm_axi3[26].arready        ),  // output wire AXI_26_ARREADY
      .AXI_26_AWREADY                 (st_hbm_axi3[26].awready        ),  // output wire AXI_26_AWREADY
      .AXI_26_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_26_RDATA_PARITY
      .AXI_26_RDATA                   (st_hbm_axi3[26].rdata          ),  // output wire [255 : 0] AXI_26_RDATA
      .AXI_26_RID                     (st_hbm_axi3[26].rid            ),  // output wire [5 : 0] AXI_26_RID
      .AXI_26_RLAST                   (st_hbm_axi3[26].rlast          ),  // output wire AXI_26_RLAST
      .AXI_26_RRESP                   (st_hbm_axi3[26].rresp          ),  // output wire [1 : 0] AXI_26_RRESP
      .AXI_26_RVALID                  (st_hbm_axi3[26].rvalid         ),  // output wire AXI_26_RVALID
      .AXI_26_WREADY                  (st_hbm_axi3[26].wready         ),  // output wire AXI_26_WREADY
      .AXI_26_BID                     (st_hbm_axi3[26].bid            ),  // output wire [5 : 0] AXI_26_BID
      .AXI_26_BRESP                   (st_hbm_axi3[26].bresp          ),  // output wire [1 : 0] AXI_26_BRESP
      .AXI_26_BVALID                  (st_hbm_axi3[26].bvalid         ),  // output wire AXI_26_BVALID

      .AXI_27_ACLK                    (axi_clk                        ),  // input wire AXI_27_ACLK
      .AXI_27_ARESET_N                (axi_rst_n                      ),  // input wire AXI_27_ARESET_N
      .AXI_27_ARADDR                  (st_hbm_axi3[27].araddr         ),  // input wire [33 : 0] AXI_27_ARADDR
      .AXI_27_ARBURST                 (st_hbm_axi3[27].arburst        ),  // input wire [1 : 0] AXI_27_ARBURST
      .AXI_27_ARID                    (st_hbm_axi3[27].arid           ),  // input wire [5 : 0] AXI_27_ARID
      .AXI_27_ARLEN                   (st_hbm_axi3[27].arlen          ),  // input wire [3 : 0] AXI_27_ARLEN
      .AXI_27_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_27_ARSIZE
      .AXI_27_ARVALID                 (st_hbm_axi3[27].arvalid        ),  // input wire AXI_27_ARVALID
      .AXI_27_AWADDR                  (st_hbm_axi3[27].awaddr         ),  // input wire [33 : 0] AXI_27_AWADDR
      .AXI_27_AWBURST                 (st_hbm_axi3[27].awburst        ),  // input wire [1 : 0] AXI_27_AWBURST
      .AXI_27_AWID                    (st_hbm_axi3[27].awid           ),  // input wire [5 : 0] AXI_27_AWID
      .AXI_27_AWLEN                   (st_hbm_axi3[27].awlen          ),  // input wire [3 : 0] AXI_27_AWLEN
      .AXI_27_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_27_AWSIZE
      .AXI_27_AWVALID                 (st_hbm_axi3[27].awvalid        ),  // input wire AXI_27_AWVALID
      .AXI_27_RREADY                  (st_hbm_axi3[27].rready         ),  // input wire AXI_27_RREADY
      .AXI_27_BREADY                  (st_hbm_axi3[27].bready         ),  // input wire AXI_27_BREADY
      .AXI_27_WDATA                   (st_hbm_axi3[27].wdata          ),  // input wire [255 : 0] AXI_27_WDATA
      .AXI_27_WLAST                   (st_hbm_axi3[27].wlast          ),  // input wire AXI_27_WLAST
      .AXI_27_WSTRB                   (st_hbm_axi3[27].wstrb          ),  // input wire [31 : 0] AXI_27_WSTRB
      .AXI_27_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_27_WDATA_PARITY
      .AXI_27_WVALID                  (st_hbm_axi3[27].wvalid         ),  // input wire AXI_27_WVALID
      .AXI_27_ARREADY                 (st_hbm_axi3[27].arready        ),  // output wire AXI_27_ARREADY
      .AXI_27_AWREADY                 (st_hbm_axi3[27].awready        ),  // output wire AXI_27_AWREADY
      .AXI_27_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_27_RDATA_PARITY
      .AXI_27_RDATA                   (st_hbm_axi3[27].rdata          ),  // output wire [255 : 0] AXI_27_RDATA
      .AXI_27_RID                     (st_hbm_axi3[27].rid            ),  // output wire [5 : 0] AXI_27_RID
      .AXI_27_RLAST                   (st_hbm_axi3[27].rlast          ),  // output wire AXI_27_RLAST
      .AXI_27_RRESP                   (st_hbm_axi3[27].rresp          ),  // output wire [1 : 0] AXI_27_RRESP
      .AXI_27_RVALID                  (st_hbm_axi3[27].rvalid         ),  // output wire AXI_27_RVALID
      .AXI_27_WREADY                  (st_hbm_axi3[27].wready         ),  // output wire AXI_27_WREADY
      .AXI_27_BID                     (st_hbm_axi3[27].bid            ),  // output wire [5 : 0] AXI_27_BID
      .AXI_27_BRESP                   (st_hbm_axi3[27].bresp          ),  // output wire [1 : 0] AXI_27_BRESP
      .AXI_27_BVALID                  (st_hbm_axi3[27].bvalid         ),  // output wire AXI_27_BVALID

      .AXI_28_ACLK                    (axi_clk                        ),  // input wire AXI_28_ACLK
      .AXI_28_ARESET_N                (axi_rst_n                      ),  // input wire AXI_28_ARESET_N
      .AXI_28_ARADDR                  (st_hbm_axi3[28].araddr         ),  // input wire [33 : 0] AXI_28_ARADDR
      .AXI_28_ARBURST                 (st_hbm_axi3[28].arburst        ),  // input wire [1 : 0] AXI_28_ARBURST
      .AXI_28_ARID                    (st_hbm_axi3[28].arid           ),  // input wire [5 : 0] AXI_28_ARID
      .AXI_28_ARLEN                   (st_hbm_axi3[28].arlen          ),  // input wire [3 : 0] AXI_28_ARLEN
      .AXI_28_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_28_ARSIZE
      .AXI_28_ARVALID                 (st_hbm_axi3[28].arvalid        ),  // input wire AXI_28_ARVALID
      .AXI_28_AWADDR                  (st_hbm_axi3[28].awaddr         ),  // input wire [33 : 0] AXI_28_AWADDR
      .AXI_28_AWBURST                 (st_hbm_axi3[28].awburst        ),  // input wire [1 : 0] AXI_28_AWBURST
      .AXI_28_AWID                    (st_hbm_axi3[28].awid           ),  // input wire [5 : 0] AXI_28_AWID
      .AXI_28_AWLEN                   (st_hbm_axi3[28].awlen          ),  // input wire [3 : 0] AXI_28_AWLEN
      .AXI_28_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_28_AWSIZE
      .AXI_28_AWVALID                 (st_hbm_axi3[28].awvalid        ),  // input wire AXI_28_AWVALID
      .AXI_28_RREADY                  (st_hbm_axi3[28].rready         ),  // input wire AXI_28_RREADY
      .AXI_28_BREADY                  (st_hbm_axi3[28].bready         ),  // input wire AXI_28_BREADY
      .AXI_28_WDATA                   (st_hbm_axi3[28].wdata          ),  // input wire [255 : 0] AXI_28_WDATA
      .AXI_28_WLAST                   (st_hbm_axi3[28].wlast          ),  // input wire AXI_28_WLAST
      .AXI_28_WSTRB                   (st_hbm_axi3[28].wstrb          ),  // input wire [31 : 0] AXI_28_WSTRB
      .AXI_28_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_28_WDATA_PARITY
      .AXI_28_WVALID                  (st_hbm_axi3[28].wvalid         ),  // input wire AXI_28_WVALID
      .AXI_28_ARREADY                 (st_hbm_axi3[28].arready        ),  // output wire AXI_28_ARREADY
      .AXI_28_AWREADY                 (st_hbm_axi3[28].awready        ),  // output wire AXI_28_AWREADY
      .AXI_28_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_28_RDATA_PARITY
      .AXI_28_RDATA                   (st_hbm_axi3[28].rdata          ),  // output wire [255 : 0] AXI_28_RDATA
      .AXI_28_RID                     (st_hbm_axi3[28].rid            ),  // output wire [5 : 0] AXI_28_RID
      .AXI_28_RLAST                   (st_hbm_axi3[28].rlast          ),  // output wire AXI_28_RLAST
      .AXI_28_RRESP                   (st_hbm_axi3[28].rresp          ),  // output wire [1 : 0] AXI_28_RRESP
      .AXI_28_RVALID                  (st_hbm_axi3[28].rvalid         ),  // output wire AXI_28_RVALID
      .AXI_28_WREADY                  (st_hbm_axi3[28].wready         ),  // output wire AXI_28_WREADY
      .AXI_28_BID                     (st_hbm_axi3[28].bid            ),  // output wire [5 : 0] AXI_28_BID
      .AXI_28_BRESP                   (st_hbm_axi3[28].bresp          ),  // output wire [1 : 0] AXI_28_BRESP
      .AXI_28_BVALID                  (st_hbm_axi3[28].bvalid         ),  // output wire AXI_28_BVALID

      .AXI_29_ACLK                    (axi_clk                        ),  // input wire AXI_29_ACLK
      .AXI_29_ARESET_N                (axi_rst_n                      ),  // input wire AXI_29_ARESET_N
      .AXI_29_ARADDR                  (st_hbm_axi3[29].araddr         ),  // input wire [33 : 0] AXI_29_ARADDR
      .AXI_29_ARBURST                 (st_hbm_axi3[29].arburst        ),  // input wire [1 : 0] AXI_29_ARBURST
      .AXI_29_ARID                    (st_hbm_axi3[29].arid           ),  // input wire [5 : 0] AXI_29_ARID
      .AXI_29_ARLEN                   (st_hbm_axi3[29].arlen          ),  // input wire [3 : 0] AXI_29_ARLEN
      .AXI_29_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_29_ARSIZE
      .AXI_29_ARVALID                 (st_hbm_axi3[29].arvalid        ),  // input wire AXI_29_ARVALID
      .AXI_29_AWADDR                  (st_hbm_axi3[29].awaddr         ),  // input wire [33 : 0] AXI_29_AWADDR
      .AXI_29_AWBURST                 (st_hbm_axi3[29].awburst        ),  // input wire [1 : 0] AXI_29_AWBURST
      .AXI_29_AWID                    (st_hbm_axi3[29].awid           ),  // input wire [5 : 0] AXI_29_AWID
      .AXI_29_AWLEN                   (st_hbm_axi3[29].awlen          ),  // input wire [3 : 0] AXI_29_AWLEN
      .AXI_29_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_29_AWSIZE
      .AXI_29_AWVALID                 (st_hbm_axi3[29].awvalid        ),  // input wire AXI_29_AWVALID
      .AXI_29_RREADY                  (st_hbm_axi3[29].rready         ),  // input wire AXI_29_RREADY
      .AXI_29_BREADY                  (st_hbm_axi3[29].bready         ),  // input wire AXI_29_BREADY
      .AXI_29_WDATA                   (st_hbm_axi3[29].wdata          ),  // input wire [255 : 0] AXI_29_WDATA
      .AXI_29_WLAST                   (st_hbm_axi3[29].wlast          ),  // input wire AXI_29_WLAST
      .AXI_29_WSTRB                   (st_hbm_axi3[29].wstrb          ),  // input wire [31 : 0] AXI_29_WSTRB
      .AXI_29_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_29_WDATA_PARITY
      .AXI_29_WVALID                  (st_hbm_axi3[29].wvalid         ),  // input wire AXI_29_WVALID
      .AXI_29_ARREADY                 (st_hbm_axi3[29].arready        ),  // output wire AXI_29_ARREADY
      .AXI_29_AWREADY                 (st_hbm_axi3[29].awready        ),  // output wire AXI_29_AWREADY
      .AXI_29_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_29_RDATA_PARITY
      .AXI_29_RDATA                   (st_hbm_axi3[29].rdata          ),  // output wire [255 : 0] AXI_29_RDATA
      .AXI_29_RID                     (st_hbm_axi3[29].rid            ),  // output wire [5 : 0] AXI_29_RID
      .AXI_29_RLAST                   (st_hbm_axi3[29].rlast          ),  // output wire AXI_29_RLAST
      .AXI_29_RRESP                   (st_hbm_axi3[29].rresp          ),  // output wire [1 : 0] AXI_29_RRESP
      .AXI_29_RVALID                  (st_hbm_axi3[29].rvalid         ),  // output wire AXI_29_RVALID
      .AXI_29_WREADY                  (st_hbm_axi3[29].wready         ),  // output wire AXI_29_WREADY
      .AXI_29_BID                     (st_hbm_axi3[29].bid            ),  // output wire [5 : 0] AXI_29_BID
      .AXI_29_BRESP                   (st_hbm_axi3[29].bresp          ),  // output wire [1 : 0] AXI_29_BRESP
      .AXI_29_BVALID                  (st_hbm_axi3[29].bvalid         ),  // output wire AXI_29_BVALID

      .AXI_30_ACLK                    (axi_clk                        ),  // input wire AXI_30_ACLK
      .AXI_30_ARESET_N                (axi_rst_n                      ),  // input wire AXI_30_ARESET_N
      .AXI_30_ARADDR                  (st_hbm_axi3[30].araddr         ),  // input wire [33 : 0] AXI_30_ARADDR
      .AXI_30_ARBURST                 (st_hbm_axi3[30].arburst        ),  // input wire [1 : 0] AXI_30_ARBURST
      .AXI_30_ARID                    (st_hbm_axi3[30].arid           ),  // input wire [5 : 0] AXI_30_ARID
      .AXI_30_ARLEN                   (st_hbm_axi3[30].arlen          ),  // input wire [3 : 0] AXI_30_ARLEN
      .AXI_30_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_30_ARSIZE
      .AXI_30_ARVALID                 (st_hbm_axi3[30].arvalid        ),  // input wire AXI_30_ARVALID
      .AXI_30_AWADDR                  (st_hbm_axi3[30].awaddr         ),  // input wire [33 : 0] AXI_30_AWADDR
      .AXI_30_AWBURST                 (st_hbm_axi3[30].awburst        ),  // input wire [1 : 0] AXI_30_AWBURST
      .AXI_30_AWID                    (st_hbm_axi3[30].awid           ),  // input wire [5 : 0] AXI_30_AWID
      .AXI_30_AWLEN                   (st_hbm_axi3[30].awlen          ),  // input wire [3 : 0] AXI_30_AWLEN
      .AXI_30_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_30_AWSIZE
      .AXI_30_AWVALID                 (st_hbm_axi3[30].awvalid        ),  // input wire AXI_30_AWVALID
      .AXI_30_RREADY                  (st_hbm_axi3[30].rready         ),  // input wire AXI_30_RREADY
      .AXI_30_BREADY                  (st_hbm_axi3[30].bready         ),  // input wire AXI_30_BREADY
      .AXI_30_WDATA                   (st_hbm_axi3[30].wdata          ),  // input wire [255 : 0] AXI_30_WDATA
      .AXI_30_WLAST                   (st_hbm_axi3[30].wlast          ),  // input wire AXI_30_WLAST
      .AXI_30_WSTRB                   (st_hbm_axi3[30].wstrb          ),  // input wire [31 : 0] AXI_30_WSTRB
      .AXI_30_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_30_WDATA_PARITY
      .AXI_30_WVALID                  (st_hbm_axi3[30].wvalid         ),  // input wire AXI_30_WVALID
      .AXI_30_ARREADY                 (st_hbm_axi3[30].arready        ),  // output wire AXI_30_ARREADY
      .AXI_30_AWREADY                 (st_hbm_axi3[30].awready        ),  // output wire AXI_30_AWREADY
      .AXI_30_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_30_RDATA_PARITY
      .AXI_30_RDATA                   (st_hbm_axi3[30].rdata          ),  // output wire [255 : 0] AXI_30_RDATA
      .AXI_30_RID                     (st_hbm_axi3[30].rid            ),  // output wire [5 : 0] AXI_30_RID
      .AXI_30_RLAST                   (st_hbm_axi3[30].rlast          ),  // output wire AXI_30_RLAST
      .AXI_30_RRESP                   (st_hbm_axi3[30].rresp          ),  // output wire [1 : 0] AXI_30_RRESP
      .AXI_30_RVALID                  (st_hbm_axi3[30].rvalid         ),  // output wire AXI_30_RVALID
      .AXI_30_WREADY                  (st_hbm_axi3[30].wready         ),  // output wire AXI_30_WREADY
      .AXI_30_BID                     (st_hbm_axi3[30].bid            ),  // output wire [5 : 0] AXI_30_BID
      .AXI_30_BRESP                   (st_hbm_axi3[30].bresp          ),  // output wire [1 : 0] AXI_30_BRESP
      .AXI_30_BVALID                  (st_hbm_axi3[30].bvalid         ),  // output wire AXI_30_BVALID

      .AXI_31_ACLK                    (axi_clk                        ),  // input wire AXI_31_ACLK
      .AXI_31_ARESET_N                (axi_rst_n                      ),  // input wire AXI_31_ARESET_N
      .AXI_31_ARADDR                  (st_hbm_axi3[31].araddr         ),  // input wire [33 : 0] AXI_31_ARADDR
      .AXI_31_ARBURST                 (st_hbm_axi3[31].arburst        ),  // input wire [1 : 0] AXI_31_ARBURST
      .AXI_31_ARID                    (st_hbm_axi3[31].arid           ),  // input wire [5 : 0] AXI_31_ARID
      .AXI_31_ARLEN                   (st_hbm_axi3[31].arlen          ),  // input wire [3 : 0] AXI_31_ARLEN
      .AXI_31_ARSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_31_ARSIZE
      .AXI_31_ARVALID                 (st_hbm_axi3[31].arvalid        ),  // input wire AXI_31_ARVALID
      .AXI_31_AWADDR                  (st_hbm_axi3[31].awaddr         ),  // input wire [33 : 0] AXI_31_AWADDR
      .AXI_31_AWBURST                 (st_hbm_axi3[31].awburst        ),  // input wire [1 : 0] AXI_31_AWBURST
      .AXI_31_AWID                    (st_hbm_axi3[31].awid           ),  // input wire [5 : 0] AXI_31_AWID
      .AXI_31_AWLEN                   (st_hbm_axi3[31].awlen          ),  // input wire [3 : 0] AXI_31_AWLEN
      .AXI_31_AWSIZE                  (DEF_AXSIZE                     ),  // input wire [2 : 0] AXI_31_AWSIZE
      .AXI_31_AWVALID                 (st_hbm_axi3[31].awvalid        ),  // input wire AXI_31_AWVALID
      .AXI_31_RREADY                  (st_hbm_axi3[31].rready         ),  // input wire AXI_31_RREADY
      .AXI_31_BREADY                  (st_hbm_axi3[31].bready         ),  // input wire AXI_31_BREADY
      .AXI_31_WDATA                   (st_hbm_axi3[31].wdata          ),  // input wire [255 : 0] AXI_31_WDATA
      .AXI_31_WLAST                   (st_hbm_axi3[31].wlast          ),  // input wire AXI_31_WLAST
      .AXI_31_WSTRB                   (st_hbm_axi3[31].wstrb          ),  // input wire [31 : 0] AXI_31_WSTRB
      .AXI_31_WDATA_PARITY            (DEF_PARITY                     ),  // input wire [31 : 0] AXI_31_WDATA_PARITY
      .AXI_31_WVALID                  (st_hbm_axi3[31].wvalid         ),  // input wire AXI_31_WVALID
      .AXI_31_ARREADY                 (st_hbm_axi3[31].arready        ),  // output wire AXI_31_ARREADY
      .AXI_31_AWREADY                 (st_hbm_axi3[31].awready        ),  // output wire AXI_31_AWREADY
      .AXI_31_RDATA_PARITY            (                               ),  // output wire [31 : 0] AXI_31_RDATA_PARITY
      .AXI_31_RDATA                   (st_hbm_axi3[31].rdata          ),  // output wire [255 : 0] AXI_31_RDATA
      .AXI_31_RID                     (st_hbm_axi3[31].rid            ),  // output wire [5 : 0] AXI_31_RID
      .AXI_31_RLAST                   (st_hbm_axi3[31].rlast          ),  // output wire AXI_31_RLAST
      .AXI_31_RRESP                   (st_hbm_axi3[31].rresp          ),  // output wire [1 : 0] AXI_31_RRESP
      .AXI_31_RVALID                  (st_hbm_axi3[31].rvalid         ),  // output wire AXI_31_RVALID
      .AXI_31_WREADY                  (st_hbm_axi3[31].wready         ),  // output wire AXI_31_WREADY
      .AXI_31_BID                     (st_hbm_axi3[31].bid            ),  // output wire [5 : 0] AXI_31_BID
      .AXI_31_BRESP                   (st_hbm_axi3[31].bresp          ),  // output wire [1 : 0] AXI_31_BRESP
      .AXI_31_BVALID                  (st_hbm_axi3[31].bvalid         ),  // output wire AXI_31_BVALID

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

endmodule // hbm_wrapper
