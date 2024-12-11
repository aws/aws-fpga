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
///////////////////////////////////////////////////////////////////////////////////////
// CL_AXI_CTL
// ----------
// - This module receives a pulse from an external block, and issues an AXI Write/Read request.
// - Interface with AXI3 bus to initiate write/read requests
// - Supports multiple outstanding transactions
// - Only support Incremental Address access patterns
// - Suport bus width aligned transfer widths. 64-Byte for DATA_WIDTH=512 / 32 Byte for DATA_WIDTH = 256
//
///////////////////////////////////////////////////////////////////////////////////////

module cl_axi_ctl
  #(
    parameter DATA_WIDTH        = 512,
    parameter NUM_OT            = 64,        // Number of Outstanding Transaactions
    parameter AXI_START_ADDR    = 64'h0000_0000_0000_0000,
    parameter AXI_END_ADDR_MASK = 64'h0000_0000_1FFF_FFFF,
    parameter AXLEN_WIDTH       = 4,
    parameter AXID_WIDTH        = 6
    )
   (
    input logic                       clk,
    input logic                       rst_n,
    input logic                       i_wr_pulse,  // issue write request on AXI write channel.
    input logic                       i_rd_pulse,  // issue read  request on AXI read  channel.
    input logic [AXLEN_WIDTH-1:0]     i_cfg_axlen, // NOTE: This should be static. Do not change axlen while there are pending requests.
    input logic [31:0]                i_wdata_pattern, // data pattern to send on AXI bus.

    output logic                      o_wr_done_pulse   = '0,   // pulse when a bvalid is received
    output logic                      o_rd_done_pulse   = '0,   // pulse when a rlast is received
    output logic                      o_bresp_err_pulse = '0,
    output logic                      o_rresp_err_pulse = '0,
    output logic [15:0]               o_wr_req_pend     = '0,
    output logic [15:0]               o_rd_req_pend     = '0,

    //===================================================================
    // AXI Interface
    //===================================================================
    output logic [AXID_WIDTH-1:0]     o_axi_awid     = '0,
    output logic [63:0]               o_axi_awaddr   = 64'(AXI_START_ADDR),
    output logic [3:0]                o_axi_awregion = '0,
    output logic [AXLEN_WIDTH-1:0]    o_axi_awlen    = '0,
    output logic [2 : 0]              o_axi_awsize   = $clog2(DATA_WIDTH/8),
    output logic [1 : 0]              o_axi_awburst  = 2'b01, // INC burst
    output logic                      o_axi_awvalid  = '0,
    input logic                       i_axi_awready,

    output logic [AXID_WIDTH-1:0]     o_axi_wid    = '0,
    output logic [DATA_WIDTH-1:0]     o_axi_wdata  = '0,
    output logic [(DATA_WIDTH/8)-1:0] o_axi_wstrb  = '1,
    output logic                      o_axi_wlast,
    output logic                      o_axi_wvalid = '0,
    input logic                       i_axi_wready,

    input logic [AXID_WIDTH-1:0]      i_axi_bid,
    input logic [1:0]                 i_axi_bresp,
    input logic                       i_axi_bvalid,
    output logic                      o_axi_bready,

    output logic [AXID_WIDTH-1:0]     o_axi_arid     = '0,
    output logic [63:0]               o_axi_araddr   = 64'(AXI_START_ADDR),
    output logic [3:0]                o_axi_arregion = '0,
    output logic [AXLEN_WIDTH-1:0]    o_axi_arlen    = '0,
    output logic [2 : 0]              o_axi_arsize   = $clog2(DATA_WIDTH/8),
    output logic [1 : 0]              o_axi_arburst  = 2'b01, //INC burst
    output logic                      o_axi_arvalid  = '0,
    input logic                       i_axi_arready,

    input logic [AXID_WIDTH-1:0]      i_axi_rid,
    input logic [DATA_WIDTH-1:0]      i_axi_rdata,
    input logic [1:0]                 i_axi_rresp,
    input logic                       i_axi_rlast,
    input logic                       i_axi_rvalid,
    output logic                      o_axi_rready
    );

   //=====================================================================
   // local params
   //=====================================================================
   localparam BUS_WIDTH_BYTES = (DATA_WIDTH/8);
   // Bits required to represent BUS_WIDTH_BYTES.
   // Example, 256 bit bus == 32 Bytes Bus == log2(32) = 5.
   // Total bytes transferred = i_cfg_axlen * 32 Bytes
   //                         = i_cfg_axlen << 5
   //                         = i_cfg_axlen << BUS_WIDTH_SHIFT
   localparam BUS_WIDTH_SHIFT = $clog2(BUS_WIDTH_BYTES);

   //=====================================================================
   // Internal Signals
   //=====================================================================
   // reset
   logic sync_rst_n;
   always_ff @(posedge clk)
     sync_rst_n <= rst_n;

   localparam DATA_DW = DATA_WIDTH / 32;

   typedef enum logic[1:0] {
                            WR_IDLE = 0,
                            WR_ADDR = 1,
                            WR_DAT = 2
                            } wr_state_t;
   wr_state_t wr_state, wr_state_nxt;

   logic [$clog2(NUM_OT):0] wr_req_pend_q = '0; // AW requests in the queue
   logic [$clog2(NUM_OT):0] rd_req_pend_q = '0;
   logic [AXLEN_WIDTH-1:0]  wr_running_length = '0;
   logic [AXLEN_WIDTH:0]    axlen_abs_val;
   logic [11:0]             total_bytes_xfrd;
   logic [11:0]             total_bytes_xfr_wr;

   always_comb begin //{
      axlen_abs_val      = i_cfg_axlen + 1;
      total_bytes_xfrd   = $bits(total_bytes_xfrd)'({axlen_abs_val, {BUS_WIDTH_SHIFT{1'b0}}});
      total_bytes_xfr_wr = (wr_state == WR_IDLE) ? '0 : total_bytes_xfrd;
   end //}

   //===================================================================
   // Configuration
   //===================================================================
   logic        inc_wr_req;
   logic        dec_wr_req;
   logic        inc_rd_req;
   logic        dec_rd_req;

   always_comb begin //{
      inc_wr_req = i_wr_pulse && (wr_req_pend_q != NUM_OT);
      dec_wr_req = o_axi_awvalid && i_axi_awready;
      inc_rd_req = i_rd_pulse && (rd_req_pend_q != NUM_OT);
      dec_rd_req = o_axi_arvalid && i_axi_arready;
   end //}

   always_ff @(posedge clk) begin //{
     if (!sync_rst_n)
       wr_req_pend_q <= '0;
     else
       wr_req_pend_q <= wr_req_pend_q + inc_wr_req - dec_wr_req;

      if (!sync_rst_n)
        rd_req_pend_q <= '0;
      else
        rd_req_pend_q <= rd_req_pend_q + inc_rd_req - dec_rd_req;
   end //}

   //===================================================================
   // Write state machine
   //===================================================================
   //
   // Next State Logic
   //
   always_comb begin : WR_FSM_COMB //{
      wr_state_nxt = wr_state;

      unique case (wr_state)
        WR_IDLE: begin
           if (|wr_req_pend_q)
             wr_state_nxt = WR_ADDR;
           else
             wr_state_nxt = WR_IDLE;
        end

        WR_ADDR: begin
           if (i_axi_awready)
             wr_state_nxt = WR_DAT;
           else
             wr_state_nxt = WR_ADDR;
        end

        WR_DAT: begin //{
           if (o_axi_wlast && i_axi_wready && |wr_req_pend_q)
             wr_state_nxt = WR_ADDR;
           else if (o_axi_wlast && i_axi_wready)
             wr_state_nxt = WR_IDLE;
           else
             wr_state_nxt = WR_DAT;
        end //}
      endcase // unique case (wr_state)
   end : WR_FSM_COMB //}

   //
   // WR FSM state sequencer
   //
   always_ff @(posedge clk)
     if (!sync_rst_n)
       wr_state <= WR_IDLE;
     else
       wr_state <= wr_state_nxt;

   //
   // AW requests
   //
   logic [31:0] aw_offset_q = '0;

   always_ff @(posedge clk) begin //{
      o_axi_awid    <= '0;
      o_axi_awlen   <= i_cfg_axlen;
      o_axi_awvalid <= (wr_state_nxt == WR_ADDR);
      o_axi_awaddr  <= AXI_START_ADDR + aw_offset_q;

      if (o_axi_awvalid && i_axi_awready)
        aw_offset_q  <= (aw_offset_q + total_bytes_xfr_wr) & AXI_END_ADDR_MASK;
   end //}

   //
   // WR WDATA
   //
   always_ff @(posedge clk)
     if (wr_state == WR_ADDR)
       wr_running_length <= i_cfg_axlen;
     else if (o_axi_wvalid && i_axi_wready)
       wr_running_length <= wr_running_length - 1;

   always_ff @(posedge clk) begin //{
      o_axi_wid    <= '0;
      o_axi_wstrb  <= '1;
      o_axi_wvalid <= (wr_state_nxt == WR_DAT);

      if (wr_state == WR_ADDR) begin //{
         for (int dw = 0; dw < (DATA_WIDTH/32); dw++)
           o_axi_wdata[dw*32+:32] <= i_wdata_pattern + dw; // First Data Set
      end //}
      else if (o_axi_wvalid && i_axi_wready) begin //{
        for (int dw = 0; dw < (DATA_WIDTH/32); dw++)
          o_axi_wdata[dw*32+:32] <= o_axi_wdata[dw*32+:32] + 32'd1;
      end //}
   end //}

   assign o_axi_wlast = (wr_running_length == '0);

   //
   // B - Response
   //
   assign o_axi_bready = '1;
   always_ff @(posedge clk) begin
      o_bresp_err_pulse <= (i_axi_bvalid && o_axi_bready && (i_axi_bresp != '0));
      o_wr_done_pulse   <= (i_axi_bvalid && o_axi_bready);
   end

   //===================================================================
   // Read state machine
   //===================================================================
   logic [7:0] wr_rd_pend_q = '0;
   logic       inc_wr_rd_pend;
   logic       dec_wr_rd_pend;
   logic       rd_hold_off;
   always_comb begin
      inc_wr_rd_pend = (wr_rd_pend_q!='1) && (i_axi_bvalid && o_axi_bready);
      dec_wr_rd_pend = (wr_rd_pend_q!='0) && (o_axi_arvalid && i_axi_arready);
      rd_hold_off    = (wr_state != WR_IDLE) && (wr_rd_pend_q == '0); // hold off read requests until write reqs go through
   end

   always_ff @(posedge clk)
     if (!sync_rst_n)
       wr_rd_pend_q <= '0;
     else
       wr_rd_pend_q <= wr_rd_pend_q + inc_wr_rd_pend - dec_wr_rd_pend;

   //
   // Issue AR Requests
   //
   logic [31:0] ar_offset_q = '0;

   always_ff @(posedge clk) begin //{
      o_axi_arid   <= '0;
      o_axi_arlen  <= i_cfg_axlen;
      o_axi_araddr <= AXI_START_ADDR + ar_offset_q;

      if (!sync_rst_n || (o_axi_arvalid && i_axi_arready))
        o_axi_arvalid <= '0;
      else if (|rd_req_pend_q && !rd_hold_off)
        o_axi_arvalid <= '1;

      if (o_axi_arvalid && i_axi_arready)
        ar_offset_q  <= (ar_offset_q + total_bytes_xfrd) & AXI_END_ADDR_MASK;
   end //}

   // Always accept reads
   always_ff @(posedge clk) begin //{
      o_axi_rready      <= '1;
      o_rd_done_pulse   <= i_axi_rvalid && o_axi_rready && i_axi_rlast;
      o_rresp_err_pulse <= i_axi_rvalid && o_axi_rready && i_axi_rlast && (i_axi_rresp != '0);
   end //}

   //=======================================================
   // Debug Regs
   //=======================================================
   always_ff @(posedge clk) begin //{
      o_wr_req_pend <= wr_req_pend_q;
      o_rd_req_pend <= rd_req_pend_q;
   end //}

endmodule // cl_axi_ctl
