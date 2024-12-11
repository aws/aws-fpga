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
// CL_KERNEL_REGS
// --------------
// - Instantiate registers/CSRs for the block
// - Provide a simple CFG bus interface to access registers
// - Various timers/counters to measure performance
//
///////////////////////////////////////////////////////////////////////////////////////

module cl_kernel_regs
  #(
    parameter NUM_CHANNELS = 32
    )
   (
    input  logic                      clk_main_a0,
    input  logic                      rst_main_a0,
    input  logic [31:0]               i_num_ot,
    //
    // CFG Interface
    //
    input  logic [31:0]               i_cfg_addr,
    input  logic [31:0]               i_cfg_wdata,
    input  logic                      i_cfg_wr,
    input  logic                      i_cfg_rd,
    output logic [31:0]               o_cfg_rdata,
    output logic                      o_cfg_ack,
    //
    // Channel specific outputs/inputs
    //
    output logic [31:0]               o_wr_start = '0,
    output logic [31:0]               o_rd_start = '0,
    output logic [31:0]               o_cfg_axlen,
    output logic [31:0]               o_cfg_wdata_pattern,
    //
    // For Performance Metrics
    //
    input  logic [31:0]               i_wr_done,
    input  logic [31:0]               i_rd_done,
    input  logic [31:0]               i_bresp_err,
    input  logic [31:0]               i_rresp_err,
    input  logic [31:0]               i_wr_pend_txns [0:NUM_CHANNELS-1],
    input  logic [31:0]               i_rd_pend_txns [0:NUM_CHANNELS-1],
    //
    // Kernel Enable
    //
    output logic                      o_kernel_enable
   );

   //===================================================================
   // local signals
   //===================================================================
   logic [31:0]                       bresp_err_q = '0;
   logic [31:0]                       rresp_err_q = '0;

   //===================================================================
   // Flop stages for inputs
   //===================================================================
   always_ff @(posedge clk_main_a0) begin //{
      bresp_err_q <= i_bresp_err;
      rresp_err_q <= i_rresp_err;
   end //}

   //===================================================================
   // CFG WR/RD reqs
   //===================================================================
   logic [7:0]  cfg_addr_q = '0;
   logic        cfg_wr_q = '0;
   logic        cfg_rd_q = '0;
   logic        cfg_wr_pulse_q = '0;
   logic        cfg_rd_pulse_q = '0;
   logic [31:0] cfg_rdata_q = '0;
   logic [31:0] cfg_wdata_q = '0;

   always_ff @(posedge clk_main_a0)
     if (!rst_main_a0) begin //{
        cfg_wr_q <= '0;
        cfg_rd_q <= '0;
     end //}
     else begin //{
        cfg_wr_q       <= i_cfg_wr;
        cfg_rd_q       <= i_cfg_rd;
        cfg_addr_q     <= i_cfg_addr[0+:$bits(cfg_addr_q)];
        cfg_wdata_q    <= i_cfg_wdata;
        cfg_wr_pulse_q <= ~cfg_wr_q & i_cfg_wr;
        cfg_rd_pulse_q <= ~cfg_rd_q & i_cfg_rd;
     end //}

   always_ff @(posedge clk_main_a0)
     if (!rst_main_a0)
       o_cfg_ack <= '0;
     else
       o_cfg_ack <= cfg_wr_pulse_q | cfg_rd_pulse_q;

   assign o_cfg_rdata = cfg_rdata_q;

   //=====================================================================
   // CSRs
   //=====================================================================
   localparam KERN_CFG_REG        = 8'h00;
   localparam CHANNEL_AVAIL_REG   = 8'h04;
   localparam NUM_OT_REG          = 8'h08;
   localparam CHNL_SEL_REG        = 8'h0C;
   localparam AXLEN_REG           = 8'h10;
   localparam WDATA_PATTERN_REG   = 8'h14;
   localparam WR_CTL_REG          = 8'h18;
   localparam RD_CTL_REG          = 8'h1C;
   //
   localparam WR_CYC_CNT_LO_REG   = 8'h30;
   localparam WR_CYC_CNT_HI_REG   = 8'h34;
   localparam WR_TIMER_LO_REG     = 8'h38;
   localparam WR_TIMER_HI_REG     = 8'h3c;
   localparam WR_LATENCY_REG      = 8'h40;
   localparam WR_OT_REG           = 8'h44;
   localparam BRESP_ERR_REG       = 8'h48;
   //
   localparam RD_CYC_CNT_LO_REG   = 8'h50;
   localparam RD_CYC_CNT_HI_REG   = 8'h54;
   localparam RD_TIMER_LO_REG     = 8'h58;
   localparam RD_TIMER_HI_REG     = 8'h5C;
   localparam RD_LATENCY_REG      = 8'h60;
   localparam RD_OT_REG           = 8'h64;
   localparam RRESP_ERR_REG       = 8'h68;

   logic [31:0] kern_cfg_reg      = '0;
   logic [31:0] channel_avail_reg = '0;
   logic [31:0] num_ot_reg        = '0;
   logic [31:0] chnl_sel_reg      = '0;
   logic [31:0] wr_ctl_reg        = '0;
   logic [31:0] rd_ctl_reg        = '0;
   logic [31:0] axlen_reg         = '0;
   logic [31:0] wdata_pattern_reg = '0;
   logic [31:0] wr_cyc_cnt_lo_reg = '0;
   logic [31:0] wr_cyc_cnt_hi_reg = '0;
   logic [31:0] wr_timer_lo_reg   = '0;
   logic [31:0] wr_timer_hi_reg   = '0;
   logic [31:0] wr_latency_reg    = '0;
   logic [31:0] wr_ot_reg         = '0;
   logic [31:0] bresp_err_reg     = '0;
   logic [31:0] rd_cyc_cnt_lo_reg = '0;
   logic [31:0] rd_cyc_cnt_hi_reg = '0;
   logic [31:0] rd_timer_lo_reg   = '0;
   logic [31:0] rd_timer_hi_reg   = '0;
   logic [31:0] rd_latency_reg    = '0;
   logic [31:0] rd_ot_reg         = '0;
   logic [31:0] rresp_err_reg     = '0;

   //=====================================================================
   // Read Datapath
   //=====================================================================
   always_ff @(posedge clk_main_a0)
     unique case (cfg_addr_q) //{
       KERN_CFG_REG      : cfg_rdata_q <= kern_cfg_reg;
       CHANNEL_AVAIL_REG : cfg_rdata_q <= 32'(NUM_CHANNELS);
       NUM_OT_REG        : cfg_rdata_q <= i_num_ot;
       CHNL_SEL_REG      : cfg_rdata_q <= chnl_sel_reg;
       WR_CTL_REG        : cfg_rdata_q <= wr_ctl_reg;
       RD_CTL_REG        : cfg_rdata_q <= rd_ctl_reg;
       AXLEN_REG         : cfg_rdata_q <= axlen_reg;
       WDATA_PATTERN_REG : cfg_rdata_q <= wdata_pattern_reg;
       WR_CYC_CNT_LO_REG : cfg_rdata_q <= wr_cyc_cnt_lo_reg;
       WR_CYC_CNT_HI_REG : cfg_rdata_q <= wr_cyc_cnt_hi_reg;
       WR_TIMER_LO_REG   : cfg_rdata_q <= wr_timer_lo_reg;
       WR_TIMER_HI_REG   : cfg_rdata_q <= wr_timer_hi_reg;
       WR_LATENCY_REG    : cfg_rdata_q <= wr_latency_reg;
       WR_OT_REG         : cfg_rdata_q <= wr_ot_reg;
       BRESP_ERR_REG     : cfg_rdata_q <= bresp_err_reg;
       RD_CYC_CNT_LO_REG : cfg_rdata_q <= rd_cyc_cnt_lo_reg;
       RD_CYC_CNT_HI_REG : cfg_rdata_q <= rd_cyc_cnt_hi_reg;
       RD_TIMER_LO_REG   : cfg_rdata_q <= rd_timer_lo_reg;
       RD_TIMER_HI_REG   : cfg_rdata_q <= rd_timer_hi_reg;
       RD_LATENCY_REG    : cfg_rdata_q <= rd_latency_reg;
       RD_OT_REG         : cfg_rdata_q <= rd_ot_reg;
       RRESP_ERR_REG     : cfg_rdata_q <= rresp_err_reg;
       default           : cfg_rdata_q <= 32'hBAAD_DEC0;
     endcase // unique case (cfg_addr_q) }

   //===================================================================
   // Writes
   //===================================================================
   always_ff @(posedge clk_main_a0) begin //{
      if ((cfg_addr_q == KERN_CFG_REG ) && cfg_wr_pulse_q) kern_cfg_reg <= cfg_wdata_q;
      if ((cfg_addr_q == CHNL_SEL_REG ) && cfg_wr_pulse_q) chnl_sel_reg <= cfg_wdata_q;
      if ((cfg_addr_q == WR_CTL_REG   ) && cfg_wr_pulse_q) wr_ctl_reg   <= cfg_wdata_q;
      if ((cfg_addr_q == RD_CTL_REG   ) && cfg_wr_pulse_q) rd_ctl_reg   <= cfg_wdata_q;
      if ((cfg_addr_q == AXLEN_REG    ) && cfg_wr_pulse_q) axlen_reg    <= cfg_wdata_q;
      if ((cfg_addr_q == WDATA_PATTERN_REG) && cfg_wr_pulse_q) wdata_pattern_reg <= cfg_wdata_q;
   end //}

   //====================================================================
   // Statistics counters
   //====================================================================
   logic [7:0]  wr_done_acc   = '0; // Max value doesnt exceed 8'd255
   logic [7:0]  rd_done_acc   = '0; // Max value doesnt exceed 8'd255
   logic [7:0]  wr_done_acc_q;
   logic [7:0]  rd_done_acc_q;
   logic [63:0] wr_cyc_cnt_q  = '0;
   logic [63:0] rd_cyc_cnt_q  = '0;
   logic [63:0] wr_timer_q    = '0;
   logic [63:0] rd_timer_q    = '0;
   logic [31:0] chnl_wr_inp   = '0, chnl_wr_inp_q; // Per channel write in progress
   logic [31:0] chnl_rd_inp   = '0, chnl_rd_inp_q; // Per channel write in progress
   logic        wr_req, wr_req_q = '0, wr_1st_actv_q = '0;
   logic        rd_req, rd_req_q = '0, rd_1st_actv_q = '0;
   logic [31:0] wr_pend_txns_q [0:NUM_CHANNELS-1];
   logic [31:0] rd_pend_txns_q [0:NUM_CHANNELS-1];

   // Accumulate control signals from all channels
   always_comb begin //{
      wr_req = o_wr_start[chnl_sel_reg[4:0]]; // Select the channel to measure latency
      rd_req = o_rd_start[chnl_sel_reg[4:0]]; // Select the channel to measure latency

      wr_done_acc = '0;
      rd_done_acc = '0;

      for (int ii = 0; ii < NUM_CHANNELS; ii++) begin //{
         wr_done_acc     = (|i_wr_done) ? (wr_done_acc + i_wr_done[ii]) : '0; // Count number of done pulses in a single clock cycle.
         rd_done_acc     = (|i_rd_done) ? (rd_done_acc + i_rd_done[ii]) : '0; // Count number of done pulses in a single clock cycle.
         chnl_wr_inp[ii] = (i_wr_pend_txns[ii][31:0] != '0);
         chnl_rd_inp[ii] = (i_rd_pend_txns[ii][31:0] != '0);
      end //}
   end //}

   // pipeline to help with timing
   lib_pipe #(.WIDTH($bits(wr_done_acc)), .STAGES(3)) PIPE_WR_ACC_I (.clk(clk_main_a0), .rst_n(1'b1), .in_bus(wr_done_acc), .out_bus(wr_done_acc_q));
   lib_pipe #(.WIDTH($bits(rd_done_acc)), .STAGES(3)) PIPE_RD_ACC_I (.clk(clk_main_a0), .rst_n(1'b1), .in_bus(rd_done_acc), .out_bus(rd_done_acc_q));
   lib_pipe #(.WIDTH($bits(chnl_wr_inp)), .STAGES(3)) PIPE_WR_INP_I (.clk(clk_main_a0), .rst_n(1'b1), .in_bus(chnl_wr_inp), .out_bus(chnl_wr_inp_q));
   lib_pipe #(.WIDTH($bits(chnl_rd_inp)), .STAGES(3)) PIPE_RD_INP_I (.clk(clk_main_a0), .rst_n(1'b1), .in_bus(chnl_rd_inp), .out_bus(chnl_rd_inp_q));

   //
   // Detect when the 1st write/read request for a specifc channel is active to measure latency
   //
   always_ff @(posedge clk_main_a0) begin //{
      wr_req_q <= wr_req;
      rd_req_q <= rd_req;

      if (i_wr_done[chnl_sel_reg[4:0]])
        wr_1st_actv_q <= '0;
      else if (wr_req && !wr_req_q)
        wr_1st_actv_q <= '1;

      if (i_rd_done[chnl_sel_reg[4:0]])
        rd_1st_actv_q <= '0;
      else if (rd_req && !rd_req_q)
        rd_1st_actv_q <= '1;
   end //}

   //
   // Counters/Timers
   //
   always_ff @(posedge clk_main_a0) begin //{
      //
      // WR Cycle Count (aggregate for all channels)
      //
      if ((cfg_addr_q == WR_CYC_CNT_LO_REG) && cfg_wr_pulse_q && (cfg_wdata_q == '0))
        wr_cyc_cnt_q <= '0;
      else
        wr_cyc_cnt_q <= wr_cyc_cnt_q + wr_done_acc_q;

      //
      // RD Cycle Count (aggregate for all channels)
      //
      if ((cfg_addr_q == RD_CYC_CNT_LO_REG) && cfg_wr_pulse_q && (cfg_wdata_q == '0))
        rd_cyc_cnt_q <= '0;
      else
        rd_cyc_cnt_q <= rd_cyc_cnt_q + rd_done_acc_q;

      //
      // WR Timer : Increment when writes are in progress
      //
      if ((cfg_addr_q == WR_TIMER_LO_REG) && cfg_wr_pulse_q && (cfg_wdata_q == '0))
        wr_timer_q <= '0;
      else if ((|o_wr_start) || (|chnl_wr_inp_q))
        wr_timer_q <= wr_timer_q + 1;

      //
      // RD Timer : Increment when Reads are in progress
      //
      if ((cfg_addr_q == RD_TIMER_LO_REG) && cfg_wr_pulse_q && (cfg_wdata_q == '0))
        rd_timer_q <= '0;
      else if ((|o_rd_start) || (|chnl_rd_inp_q))
        rd_timer_q <= rd_timer_q + 1;

      //
      // WR Latency : Measure latency for first write request (channel selected in CHNL_SEL_REG)
      //
      if ((cfg_addr_q == WR_LATENCY_REG) && cfg_wr_pulse_q && (cfg_wdata_q == '0))
        wr_latency_reg <= '0;
      else if (wr_1st_actv_q)
        wr_latency_reg <= wr_latency_reg + 1;

      //
      // RD Latency : Measure latency for first rd request (channel selected in CHNL_SEL_REG)
      //
      if ((cfg_addr_q == RD_LATENCY_REG) && cfg_wr_pulse_q && (cfg_wdata_q == '0))
        rd_latency_reg <= '0;
      else if (rd_1st_actv_q)
        rd_latency_reg <= rd_latency_reg + 1;

      //
      // BRESP Error Regs : Sticky set by HW, cleared by SW
      //
      if ((cfg_addr_q == BRESP_ERR_REG) && cfg_wr_pulse_q && (cfg_wdata_q == '0))
        bresp_err_reg <= '0;
      else if (|bresp_err_q)
        bresp_err_reg <= bresp_err_reg | bresp_err_q;

      //
      // RRESP Error Regs : Sticky set by HW, cleared by SW
      //
      if ((cfg_addr_q == RRESP_ERR_REG) && cfg_wr_pulse_q && (cfg_wdata_q == '0))
        rresp_err_reg <= '0;
      else if (|rresp_err_q)
        rresp_err_reg <= rresp_err_reg | rresp_err_q;
   end //}

   // Readback
   always_comb begin //{
      {wr_cyc_cnt_hi_reg, wr_cyc_cnt_lo_reg} = wr_cyc_cnt_q;
      {rd_cyc_cnt_hi_reg, rd_cyc_cnt_lo_reg} = rd_cyc_cnt_q;
      {wr_timer_hi_reg,   wr_timer_lo_reg}   = wr_timer_q;
      {rd_timer_hi_reg,   rd_timer_lo_reg}   = rd_timer_q;
   end //}

   //
   // WR_OT_REG / RD_OT_REG, based on channel in CHNL_SEL_REG
   //
   always_ff @(posedge clk_main_a0) begin //{
      for (int ii = 0; ii < NUM_CHANNELS; ii++) begin //{
         wr_pend_txns_q[ii] <= i_wr_pend_txns[ii][31:0];
         rd_pend_txns_q[ii] <= i_rd_pend_txns[ii][31:0];
      end //}
      wr_ot_reg <= wr_pend_txns_q[chnl_sel_reg[4:0]];
      rd_ot_reg <= rd_pend_txns_q[chnl_sel_reg[4:0]];
   end //}

   //===================================================================
   // Outputs
   //===================================================================
   assign o_kernel_enable     = kern_cfg_reg[0];
   assign o_cfg_axlen         = axlen_reg;
   assign o_cfg_wdata_pattern = wdata_pattern_reg;

   always_ff @(posedge clk_main_a0) begin //{
      o_wr_start <= wr_ctl_reg & {32{o_kernel_enable}};
      o_rd_start <= rd_ctl_reg & {32{o_kernel_enable}};
   end //}

endmodule // cl_kernel_regs
