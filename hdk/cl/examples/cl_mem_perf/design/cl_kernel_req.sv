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
// CL_KERNEL_REQ
// --------------
// - Issue WR/RD request pulse based on number of outstanding transactions per channel
// - Track pending transactions per channel
// - Perform CDC between clk_main_a0 and clk_hbm
//
///////////////////////////////////////////////////////////////////////////////////////

module cl_kernel_req
  #(
    parameter NUM_OT = 64 // Number of Outstanding Transaactions
    )
   (
    input  logic                      clk_main_a0,
    input  logic                      rst_main_a0,
    input  logic                      clk_hbm,
    input  logic                      rst_hbm_n,

    input  logic                      i_main_start_req,       // Start signal in clk_main_a0
    output logic [31:0]               o_main_pend_txns,       // clk_main_a0 domain
    output logic                      o_main_req_done,        // clk_main_a0 domain
    output logic                      o_main_resp_err,        // clk_main_a0 domain

    output logic                      o_hbm_req_pulse = '0,   // request pulse in clk_hbm domain
    input  logic                      i_hbm_done_pulse,       // done pulse in clk_hbm domain
    input  logic                      i_hbm_resp_err
    );

   //=====================================================================
   // local params/signals
   //=====================================================================
   localparam PEND_TXNS_WIDTH =       $clog2(NUM_OT); // Need 1 extra bit to store absolute values (not 0-based). Example: log2(64) = 6.
   logic                              sync_rst_main_n;
   logic                              sync_hbm_rst_n  = '0;
   logic                              main_start_req_q;
   logic                              hbm_done_q = '0;
   logic                              hbm_resp_err_q = '0;
   logic [PEND_TXNS_WIDTH:0]          main_pend_txns_q = '0; // example: [6:0] = 7 bits is sufficient to store absolute value of 64.
   logic                              inc_pend_txn;
   logic                              dec_pend_txn;
   logic                              req_fifo_full;
   logic                              hbm_req_valid;
   logic                              main_req_done_q = '0;

   //=====================================================================
   // flop stages for inputs, to help with timing
   //=====================================================================
   //
   // NOTE: using lib_pipe pipelines to help with timing congestion and help to
   // physically space out clk_main_a0 as far as possible from the main cl_kernel_regs.sv during placement.
   //
   localparam PIPE_STAGES = 4;
   lib_pipe #(.WIDTH(1), .STAGES(PIPE_STAGES)) PIPE_RST_MAIN   (.clk(clk_main_a0), .rst_n(1'b1), .in_bus(rst_main_a0),      .out_bus(sync_rst_main_n));
   lib_pipe #(.WIDTH(1), .STAGES(PIPE_STAGES)) PIPE_START_MAIN (.clk(clk_main_a0), .rst_n(1'b1), .in_bus(i_main_start_req), .out_bus(main_start_req_q));

   // HBM done signals
   always_ff @(posedge clk_hbm) begin //{
      sync_hbm_rst_n <= rst_hbm_n;
      hbm_done_q     <= i_hbm_done_pulse;
      hbm_resp_err_q <= i_hbm_resp_err;
   end //}

   //=====================================================================
   // Track pending transactions and issue more if it is <= NUM_OT
   //=====================================================================
   always_comb begin //{
      inc_pend_txn = !req_fifo_full && main_start_req_q && (main_pend_txns_q < NUM_OT);
      dec_pend_txn = o_main_req_done;
   end //}

   always_ff @(posedge clk_main_a0)
     main_pend_txns_q <= main_pend_txns_q + inc_pend_txn - dec_pend_txn;

   //=====================================================================
   // CDC clk_main_a0 to clk_hbm (M2H) for wr/rd requests
   // Push to this FIFO when there are less than NUM_OT outstanding requests to the HBM core
   //=====================================================================
   cdc_async_fifo
     #(
       .DATA_WIDTH  (1      ),
       .FIFO_DEPTH  (NUM_OT ), // Supports NUM_OT of outstanding transactions.
       .MEMORY_TYPE ("auto" )
       )
   CDC_M2H_REQ_FIFO
     (
      .wr_clk       (clk_main_a0     ),
      .wr_rst_n     (sync_rst_main_n ),
      .wr_push      (inc_pend_txn    ),
      .wr_di        (1'd1            ),
      .full         (req_fifo_full   ),
      .rd_clk       (clk_hbm         ),
      .rd_rst_n     (sync_hbm_rst_n  ),
      .rd_pop       (1'd1            ),
      .rd_do        (                ), // No connect
      .rd_vld       (hbm_req_valid   ),
      .empty        (                )
      );

   //
   // output HBM request
   // NOTE: This need not be single cycle pulse.
   // If the signal extends for multiple clk cycles, it means those many number of WR/RD requests are issued.
   //
   always_ff @(posedge clk_hbm)
     o_hbm_req_pulse <= hbm_req_valid;

   //=====================================================================
   // CDC clk_hbm to clk_main_a0 (H2M) for wr/rd responses
   // Push to this FIFO when there is a wr_done/rd_done pulse from HBM
   //=====================================================================
   cdc_async_fifo
     #(
       .DATA_WIDTH  (1      ),
       .FIFO_DEPTH  (16     ), // 16 deep FIFO is min, but is sufficient since we pop the data as soon as it is available.
       .MEMORY_TYPE ("auto" )
       )
   CDC_H2M_RESP_FIFO
     (
      .wr_clk       (clk_hbm          ),
      .wr_rst_n     (sync_hbm_rst_n   ),
      .wr_push      (hbm_done_q       ),
      .wr_di        (hbm_resp_err_q   ),
      .full         (                 ),
      .rd_clk       (clk_main_a0      ),
      .rd_rst_n     (sync_rst_main_n  ),
      .rd_pop       (1'd1             ),
      .rd_do        (main_resp_err    ), // No connect
      .rd_vld       (main_req_done    ),
      .empty        (                 )
      );

   //
   // Output WR/RD Request Response in clk_main_a0
   // NOTE: This need not be single cycle pulse.
   // If the signal extends for multiple clk cycles, it means those many number of WR/RD responses are rcvd.
   //
   logic main_resp_err_vld;
   assign main_resp_err_vld = main_resp_err & main_req_done;

   lib_pipe #(.WIDTH(1), .STAGES(PIPE_STAGES)) PIPE_RQ_DONE_MAIN (.clk(clk_main_a0), .rst_n(1'b1), .in_bus(main_req_done),     .out_bus(o_main_req_done));
   lib_pipe #(.WIDTH(1), .STAGES(PIPE_STAGES)) PIPE_RQ_RESP_MAIN (.clk(clk_main_a0), .rst_n(1'b1), .in_bus(main_resp_err_vld), .out_bus(o_main_resp_err));

   //
   // Pipeline pending transactions count for better placement
   //
   lib_pipe
     #(
       .WIDTH  ($bits(o_main_pend_txns)),
       .STAGES (PIPE_STAGES            )
       )
   PIPE_PEND_MAIN
     (
      .clk     (clk_main_a0            ),
      .rst_n   (1'b1                   ),
      .in_bus  (32'(main_pend_txns_q)  ),
      .out_bus (o_main_pend_txns       )
      );

endmodule // cl_kernel_ctl
