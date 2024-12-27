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


///////////////////////////////////////////////////////////////////////////////////
// Module
// -------
// CL_CLK_FREQ
//
// Description
// -----------
// * Measure Clock Frequency of input clocks
// * Ref clock runs at 100MHz.
// * Registers on CFG bus
///////////////////////////////////////////////////////////////////////////////////

module cl_clk_freq
  #(
    parameter NUM_OF_CLKS = 9
    )
   (
    input logic                   i_ref_clk,
    input logic                   i_ref_rst_n,

    input logic                   i_clk_main_a0,
    input logic                   i_rst_main_n,
    cfg_bus_t.slave               s_cfg_bus,     // in clk_main_a0

    input logic [NUM_OF_CLKS-1:0] i_test_clks
    );

   //=================================================================================
   // local signals and params
   //=================================================================================
`ifdef AWS_SIM
   localparam REF_CNT_MAX = 10000;
`else
   localparam REF_CNT_MAX = 100000000; //Counter value for 1 second at 100MHz clk
`endif

   localparam CTR_WIDTH = 32;
   localparam MAX_NUM_CLKS_SUPPORTED = 10;

   logic [CTR_WIDTH-1:0]   ref_ctr_q = '0;
   logic [CTR_WIDTH-1:0]   sync_clk_freq_ctr_q [MAX_NUM_CLKS_SUPPORTED-1:0];
   logic [CTR_WIDTH-1:0]   clk_freq_ctr_q [NUM_OF_CLKS-1:0] = {default: '0};
   logic                   clr_ctr_q = '0;
   logic                   cdc_clr_ctr_q;
   logic                   measure_inp_q = '0;
   logic                   main_measure_done_q;
   logic                   ref_measure_done_q = '0;
   logic [NUM_OF_CLKS-1:0] cdc_active_q, cdc_clr_clk_ctr;
   logic [CTR_WIDTH-1:0]   ref_freq_ctr_reg;
   logic [7:0]             cfg_addr_q = '0;
   logic                   cfg_wr_q = '0;
   logic                   cfg_rd_q = '0;
   logic                   cfg_wr_pulse_q = '0;
   logic                   cfg_rd_pulse_q = '0;
   logic [31:0]            cfg_rdata_q = '0;
   logic [31:0]            cfg_wdata_q = '0;

   cfg_bus_t cfg_bus_q();

   //=================================================================================
   // CSR
   //=================================================================================
   localparam CTL_REG      = 8'h00;
   localparam REF_FREQ_CTR = 8'h04;
   localparam FREQ_CTR_0   = 8'h10;
   localparam FREQ_CTR_1   = 8'h14;
   localparam FREQ_CTR_2   = 8'h18;
   localparam FREQ_CTR_3   = 8'h1C;
   localparam FREQ_CTR_4   = 8'h20;
   localparam FREQ_CTR_5   = 8'h24;
   localparam FREQ_CTR_6   = 8'h28;
   localparam FREQ_CTR_7   = 8'h2C;
   localparam FREQ_CTR_8   = 8'h30;
   localparam FREQ_CTR_9   = 8'h34;

   logic [31:0]            ctl_reg = '0;

   //===================================================================
   // CFG WR/RD reqs
   //===================================================================
   // Pipeline cfg_bus for better timing
   lib_pipe
     #(
       .WIDTH  ($bits(cfg_addr_q) + $bits(cfg_wdata_q) + $bits(cfg_wr_q) + $bits(cfg_rd_q)),
       .STAGES (4)
       )
   PIPE_CFG_REQ_CCT_I
     (
      .clk     (i_clk_main_a0                                                     ),
      .rst_n   (1'd1                                                              ),
      .in_bus  ({s_cfg_bus.addr[7:0], s_cfg_bus.wdata, s_cfg_bus.wr, s_cfg_bus.rd}),
      .out_bus ({cfg_bus_q.addr[7:0], cfg_bus_q.wdata, cfg_bus_q.wr, cfg_bus_q.rd})
      );

   // ACK
   lib_pipe
     #(
       .WIDTH  ($bits(cfg_rdata_q) + $bits(cfg_rd_q)),
       .STAGES (4)
       )
   PIPE_CFG_ACK_CCT_I
     (
      .clk     (i_clk_main_a0                   ),
      .rst_n   (1'd1                            ),
      .in_bus  ({cfg_bus_q.rdata, cfg_bus_q.ack}),
      .out_bus ({s_cfg_bus.rdata, s_cfg_bus.ack})
      );

   always_ff @(posedge i_clk_main_a0)
     if (!i_rst_main_n) begin //{
        cfg_wr_q <= '0;
        cfg_rd_q <= '0;
     end //}
     else begin //{
        cfg_wr_q       <= cfg_bus_q.wr;
        cfg_rd_q       <= cfg_bus_q.rd;
        cfg_addr_q     <= cfg_bus_q.addr[0+:$bits(cfg_addr_q)];
        cfg_wdata_q    <= cfg_bus_q.wdata;
        cfg_wr_pulse_q <= ~cfg_wr_q & cfg_bus_q.wr;
        cfg_rd_pulse_q <= ~cfg_rd_q & cfg_bus_q.rd;
     end //}

   always_ff @(posedge i_clk_main_a0)
     if (!i_rst_main_n)
       cfg_bus_q.ack <= '0;
     else
       cfg_bus_q.ack <= cfg_wr_pulse_q | cfg_rd_pulse_q;

   assign cfg_bus_q.rdata = cfg_rdata_q;

   //===================================================================
   // Read Datapath
   //===================================================================
   always_ff @(posedge i_clk_main_a0)
     unique case (cfg_addr_q) //{
       CTL_REG      : cfg_rdata_q <= ctl_reg;
       REF_FREQ_CTR : cfg_rdata_q <= 32'(ref_freq_ctr_reg);
       FREQ_CTR_0   : cfg_rdata_q <= sync_clk_freq_ctr_q[0];
       FREQ_CTR_1   : cfg_rdata_q <= sync_clk_freq_ctr_q[1];
       FREQ_CTR_2   : cfg_rdata_q <= sync_clk_freq_ctr_q[2];
       FREQ_CTR_3   : cfg_rdata_q <= sync_clk_freq_ctr_q[3];
       FREQ_CTR_4   : cfg_rdata_q <= sync_clk_freq_ctr_q[4];
       FREQ_CTR_5   : cfg_rdata_q <= sync_clk_freq_ctr_q[5];
       FREQ_CTR_6   : cfg_rdata_q <= sync_clk_freq_ctr_q[6];
       FREQ_CTR_7   : cfg_rdata_q <= sync_clk_freq_ctr_q[7];
       FREQ_CTR_8   : cfg_rdata_q <= sync_clk_freq_ctr_q[8];
       FREQ_CTR_9   : cfg_rdata_q <= sync_clk_freq_ctr_q[9];
       default      : cfg_rdata_q <= 32'hDEAD_DEAD;
     endcase // unique case (cfg_addr_q) }

   //=================================================================================
   // Start/Stop clock measurements
   //=================================================================================
   //
   // Set by SW, Cleared by HW after REF_CNT_MAX cycles
   // synchronize "start/clr signal" between i_clk_main_a0 (faster) and i_ref_clk (slower)
   //
   always_ff @(posedge i_clk_main_a0) begin //{
      if (cfg_wr_pulse_q && (cfg_addr_q == CTL_REG))
        clr_ctr_q <= cfg_wdata_q[31];

      // freq measurement in progress
      if (cfg_wr_pulse_q && (cfg_addr_q == CTL_REG) && cfg_wdata_q[0])
        measure_inp_q <= '1;
      else if (main_measure_done_q || clr_ctr_q)
        measure_inp_q <= '0;
   end //}

   //==================================================================
   // CTL_REG
   // -------
   // bit [31]   | RW | 1 = Clear all the counters
   // bit [30:1] | RO | 0 = RSVD
   // bit [0]    | RW | Set by SW to Start frequency measurement
   //                 | Cleared by HW when frequency measurement is done.
   //==================================================================
   always_comb begin //{
      ctl_reg[31]   = clr_ctr_q;
      ctl_reg[30:1] = '0;
      ctl_reg[0]    = measure_inp_q;
   end //}

   // sync "start" into i_ref_clk. This is level signal.
   xpm_cdc_single
     #(
       .DEST_SYNC_FF   (4),
       .INIT_SYNC_FF   (0),
       .SIM_ASSERT_CHK (0),
       .SRC_INPUT_REG  (0)
       )
   CDC_START_I
     (
      .src_clk  (i_clk_main_a0      ),
      .src_in   (measure_inp_q      ),
      .dest_clk (i_ref_clk          ),
      .dest_out (cdc_measure_inp_q  )
      );

   // sync clr into i_ref_clk. This is level signal.
   xpm_cdc_single
     #(
       .DEST_SYNC_FF   (4),
       .INIT_SYNC_FF   (0),
       .SIM_ASSERT_CHK (0),
       .SRC_INPUT_REG  (0)
       )
   CDC_CLR_I
     (
      .src_clk  (i_clk_main_a0 ),
      .src_in   (clr_ctr_q     ),
      .dest_clk (i_ref_clk     ),
      .dest_out (cdc_clr_ctr_q )
      );

   always_ff @(posedge i_ref_clk) begin : CLK_MSRE_INP_I //{
      // Reference counter
      if (cdc_clr_ctr_q)
        ref_ctr_q <= '0;
      else if (cdc_measure_inp_q && (ref_ctr_q != REF_CNT_MAX))
        ref_ctr_q <= ref_ctr_q + 1;

      ref_measure_done_q <= (ref_ctr_q == REF_CNT_MAX);
   end : CLK_MSRE_INP_I //}

   // sync active_q back into clk_main_a0 for CSRs
   xpm_cdc_single
     #(
       .DEST_SYNC_FF   (4),
       .INIT_SYNC_FF   (0),
       .SIM_ASSERT_CHK (0),
       .SRC_INPUT_REG  (0)
       )
   CDC_MAIN_ACTV_I
     (
      .src_clk  (i_ref_clk           ),
      .src_in   (ref_measure_done_q  ),
      .dest_clk (i_clk_main_a0       ),
      .dest_out (main_measure_done_q )
      );

   //
   // Sync ref_ctr_q into clk_main_a0 for REF_FREQ_CTR reg
   //
   xpm_cdc_array_single
     #(
       .DEST_SYNC_FF   (2),
       .INIT_SYNC_FF   (0),
       .SIM_ASSERT_CHK (0),
       .SRC_INPUT_REG  (0),
       .WIDTH          (CTR_WIDTH)
       )
   CDC_CLK_CTR_I
     (
      .src_clk         (i_ref_clk        ),
      .src_in          (ref_ctr_q        ),
      .dest_clk        (i_clk_main_a0    ),
      .dest_out        (ref_freq_ctr_reg )
      );

   //=================================================================================
   // Frequency Measurement Logic for all the input test clocks.
   // CDC for active signals and clock frequency counters in all other clock domains.
   //=================================================================================
   generate //{
      for (genvar gg = 0; gg < NUM_OF_CLKS; gg++) begin : FOR_CDC_ACTV //{
         // sync "clr" into all test clocks domain
         xpm_cdc_single
                       #(
                         .DEST_SYNC_FF   (4),
                         .INIT_SYNC_FF   (0),
                         .SIM_ASSERT_CHK (0),
                         .SRC_INPUT_REG  (0)
                         )
         CDC_SYNC_CLR_I
                       (
                        .src_clk  (i_ref_clk           ),
                        .src_in   (cdc_clr_ctr_q       ),
                        .dest_clk (i_test_clks[gg]     ),
                        .dest_out (cdc_clr_clk_ctr[gg] )
                        );

         // Sync "active" into all the test clks domain
         xpm_cdc_single
                       #(
                         .DEST_SYNC_FF   (4),
                         .INIT_SYNC_FF   (0),
                         .SIM_ASSERT_CHK (0),
                         .SRC_INPUT_REG  (0)
                         )
         CDC_SYNC_ACTV_I
                       (
                        .src_clk  (i_ref_clk         ),
                        .src_in   (cdc_measure_inp_q ),
                        .dest_clk (i_test_clks[gg]   ),
                        .dest_out (cdc_active_q[gg]  )
                        );

         //
         // Clock counters in each i_test_clks domain
         //
         always_ff @(posedge i_test_clks[gg])
           if (cdc_clr_clk_ctr[gg])
             clk_freq_ctr_q[gg] <= '0;
           else if (cdc_active_q[gg] && (clk_freq_ctr_q[gg] != '1))
             clk_freq_ctr_q[gg] <= clk_freq_ctr_q[gg] + 1;

         //
         // Sync back clock counters into i_clk_main_a0 domain
         // We read back this value only when active_q = 0. So simple multi-bit synchronizer is sufficient.
         //
         xpm_cdc_array_single
           #(
             .DEST_SYNC_FF   (2),
             .INIT_SYNC_FF   (0),
             .SIM_ASSERT_CHK (0),
             .SRC_INPUT_REG  (0),
             .WIDTH          (CTR_WIDTH)
             )
         CDC_CLK_CTR_I
           (
            .src_clk         (i_test_clks[gg]         ),
            .src_in          (clk_freq_ctr_q[gg]      ),
            .dest_clk        (i_clk_main_a0           ),
            .dest_out        (sync_clk_freq_ctr_q[gg] )
            );
      end : FOR_CDC_ACTV //}
   endgenerate //}

endmodule // cl_clk_freq
