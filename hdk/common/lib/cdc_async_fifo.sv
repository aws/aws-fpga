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


// Async FF-based FIFO for CDC


//=============================================================================
// Module
//=============================================================================
module cdc_async_fifo
#(
  parameter DATA_WIDTH  = 32,
  parameter FIFO_DEPTH  = 128,
  parameter MEMORY_TYPE = "distributed"
)
(
  input  logic                  wr_clk,
  input  logic                  wr_rst_n,
  input  logic                  wr_push,
  input  logic [DATA_WIDTH-1:0] wr_di,
  output logic                  full,

  input  logic                  rd_clk,
  input  logic                  rd_rst_n,
  input  logic                  rd_pop,
  output logic [DATA_WIDTH-1:0] rd_do,
  output logic                  rd_vld,
  output logic                  empty
);

//=============================================================================
// Signals
//=============================================================================
  logic       fifo_rst_n_async;
  logic       fifo_rst_sync;

  logic       wr_en;
  logic       rd_en;

  logic       wr_rst_busy;
  logic       rd_rst_busy;

//=============================================================================
// Reset
//=============================================================================

  // Reset FIFO if receiving reset from either domain
  assign fifo_rst_n_async = wr_rst_n & rd_rst_n;

  xpm_cdc_async_rst
  #(
    .DEST_SYNC_FF         (4),
    .INIT_SYNC_FF         (0),
    .RST_ACTIVE_HIGH      (1)  // Active high reset
  )
  SYNC_RESET_IN
  (
    .src_arst             (~fifo_rst_n_async),
    .dest_clk             (wr_clk),
    .dest_arst            (fifo_rst_sync)
  );


  // Mask off enable based upon the FIFO status for safety
  assign wr_en = (~wr_rst_busy) & wr_push & (~full);
  assign rd_en = (~rd_rst_busy) & rd_pop  & (~empty);

  // XPM async fifo
  xpm_fifo_async
  #(
    .CASCADE_HEIGHT       (0),            // DECIMAL
    .CDC_SYNC_STAGES      (2),            // DECIMAL
    .DOUT_RESET_VALUE     ("0"),          // String
    .ECC_MODE             ("no_ecc"),     // String
    .FIFO_MEMORY_TYPE     (MEMORY_TYPE),  // String
    .FIFO_READ_LATENCY    (1),            // DECIMAL
    .FIFO_WRITE_DEPTH     (FIFO_DEPTH),   // DECIMAL
    .FULL_RESET_VALUE     (0),            // DECIMAL
    .PROG_EMPTY_THRESH    (10),           // DECIMAL
    .PROG_FULL_THRESH     (10),           // DECIMAL
    .RD_DATA_COUNT_WIDTH  (1),            // DECIMAL
    .READ_DATA_WIDTH      (DATA_WIDTH),   // DECIMAL
    .READ_MODE            ("std"),        // String
    .RELATED_CLOCKS       (0),            // DECIMAL
    .SIM_ASSERT_CHK       (0),            // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
    .USE_ADV_FEATURES     ("1707"),       // String
    .WAKEUP_TIME          (0),            // DECIMAL
    .WRITE_DATA_WIDTH     (DATA_WIDTH),   // DECIMAL
    .WR_DATA_COUNT_WIDTH  (1)             // DECIMAL
  )
  XPM_ASIC_FIFO
  (
    .wr_clk               (wr_clk),
    .rst                  (fifo_rst_sync),  // Must be synchronous to wr_clk.
    .wr_en                (wr_en),
    .din                  (wr_di),
    .full                 (full),
    .wr_rst_busy          (wr_rst_busy),

    .rd_clk               (rd_clk),
    .rd_en                (rd_en),
    .data_valid           (rd_vld),
    .dout                 (rd_do),
    .empty                (empty),
    .rd_rst_busy          (rd_rst_busy),

    // NOT USED
    .sleep                ('b0),
    .injectdbiterr        (1'b0),
    .injectsbiterr        (1'b0),
    .sbiterr              (),
    .almost_empty         (),
    .almost_full          (),
    .dbiterr              (),
    .overflow             (),
    .underflow            (),
    .prog_empty           (),
    .prog_full            (),
    .rd_data_count        (),
    .wr_data_count        (),
    .wr_ack               ()
  );

endmodule // cdc_async_fifo
