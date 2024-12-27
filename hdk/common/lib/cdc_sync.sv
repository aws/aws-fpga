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


// Single- or Multi-bit Synchronizer based on Xilinx XPM


//=============================================================================
// Module
//=============================================================================
module cdc_sync
#(
  parameter WIDTH          = 1,
  parameter DEST_SYNC_FF   = 4,
  parameter INIT_SYNC_FF   = 0,
  parameter SIM_ASSERT_CHK = 0,
  parameter SRC_INPUT_REG  = 0
)
(
  input  logic              src_clk,
  input  logic [WIDTH-1:0]  src_in,

  input  logic              dest_clk,
  output logic [WIDTH-1:0]  dest_out
);

  generate

    if (WIDTH == 1)

      xpm_cdc_single
      #(
        .DEST_SYNC_FF       (DEST_SYNC_FF),
        .INIT_SYNC_FF       (INIT_SYNC_FF),
        .SIM_ASSERT_CHK     (SIM_ASSERT_CHK),
        .SRC_INPUT_REG      (SRC_INPUT_REG)
      )
      CDC_XPM_SINGLE
      (
        .src_clk            (src_clk),
        .src_in             (src_in),

        .dest_clk           (dest_clk),
        .dest_out           (dest_out)
      );

    else // >1

      xpm_cdc_array_single
      #(
        .DEST_SYNC_FF       (DEST_SYNC_FF),
        .INIT_SYNC_FF       (INIT_SYNC_FF),
        .SIM_ASSERT_CHK     (SIM_ASSERT_CHK),
        .SRC_INPUT_REG      (SRC_INPUT_REG),
        .WIDTH              (WIDTH)
      )
      CDC_XPM_MULTI
      (
        .src_clk            (src_clk),
        .src_in             (src_in),

        .dest_clk           (dest_clk),
        .dest_out           (dest_out)
      );

  endgenerate

endmodule   //cdc_sync
