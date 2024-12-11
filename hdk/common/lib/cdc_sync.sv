//=============================================================================
// Copyright 2022 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
//=============================================================================


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
