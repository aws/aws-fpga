// (c) Copyright 2013-2015, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// AMD, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) AMD shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or AMD had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// AMD products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of AMD products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
////////////////////////////////////////////////////////////

// ***************************
// * DO NOT MODIFY THIS FILE *
// ***************************

`timescale 1ps/1ps

module gtwizard_ultrascale_v1_7_18_gtwiz_buffbypass_tx #(

  parameter integer P_BUFFER_BYPASS_MODE       = 0,
  parameter integer P_TOTAL_NUMBER_OF_CHANNELS = 1,
  parameter integer P_MASTER_CHANNEL_POINTER   = 0

)(

  // User interface ports
  input  wire gtwiz_buffbypass_tx_clk_in,
  input  wire gtwiz_buffbypass_tx_reset_in,
  input  wire gtwiz_buffbypass_tx_start_user_in,
  input  wire gtwiz_buffbypass_tx_resetdone_in,
  output reg  gtwiz_buffbypass_tx_done_out  = 1'b0,
  output reg  gtwiz_buffbypass_tx_error_out = 1'b0,

  // Transceiver interface ports
  input  wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txphaligndone_in,
  input  wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txphinitdone_in,
  input  wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txdlysresetdone_in,
  input  wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txsyncout_in,
  input  wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txsyncdone_in,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txphdlyreset_out,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txphalign_out,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txphalignen_out,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txphdlypd_out,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txphinit_out,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txphovrden_out,
  output reg  [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txdlysreset_out = {P_TOTAL_NUMBER_OF_CHANNELS{1'b0}},
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txdlybypass_out,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txdlyen_out,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txdlyovrden_out,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txphdlytstclk_out,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txdlyhold_out,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txdlyupdown_out,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txsyncmode_out,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txsyncallin_out,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS-1):0] txsyncin_out

);


  // -------------------------------------------------------------------------------------------------------------------
  // Transmitter buffer bypass conditional generation, based on parameter values in module instantiation
  // -------------------------------------------------------------------------------------------------------------------
  localparam [1:0] ST_BUFFBYPASS_TX_IDLE                 = 2'd0;
  localparam [1:0] ST_BUFFBYPASS_TX_DEASSERT_TXDLYSRESET = 2'd1;
  localparam [1:0] ST_BUFFBYPASS_TX_WAIT_TXSYNCDONE      = 2'd2;
  localparam [1:0] ST_BUFFBYPASS_TX_DONE                 = 2'd3;

  generate if (1) begin: gen_gtwiz_buffbypass_tx_main

    // Use auto mode buffer bypass
    if (P_BUFFER_BYPASS_MODE == 0) begin : gen_auto_mode

      // For single-lane auto mode buffer bypass, perform specified input port tie-offs
      if (P_TOTAL_NUMBER_OF_CHANNELS == 1) begin : gen_assign_one_chan
        assign txphdlyreset_out  = 1'b0;
        assign txphalign_out     = 1'b0;
        assign txphalignen_out   = 1'b0;
        assign txphdlypd_out     = 1'b0;
        assign txphinit_out      = 1'b0;
        assign txphovrden_out    = 1'b0;
        assign txdlybypass_out   = 1'b0;
        assign txdlyen_out       = 1'b0;
        assign txdlyovrden_out   = 1'b0;
        assign txphdlytstclk_out = 1'b0;
        assign txdlyhold_out     = 1'b0;
        assign txdlyupdown_out   = 1'b0;
        assign txsyncmode_out    = 1'b1;
        assign txsyncallin_out   = txphaligndone_in;
        assign txsyncin_out      = 1'b0;
      end

      // For multi-lane auto mode buffer bypass, perform specified master and slave lane input port tie-offs
      else begin : gen_assign_multi_chan
        assign txphdlyreset_out  = {P_TOTAL_NUMBER_OF_CHANNELS{1'b0}};
        assign txphalign_out     = {P_TOTAL_NUMBER_OF_CHANNELS{1'b0}};
        assign txphalignen_out   = {P_TOTAL_NUMBER_OF_CHANNELS{1'b0}};
        assign txphdlypd_out     = {P_TOTAL_NUMBER_OF_CHANNELS{1'b0}};
        assign txphinit_out      = {P_TOTAL_NUMBER_OF_CHANNELS{1'b0}};
        assign txphovrden_out    = {P_TOTAL_NUMBER_OF_CHANNELS{1'b0}};
        assign txdlybypass_out   = {P_TOTAL_NUMBER_OF_CHANNELS{1'b0}};
        assign txdlyen_out       = {P_TOTAL_NUMBER_OF_CHANNELS{1'b0}};
        assign txdlyovrden_out   = {P_TOTAL_NUMBER_OF_CHANNELS{1'b0}};
        assign txphdlytstclk_out = {P_TOTAL_NUMBER_OF_CHANNELS{1'b0}};
        assign txdlyhold_out     = {P_TOTAL_NUMBER_OF_CHANNELS{1'b0}};
        assign txdlyupdown_out   = {P_TOTAL_NUMBER_OF_CHANNELS{1'b0}};

        genvar gi;
        for (gi = 0; gi < P_TOTAL_NUMBER_OF_CHANNELS; gi = gi + 1) begin : gen_assign_txsyncmode
          if (gi == P_MASTER_CHANNEL_POINTER)
            assign txsyncmode_out[gi] = 1'b1;
          else
            assign txsyncmode_out[gi] = 1'b0;
        end

        assign txsyncallin_out = {P_TOTAL_NUMBER_OF_CHANNELS{&txphaligndone_in}};
        assign txsyncin_out    = {P_TOTAL_NUMBER_OF_CHANNELS{txsyncout_in[P_MASTER_CHANNEL_POINTER]}};
      end

      // Detect the rising edge of the transmitter reset done re-synchronized input. Assign an internal buffer bypass
      // start signal to the OR of this reset done indicator, and the synchronous buffer bypass procedure user request.
      wire gtwiz_buffbypass_tx_resetdone_sync_int;

      gtwizard_ultrascale_v1_7_18_reset_inv_synchronizer reset_synchronizer_resetdone_inst (
        .clk_in  (gtwiz_buffbypass_tx_clk_in),
        .rst_in  (gtwiz_buffbypass_tx_resetdone_in),
        .rst_out (gtwiz_buffbypass_tx_resetdone_sync_int)
      );

      reg  gtwiz_buffbypass_tx_resetdone_reg = 1'b0;
      wire gtwiz_buffbypass_tx_start_int;

      always @(posedge gtwiz_buffbypass_tx_clk_in) begin
        if (gtwiz_buffbypass_tx_reset_in)
          gtwiz_buffbypass_tx_resetdone_reg <= 1'b0;
        else
          gtwiz_buffbypass_tx_resetdone_reg <= gtwiz_buffbypass_tx_resetdone_sync_int;
      end

      assign gtwiz_buffbypass_tx_start_int = (gtwiz_buffbypass_tx_resetdone_sync_int &&
                                             ~gtwiz_buffbypass_tx_resetdone_reg) || gtwiz_buffbypass_tx_start_user_in;

      // Synchronize the master channel's buffer bypass completion output (TXSYNCDONE) into the local clock domain
      // and detect its rising edge for purposes of safe state machine transitions
      reg  gtwiz_buffbypass_tx_master_syncdone_sync_reg = 1'b0;
      wire gtwiz_buffbypass_tx_master_syncdone_sync_int;
      wire gtwiz_buffbypass_tx_master_syncdone_sync_re;

      gtwizard_ultrascale_v1_7_18_bit_synchronizer bit_synchronizer_master_syncdone_inst (
        .clk_in (gtwiz_buffbypass_tx_clk_in),
        .i_in   (txsyncdone_in[P_MASTER_CHANNEL_POINTER]),
        .o_out  (gtwiz_buffbypass_tx_master_syncdone_sync_int)
      );

      always @(posedge gtwiz_buffbypass_tx_clk_in)
        gtwiz_buffbypass_tx_master_syncdone_sync_reg <= gtwiz_buffbypass_tx_master_syncdone_sync_int;

      assign gtwiz_buffbypass_tx_master_syncdone_sync_re = gtwiz_buffbypass_tx_master_syncdone_sync_int &&
                                                          ~gtwiz_buffbypass_tx_master_syncdone_sync_reg;

      // Synchronize the master channel's phase alignment completion output (TXPHALIGNDONE) into the local clock domain
      wire gtwiz_buffbypass_tx_master_phaligndone_sync_int;

      gtwizard_ultrascale_v1_7_18_bit_synchronizer bit_synchronizer_master_phaligndone_inst (
        .clk_in (gtwiz_buffbypass_tx_clk_in),
        .i_in   (txphaligndone_in[P_MASTER_CHANNEL_POINTER]),
        .o_out  (gtwiz_buffbypass_tx_master_phaligndone_sync_int)
      );

      // Implement a simple state machine to perform the transmitter auto mode buffer bypass procedure
      reg [1:0] sm_buffbypass_tx = ST_BUFFBYPASS_TX_IDLE;

      always @(posedge gtwiz_buffbypass_tx_clk_in) begin
        if (gtwiz_buffbypass_tx_reset_in) begin
          gtwiz_buffbypass_tx_done_out  <= 1'b0;
          gtwiz_buffbypass_tx_error_out <= 1'b0;
          txdlysreset_out               <= {P_TOTAL_NUMBER_OF_CHANNELS{1'b0}};
          sm_buffbypass_tx              <= ST_BUFFBYPASS_TX_IDLE;
        end
        else begin
          case (sm_buffbypass_tx)

            // Upon assertion of the internal buffer bypass start signal, assert TXDLYSRESET output(s)
            default: begin
              if (gtwiz_buffbypass_tx_start_int) begin
                gtwiz_buffbypass_tx_done_out  <= 1'b0;
                gtwiz_buffbypass_tx_error_out <= 1'b0;
                txdlysreset_out               <= {P_TOTAL_NUMBER_OF_CHANNELS{1'b1}};
                sm_buffbypass_tx              <= ST_BUFFBYPASS_TX_DEASSERT_TXDLYSRESET;
              end
            end

            // De-assert the TXDLYSRESET output(s)
            ST_BUFFBYPASS_TX_DEASSERT_TXDLYSRESET: begin
              txdlysreset_out  <= {P_TOTAL_NUMBER_OF_CHANNELS{1'b0}};
              sm_buffbypass_tx <= ST_BUFFBYPASS_TX_WAIT_TXSYNCDONE;
            end

            // Upon assertion of the synchronized TXSYNCDONE indicator, transition to the final state
            ST_BUFFBYPASS_TX_WAIT_TXSYNCDONE: begin
              if (gtwiz_buffbypass_tx_master_syncdone_sync_re)
                sm_buffbypass_tx <= ST_BUFFBYPASS_TX_DONE;
            end

            // Assert the buffer bypass procedure done user indicator, and set the procedure error flag if the
            // synchronized TXPHALIGNDONE indicator is not high
            ST_BUFFBYPASS_TX_DONE: begin
              gtwiz_buffbypass_tx_done_out  <= 1'b1;
              gtwiz_buffbypass_tx_error_out <= ~gtwiz_buffbypass_tx_master_phaligndone_sync_int;
              sm_buffbypass_tx              <= ST_BUFFBYPASS_TX_IDLE;
            end

          endcase
        end
      end

    end
  end
  endgenerate


endmodule
