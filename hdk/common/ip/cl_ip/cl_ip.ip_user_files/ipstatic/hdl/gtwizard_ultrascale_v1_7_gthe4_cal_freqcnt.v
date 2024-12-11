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

module gtwizard_ultrascale_v1_7_18_gthe4_cpll_cal_freq_counter # (
  parameter REVISION = 1
)(
  output reg  [17:0] freq_cnt_o = 18'd0,
  output reg  done_o,
  input  wire rst_i,
  input  wire [15:0] test_term_cnt_i,
  input  wire ref_clk_i,
  input  wire test_clk_i
);
  //****************************************************************************
  //  Local Parameters
  //****************************************************************************
  localparam RESET_STATE = 0;
  localparam MEASURE_STATE = 1;
  localparam HOLD_STATE = 2;
  localparam UPDATE_STATE = 3;
  localparam DONE_STATE = 4;

  //****************************************************************************
  //  Local Signals
  //****************************************************************************
  reg [17:0] testclk_cnt = 18'h00000;
  reg [15:0] refclk_cnt = 16'h0000;
  reg [3:0] testclk_div4 = 4'h1;
  wire testclk_rst;
  wire testclk_en;
  reg [5:0] hold_clk = 6'd0;
  reg [4:0] state = 5'd1;

  (* ASYNC_REG = "TRUE" *) reg tstclk_rst_dly1, tstclk_rst_dly2;
  (* ASYNC_REG = "TRUE" *) reg testclk_en_dly1, testclk_en_dly2;

  //
  // need to get testclk_rst into TESTCLK_I domain
  //
  always @(posedge test_clk_i)
  begin
    tstclk_rst_dly1 <= testclk_rst;
    tstclk_rst_dly2 <= tstclk_rst_dly1;
  end

  //
  // need to get testclk_en into TESTCLK_I domain
  //
  always @(posedge test_clk_i)
  begin
    testclk_en_dly1 <= testclk_en;
    testclk_en_dly2 <= testclk_en_dly1;
  end

  always @(posedge test_clk_i)
  begin
    if (tstclk_rst_dly2 == 1'b1)
    begin
      testclk_div4 <= 4'h1;
    end
    else
    begin
      testclk_div4 <= {testclk_div4[2:0], testclk_div4[3]};
    end
  end

  wire testclk_rst_sync;

  gtwizard_ultrascale_v1_7_18_reset_synchronizer reset_synchronizer_testclk_rst_inst (
    .clk_in (test_clk_i),
    .rst_in   (testclk_rst),
    .rst_out  (testclk_rst_sync)
  );

  always @(posedge test_clk_i or posedge testclk_rst_sync)
  begin
    if (testclk_rst_sync == 1'b1)
    begin
      testclk_cnt <= 0;
    end
    else if (testclk_en_dly2 == 1'b1 && testclk_div4 == 4'h8)
    begin
      testclk_cnt <= testclk_cnt + 1;
    end
  end

/*   always @(posedge test_clk_i or posedge testclk_rst)
  begin
    if (testclk_rst == 1'b1)
    begin
      testclk_cnt <= 0;
    end
    else if (testclk_en_dly2 == 1'b1 && testclk_div4 == 4'h8)
    begin
      testclk_cnt <= testclk_cnt + 1;
    end
  end */

  always @(posedge ref_clk_i or posedge rst_i)
  begin
    if (rst_i)
      done_o <= 1'b0;
    else
      done_o <= state[DONE_STATE];
  end

  always @(posedge ref_clk_i or posedge rst_i)
  begin
    if (rst_i) begin
      state <= 0;
      state[RESET_STATE] <= 1'b1;
    end
    else begin
      state <= 0;
      case (1'b1) // synthesis parallel_case full_case
        state[RESET_STATE]:
          begin
            if (hold_clk == 6'h3F)
              state[MEASURE_STATE] <= 1'b1;
            else
              state[RESET_STATE] <= 1'b1;
          end
        state[MEASURE_STATE]:
          begin
            if (refclk_cnt == test_term_cnt_i)
              state[HOLD_STATE] <= 1'b1;
            else
              state[MEASURE_STATE] <= 1'b1;
          end
        state[HOLD_STATE]:
          begin
            if (hold_clk == 6'hF)
              state[UPDATE_STATE] <= 1'b1;
            else
              state[HOLD_STATE] <= 1'b1;
          end
        state[UPDATE_STATE]:
          begin
            freq_cnt_o <= testclk_cnt;
            state[DONE_STATE] <= 1'b1;
          end
        state[DONE_STATE]:
          begin
            state[DONE_STATE] <= 1'b1;
          end
      endcase
    end
  end

  assign testclk_rst = state[RESET_STATE];
  assign testclk_en = state[MEASURE_STATE];


  always @(posedge ref_clk_i)
  begin
    if (state[RESET_STATE] == 1'b1 || state[HOLD_STATE] == 1'b1)
      hold_clk <= hold_clk + 1;
    else
      hold_clk <= 0;
  end

  always @(posedge ref_clk_i)
  begin
    if (state[MEASURE_STATE] == 1'b1)
      refclk_cnt <= refclk_cnt + 1;
    else
      refclk_cnt <= 0;
  end




endmodule
