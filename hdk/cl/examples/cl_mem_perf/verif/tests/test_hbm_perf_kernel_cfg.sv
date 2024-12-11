// Amazon FPGA Hardware Development Kit
//
// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

module test_hbm_perf_kernel_cfg();

   import tb_type_defines_pkg::*;

   `include "base_test_utils.svh";

   initial begin
     automatic logic [31:0] read_data = 32'h0;
     tb.power_up(.clk_recipe_a(ClockRecipe::A1),
          .clk_recipe_b(ClockRecipe::B0),
          .clk_recipe_c(ClockRecipe::C0));
      aws_clkgen_dsrt_rst();
      initialize_hbm();
      deselect_cl_tst_hw();

      ocl_peek_poke_peek(.register(`KERN_CFG_REG),      .expected_default_data(32'h0),  .new_data(32'h1));
      ocl_peek_poke_peek(.register(`CHANNEL_AVAIL_REG), .expected_default_data(32'h20), .is_read_only(1'b1));
      ocl_peek_poke_peek(.register(`NUM_OT_REG),        .expected_default_data(32'h40), .is_read_only(1'b1));
      ocl_peek_poke_peek(.register(`CHNL_SEL_REG),      .expected_default_data(32'h0),  .new_data(32'h1F));
      ocl_peek_poke_peek(.register(`AXLEN_REG),         .expected_default_data(32'h0),  .new_data(32'hFFFF));
      ocl_peek_poke_peek(.register(`WDATA_PATTERN_REG), .expected_default_data(32'h0),  .new_data(32'hBEAD));

      ocl_peek_poke_peek(.register(12'h420), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h424), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h428), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h42C), .is_missing_reg(1'b1));

      // Write 0 to clear these registers
      ocl_peek_poke_peek(.register(`WR_CYC_CNT_LO_REG), .expected_default_data(32'h0), .new_data(32'h0));
      ocl_peek_poke_peek(.register(`WR_CYC_CNT_HI_REG), .expected_default_data(32'h0), .new_data(32'h0));
      ocl_peek_poke_peek(.register(`WR_TIMER_LO_REG),   .expected_default_data(32'h0), .new_data(32'h0));
      ocl_peek_poke_peek(.register(`WR_TIMER_HI_REG),   .expected_default_data(32'h0), .new_data(32'h0));
      ocl_peek_poke_peek(.register(`WR_LATENCY_REG),    .expected_default_data(32'h0), .new_data(32'h0));
      ocl_peek_poke_peek(.register(`WR_OT_REG),         .expected_default_data(32'h0), .is_read_only(1'b1));
      ocl_peek_poke_peek(.register(`BRESP_ERR_REG),     .expected_default_data(32'h0), .new_data(32'h0));

      ocl_peek_poke_peek(.register(12'h44C), .is_missing_reg(1'b1));

      // Write 0 to clear these registers
      ocl_peek_poke_peek(.register(`RD_CYC_CNT_LO_REG), .expected_default_data(32'h0), .new_data(32'h0));
      ocl_peek_poke_peek(.register(`RD_CYC_CNT_HI_REG), .expected_default_data(32'h0), .new_data(32'h0));
      ocl_peek_poke_peek(.register(`RD_TIMER_LO_REG),   .expected_default_data(32'h0), .new_data(32'h0));
      ocl_peek_poke_peek(.register(`RD_TIMER_HI_REG),   .expected_default_data(32'h0), .new_data(32'h0));
      ocl_peek_poke_peek(.register(`RD_LATENCY_REG),    .expected_default_data(32'h0), .new_data(32'h0));
      ocl_peek_poke_peek(.register(`RD_OT_REG),         .expected_default_data(32'h0), .is_read_only(1'b1));
      ocl_peek_poke_peek(.register(`RRESP_ERR_REG),     .expected_default_data(32'h0), .new_data(32'h0));

      ocl_peek_poke_peek(.register(`WR_CTL_REG),        .expected_default_data(32'h0),  .new_data(32'hF));
      #1000ns;
      ocl_peek_poke_peek(.register(`WR_CTL_REG),        .expected_default_data(32'hF),  .new_data(32'h0));
      ocl_peek_poke_peek(.register(`RD_CTL_REG),        .expected_default_data(32'h0),  .new_data(32'hF));
      #1000ns;
      ocl_peek_poke_peek(.register(`RD_CTL_REG),        .expected_default_data(32'hF),  .new_data(32'h0));

      tb.peek_ocl(.addr(`WR_CYC_CNT_LO_REG), .data(read_data));
      if (read_data == 32'h0) begin
         $error("Read from HBM performance kernel WR_CYC_CNT_LO_REG, address %x, was 0 after running", `WR_CYC_CNT_LO_REG);
         error_count++;
      end
      read_data = 32'h0;

      tb.peek_ocl(.addr(`WR_TIMER_LO_REG), .data(read_data));
      if (read_data == 32'h0) begin
         $error("Read from HBM performance kernel WR_TIMER_LO_REG, address %x, was 0 after running", `WR_TIMER_LO_REG);
         error_count++;
      end
      read_data = 32'h0;

      tb.peek_ocl(.addr(`RD_CYC_CNT_LO_REG), .data(read_data));
      if (read_data == 32'h0) begin
         $error("Read from HBM performance kernel RD_CYC_CNT_LO_REG, address %x, was 0 after running", `RD_CYC_CNT_LO_REG);
          error_count++;
      end
      read_data = 32'h0;

      tb.peek_ocl(.addr(`RD_TIMER_LO_REG), .data(read_data));
      if (read_data == 32'h0) begin
         $error("Read from HBM performance kernel RD_TIMER_LO_REG, address %x, was 0 after running", `RD_TIMER_LO_REG);
          error_count++;
      end
      read_data = 32'h0;

      ocl_peek_poke_peek(.register(12'h46C), .is_missing_reg(1'b1));

      ocl_peek_poke_peek(.register(12'h470), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h474), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h478), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h47C), .is_missing_reg(1'b1));

      ocl_peek_poke_peek(.register(12'h480), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h484), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h488), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h48C), .is_missing_reg(1'b1));

      ocl_peek_poke_peek(.register(12'h490), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h494), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h498), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h49C), .is_missing_reg(1'b1));

      ocl_peek_poke_peek(.register(12'h4A0), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4A4), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4A8), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4AC), .is_missing_reg(1'b1));

      ocl_peek_poke_peek(.register(12'h4B0), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4B4), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4B8), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4BC), .is_missing_reg(1'b1));

      ocl_peek_poke_peek(.register(12'h4C0), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4C4), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4C8), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4CC), .is_missing_reg(1'b1));

      ocl_peek_poke_peek(.register(12'h4D0), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4D4), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4D8), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4DC), .is_missing_reg(1'b1));

      ocl_peek_poke_peek(.register(12'h4E0), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4E4), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4E8), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4EC), .is_missing_reg(1'b1));

      ocl_peek_poke_peek(.register(12'h4F0), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4F4), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4F8), .is_missing_reg(1'b1));
      ocl_peek_poke_peek(.register(12'h4FC), .is_missing_reg(1'b1));

      #500ns;
      tb.power_down();

      report_pass_fail_status();

      $finish;
   end
endmodule // test_hbm_perf_kernel_cfg
