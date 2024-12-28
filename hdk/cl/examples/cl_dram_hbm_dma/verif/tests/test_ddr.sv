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


module test_ddr();

   import tb_type_defines_pkg::*;

   `include "base_test_utils.svh";

   initial begin

      tb.power_up(.clk_recipe_a(ClockRecipe::A0),
                  .clk_recipe_b(ClockRecipe::B0),
                  .clk_recipe_c(ClockRecipe::C0));
      initialize_ddr();
      deselect_cl_tst_hw();

      // select the ATG hardware
      tb.poke_ocl(.addr(64'h130), .data(1));

      $display("[%t] : Programming cl_tst registers for DDR sequence 0 traffic", $realtime);
      program_cl_tst(.base_addr(64'h0100), .test_addr(`DDR_BASE_ADDR), .enable_write(1'b1), .enable_read(1'b1),
              .axi_len(8'h07), .iter_mode(1'b0), .num_iter(0), .num_inst(16'h000f));

      $display("[%t] : Programming cl_tst registers for DDR sequence 1 traffic", $realtime);
      program_cl_tst(.base_addr(64'h0100), .test_addr(`DDR_BASE_ADDR + `DDR_LEVEL_1), .enable_write(1'b1), .enable_read(1'b1),
              .axi_len(8'h07), .iter_mode(1'b0), .num_iter(0), .num_inst(16'h000f));

      $display("[%t] : Programming cl_tst registers for DDR sequence 2 traffic", $realtime);
      program_cl_tst(.base_addr(64'h0100), .test_addr(`DDR_BASE_ADDR + `DDR_LEVEL_2), .enable_write(1'b1), .enable_read(1'b1),
              .axi_len(8'h07), .iter_mode(1'b0), .num_iter(0), .num_inst(16'h000f));

      $display("[%t] : Programming cl_tst registers for DDR sequence 3 traffic", $realtime);
      program_cl_tst(.base_addr(64'h0100), .test_addr(`DDR_BASE_ADDR + `DDR_LEVEL_3), .enable_write(1'b1), .enable_read(1'b1),
              .axi_len(8'h07), .iter_mode(1'b0), .num_iter(0), .num_inst(16'h000f));

      #500ns;
      tb.power_down();

      report_pass_fail_status();

      $finish;
   end
endmodule // test_ddr
