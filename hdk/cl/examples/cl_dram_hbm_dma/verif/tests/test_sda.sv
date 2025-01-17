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


// Test for SDA interface

module test_sda();

   import tb_type_defines_pkg::*;

   `include "base_test_utils.svh";

   logic [63:0]  sda_addr;
   logic [31:0]  sda_data;

   logic [31:0]  read_data;
   int           timeout_count;

   initial begin

      tb.power_up(.clk_recipe_a(ClockRecipe::A0),
                  .clk_recipe_b(ClockRecipe::B0),
                  .clk_recipe_c(ClockRecipe::C0));
      initialize_ddr();

      sda_addr  = 'h0;
      for (int i=0; i<64; i=i+4) begin
         sda_addr = sda_addr + i;

         sda_data = $urandom();

         tb.poke_sda(.addr(sda_addr), .data(sda_data));

         #100ns;

         timeout_count = 0;
         do begin
            tb.peek_sda(.addr(sda_addr), .data(read_data));
            $display("[%t] : Read data for sda_addr %h read_data %h.", $realtime, sda_addr, read_data);
            timeout_count++;
         end while ((read_data[31:0] !== sda_data[31:0]) && (timeout_count < 1000)); // UNMATCHED !!

         if ((timeout_count == 1000) || (read_data[31:0] !== sda_data[31:0])) begin
            $error("[%t] : *** ERROR *** Read data mismatch for sda exp_data %h act_data %h.", $realtime, sda_data, read_data);
            error_count++;
         end

         #100ns;

         $display("[%t] : Waiting for SDA write and read activity to complete", $realtime);
      end // for (int i=0; i<63; i=i+4)

      #500ns;
      tb.power_down();

      report_pass_fail_status();

      $finish;
   end // initial begin
endmodule // test_sda
