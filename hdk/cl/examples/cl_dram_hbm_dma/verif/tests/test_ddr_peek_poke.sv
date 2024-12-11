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
// 
// Description: This test is to catch the memory aliasing issues in DDR memory models.
// The test walks through the DDR address range and tests the contents.

module test_ddr_peek_poke();

   import tb_type_defines_pkg::*;

   `include "base_test_utils.svh";

   logic [63:0]  addr;
   logic [511:0]  wide_read_data;

   initial begin
      tb.power_up(.clk_recipe_a(ClockRecipe::A0),
                  .clk_recipe_b(ClockRecipe::B0),
                  .clk_recipe_c(ClockRecipe::C0));
      initialize_ddr();      
      deselect_cl_tst_hw();

      for ( int i=0; i<26; i++) begin
//Walk through DDR address range to check if any of the bits in DDR Rank are tied to 0.         
         addr = 'h40 << i;
         $display("Write to Addr %b", addr);
         tb.poke(.addr(addr), .data({512{1'b1}}), .size(DataSize::UINT512));
         addr = 'h0;
         $display("Write to Addr %b", addr);
         tb.poke(.addr(addr), .data({512{1'b0}}), .size(DataSize::UINT512));
         addr = 'h40 << i;
         $display("Read  to Addr %b", addr);
         tb.peek(.addr(addr), .data(wide_read_data), .size(DataSize::UINT512));
         if (wide_read_data != {512{1'b1}}) begin
            $error("Read Data mismatch for Addr %h: Exp %h, Act %h", addr, {512{1'b1}}, wide_read_data);
            error_count++;
         end
//Walk through DDR address range to check if two adjacent bits are wrongly wired.         
         addr = 'h40 << i;
         $display("Write to Addr %b", addr);
         tb.poke(.addr(addr), .data({512{1'b1}}), .size(DataSize::UINT512));
         addr = 'h20 << i;
         $display("Write to Addr %b", addr);
         tb.poke(.addr(addr), .data({512{1'b0}}), .size(DataSize::UINT512));
         addr = 'h40 << i;
         $display("Read  to Addr %b", addr);
         tb.peek(.addr(addr), .data(wide_read_data), .size(DataSize::UINT512));
         if (wide_read_data != {512{1'b1}}) begin
            $error("Read Data mismatch for Addr %h: Exp %h, Act %h", addr, {512{1'b1}}, wide_read_data);
            error_count++;
         end         
      end 
      
      tb.nsec_delay(500);

      // Power down
      tb.power_down();
      
      report_pass_fail_status();

      $finish;
   end

endmodule // test_ddr_peek_poke
