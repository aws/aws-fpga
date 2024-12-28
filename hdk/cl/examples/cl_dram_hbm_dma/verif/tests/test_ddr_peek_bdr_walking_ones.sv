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


// This test shows example of backdoor loading DRAM micron memory and frontdoor reading through DMA.
// The test covers valid rows, bank groups, banks and columns
// The test also covers some row, bank group, bank and column combinations.

module test_ddr_peek_bdr_walking_ones();
   import tb_type_defines_pkg::*;

   `include "base_test_utils.svh";

   int      fp;
   string   file_name;

   logic [63:0] addr = 64'h0;

   initial begin
      `define BYTE_COUNT 64
      `define BACKDOOR_DATA 512'h77777777777777776666666666666666555555555555555544444444444444443333333333333333222222222222222211111111111111110000000000000000

      tb.power_up(.clk_recipe_a(ClockRecipe::A1),
          .clk_recipe_b(ClockRecipe::B0),
          .clk_recipe_c(ClockRecipe::C0));
      initialize_ddr();

      //Disable ECC
      tb.poke_stat(.addr(8'h10), .intf("ddr"), .data(32'h0000_0008));
      //Write ECC register address in DRAM controller
      tb.poke_stat(.addr(8'h14), .intf("ddr"), .data(32'h0000_0000));

      $display("Starting Back Door Memory Load\n");
      file_name = $sformatf("axi_bkdr.mem");
      $display("file_name is %0s", file_name);
      fp = $fopen(file_name, "w");
      tb.card.write_cfg_info_to_file(fp);

      //Write 8*64 bits of data starting at address 'h0
      //Covers different columns
      $fdisplay(fp, "%0h %0h", 64'h0, `BACKDOOR_DATA);
      addr = 64'h0;
      tb.poke(.addr(addr), .data(`BACKDOOR_DATA), .size(DataSize::UINT512));

      //Write 8*64 bits of data starting at address 'h100
      //Covers different columns
      $fdisplay(fp, "%0h %0h", 64'h100, `BACKDOOR_DATA);
      addr = 64'h100;
      tb.poke(.addr(addr), .data(`BACKDOOR_DATA), .size(DataSize::UINT512));

      //Write 8*64 bits of data starting at address 'h300
      //Covers different columns
      $fdisplay(fp, "%0h %0h", 64'h300, `BACKDOOR_DATA);
      addr = 64'h300;
      tb.poke(.addr(addr), .data(`BACKDOOR_DATA), .size(DataSize::UINT512));

      //Write 8*64 bits of data starting at address 'h1000
      //Covers different columns
      $fdisplay(fp, "%0h %0h", 64'h1000, `BACKDOOR_DATA);
      addr = 64'h1000;
      tb.poke(.addr(addr), .data(`BACKDOOR_DATA), .size(DataSize::UINT512));

      //Covers rows
      for ( int i=0; i<4; i++) begin
         $fdisplay(fp, "%0h %0h", 64'h2_0000 << i, `BACKDOOR_DATA);
         addr = 64'h2_0000 << i;
         tb.poke(.addr(addr), .data(`BACKDOOR_DATA), .size(DataSize::UINT512));
      end

      //Covers some row, bank group, bank and column combinations
      for ( int i=0; i<4; i++) begin
         $fdisplay(fp, "%0h %0h", 64'h2_0040 << i, `BACKDOOR_DATA);
         addr = 64'h2_0040 << i;
         tb.poke(.slot_id(0), .addr(addr), .data(`BACKDOOR_DATA), .size(DataSize::UINT512));
      end

      $fclose(fp);

      // Not using backdoor load (Errata #8)
      tb.nsec_delay(500);

      ddr_peeks(64'h0, 1, `BACKDOOR_DATA);
      ddr_peeks(64'h100, 1, `BACKDOOR_DATA);
      ddr_peeks(64'h300, 1, `BACKDOOR_DATA);
      ddr_peeks(64'h1000, 1, `BACKDOOR_DATA);
      ddr_peeks(64'h2_0000, 4, `BACKDOOR_DATA);
      ddr_peeks(64'h2_0040, 4, `BACKDOOR_DATA);

      tb.nsec_delay(2000);
      tb.power_down();

      report_pass_fail_status();

      $finish;
   end // initial begin

   task ddr_peeks(logic [63:0] addr, int num_xfers, logic [511:0] data);
      logic [63:0] bdr_addr;
      logic [511:0] read_data;
      //Front Door read data
      for ( int i=0; i<num_xfers; i++) begin
         bdr_addr = addr << i;
         tb.peek(.addr(bdr_addr), .data(read_data), .size(DataSize::UINT512));
         $display("Read Data for Addr %h: is %h", bdr_addr, read_data);

         if (read_data != data) begin
            $error(" ** ERROR ** Read Data mismatch for Addr: %h\nExpected: %h\nActual: %h", bdr_addr, data, read_data);
            error_count++;
         end
      end
   endtask // ddr_peeks

endmodule // test_ddr_peek_bdr_walking_ones
