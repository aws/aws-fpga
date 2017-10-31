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

   logic [63:0]  addr;

   logic [511:0]  wide_read_data;

   int           error_count;
   int           fail;

   initial begin
      error_count = 0;
      fail = 0;

      tb.power_up();

      tb.nsec_delay(500);
      
      tb.poke_stat(.addr(8'h0c), .ddr_idx(0), .data(32'h0000_0000));
      tb.poke_stat(.addr(8'h0c), .ddr_idx(1), .data(32'h0000_0000));
      tb.poke_stat(.addr(8'h0c), .ddr_idx(2), .data(32'h0000_0000));
      
      // select the ATG hardware
       
      tb.poke_ocl(.addr(64'h130), .data(0));
      tb.poke_ocl(.addr(64'h230), .data(0));
      tb.poke_ocl(.addr(64'h330), .data(0));
      tb.poke_ocl(.addr(64'h430), .data(0));

      // allow memory to initialize
      tb.nsec_delay(25000);

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
            $display("Read Data mismatch for Addr %h: Exp %h, Act %h", addr, {512{1'b1}}, wide_read_data);
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
            $display("Read Data mismatch for Addr %h: Exp %h, Act %h", addr, {512{1'b1}}, wide_read_data);
            error_count++;
         end         
      end 
      
      tb.nsec_delay(500);

      // Power down
      tb.power_down();

      //---------------------------
      // Report pass/fail status
      //---------------------------
      $display("[%t] : Checking total error count...", $realtime);
      if (error_count > 0) begin
         fail = 1;
      end
      $display("[%t] : Detected %3d errors during this test", $realtime, error_count);

      if (fail) begin
         $display("[%t] : *** TEST FAILED ***", $realtime);
      end else begin
         $display("[%t] : *** TEST PASSED ***", $realtime);
      end

      $finish;
   end

endmodule // test_ddr_peek_poke
