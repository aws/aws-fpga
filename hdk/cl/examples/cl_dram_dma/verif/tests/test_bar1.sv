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

module test_bar1();

   import tb_type_defines_pkg::*;
   
   logic [63:0]  bar1_addr;
   logic [31:0]  bar1_data;

   logic [63:0]  bar1_addr;
   logic [31:0]  bar1_data;
   
   logic [31:0]  read_data;
   int           timeout_count;

   int           error_count;
   int           fail;
   
   initial begin
      tb.power_up();

      tb.nsec_delay(500);

      tb.poke_stat(.addr(8'h0c), .ddr_idx(0), .data(32'h0000_0000));
      tb.poke_stat(.addr(8'h0c), .ddr_idx(1), .data(32'h0000_0000));
      tb.poke_stat(.addr(8'h0c), .ddr_idx(2), .data(32'h0000_0000));
      
      bar1_addr  = 'h0;
      for (int i=0; i<64; i=i+4) begin
         bar1_addr = bar1_addr + i;
         
         bar1_data = $urandom();

         tb.poke_bar1(.addr(bar1_addr), .data(bar1_data));

         #100ns;

         timeout_count = 0;
         do begin
            tb.peek_bar1(.addr(bar1_addr), .data(read_data));
            $display("[%t] : Read data for bar1_addr %h read_data %h.", $realtime, bar1_addr, read_data);
            timeout_count++;
         end while ((read_data[31:0] !== bar1_data[31:0]) && (timeout_count < 1000)); // UNMATCHED !!

         if ((timeout_count == 1000) || (read_data[31:0] !== bar1_data[31:0])) begin
            $display("[%t] : *** ERROR *** Read data mismatch for bar1 exp_data %h act_data %h.", $realtime, bar1_data, read_data);
            error_count++;
         end

         #100ns;
         
         timeout_count = 0;

         $display("[%t] : Waiting for BAR1 write and read activity to complete", $realtime);
      end // for (int i=0; i<63; i=i+4)
      
      #500ns;


      tb.power_down();

      //---------------------------
      // Report pass/fail status
      //---------------------------
      $display("[%t] : Checking total error count...", $realtime);
      if (error_count > 0)begin
         fail = 1;
      end
      $display("[%t] : Detected %3d errors during this test", $realtime, error_count);

      if (fail || (tb.chk_prot_err_stat())) begin
         $display("[%t] : *** TEST FAILED ***", $realtime);
      end else begin
         $display("[%t] : *** TEST PASSED ***", $realtime);
      end

      $finish;
   end // initial begin
endmodule // test_bar1

      
         

      
      
      
      