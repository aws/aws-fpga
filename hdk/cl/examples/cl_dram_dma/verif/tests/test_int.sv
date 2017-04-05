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

module test_int();

   import tb_type_defines_pkg::*;
   
   logic [63:0]   base_addr;

   logic [31:0]   write_data;
   logic [31:0]   read_data;

   logic [15:0]   int_pend;

   int            timeout_count;

   int            error_count;
   int            fail;

   initial begin
      error_count = 0;
      fail = 0;

      tb.power_up();

      //---------------------------
      // Program CL registers to trigger interrupts
      //---------------------------

      base_addr = 64'h0000_0000_0000_0d00;

      // Check all combinations of one or two interrupts
      for (logic [7:0] vector_num = 8'h00; vector_num < 8'h10; vector_num = vector_num + 8'h01) begin
         for (logic [7:0] vector_num2 = 8'h00; vector_num2 < 8'h01; vector_num2 = vector_num2 + 8'h01) begin

            if (vector_num !== vector_num2) begin
               $display("[%t] : Programming cl_int_tst to trigger interrupt vectors %2d and %2d", $realtime, vector_num, vector_num2);
            end else begin
               $display("[%t] : Programming cl_int_tst to trigger interrupt vector %2d", $realtime, vector_num);
            end
            write_data = 32'h0;
            write_data |= 1'b1 << vector_num;
            write_data |= 1'b1 << vector_num2;
            int_pend = write_data[15:0];
            tb.poke_ocl(.addr(base_addr + 64'h000), .data(write_data));

            timeout_count = 0;
            do begin
               tb.peek_ocl(.addr(base_addr + 64'h000), .data(read_data));
               if (|read_data[31:16]) begin
                  int_pend &= ~(read_data[31:16]);
                  tb.poke_ocl(.addr(base_addr + 64'h000), .data({read_data[31:16], 16'h0000}));
               end
               timeout_count++;
               if (timeout_count == 100) begin
                  if (vector_num !== vector_num2) begin
                     $display("[%t] : *** ERROR *** Timeout waiting for cl_int_tst Done bits to be set (vectors %2d, %2d).", $realtime, vector_num, vector_num2);
                  end else begin
                     $display("[%t] : *** ERROR *** Timeout waiting for cl_int_tst Done bit to be set (vector %2d).", $realtime, vector_num);
                  end
                  error_count++;
               end
            end while ((int_pend !== 16'h0000) && (timeout_count < 100));

            tb.peek_ocl(.addr(base_addr + 64'h000), .data(read_data));
            if (read_data !== 32'h0000_0000) begin
               if (vector_num !== vector_num2) begin
                  $display("[%t] : *** ERROR *** Done bits were not cleared for vectors %2d, %2d.", $realtime, vector_num, vector_num2);
               end else begin
                  $display("[%t] : *** ERROR *** Done bit was not cleared for vector %2d.", $realtime, vector_num);
               end
               error_count++;
            end
         end
      end

      // Power down
      #500ns;
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

endmodule // test_int
