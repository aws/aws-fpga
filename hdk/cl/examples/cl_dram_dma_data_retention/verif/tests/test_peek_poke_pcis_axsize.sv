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


module test_peek_poke_pcis_axsize();

   import tb_type_defines_pkg::*;

   logic [63:0]  pcis_addr;
   logic [511:0] pcis_wr_data;
   logic [511:0] pcis_rd_data;
   bit   [511:0] pcis_exp_data;
   bit   [511:0] pcis_act_data;

   logic [63:0]  cycle_count;
   logic [63:0]  error_addr;

   logic [3:0]   error_index;
   logic [7:0]   data_array[];

   int           data;
   int           timeout_count;

   int           error_count;
   int           fail;
   
 
   initial begin
      error_count = 0;
      fail = 0;

      tb.power_up();

      tb.nsec_delay(2000);
      tb.poke_stat(.addr(8'h0c), .ddr_idx(0), .data(32'h0000_0000));
      tb.poke_stat(.addr(8'h0c), .ddr_idx(1), .data(32'h0000_0000));
      tb.poke_stat(.addr(8'h0c), .ddr_idx(2), .data(32'h0000_0000));

      pcis_wr_data =0; 
      data =1; 
      for(int size =0; size <=6; size++) begin
          $display("[%t] : Size of peek/poke = %0d", $realtime, size);
          for(int addr =0; addr <=63; addr = addr+(2**size)) begin
             $display("[%t] : Address of peek/poke = %0h", $realtime, addr);
             for (int num_bytes =0; num_bytes < 2**size; num_bytes++) begin
                  pcis_wr_data[(num_bytes*8)+:8] = data;
                  data ++;
             end 
             tb.poke(.addr(addr), .data(pcis_wr_data), .size(DataSize::DATA_SIZE'(size)));
             tb.peek(.addr(addr), .data(pcis_rd_data), .size(DataSize::DATA_SIZE'(size)));
             for (int num_bytes =0; num_bytes < 2**size; num_bytes++) begin           
                 pcis_exp_data[((addr+num_bytes)*8)+:8] = pcis_wr_data[(num_bytes*8)+:8];
                 pcis_act_data[((addr+num_bytes)*8)+:8] = pcis_rd_data[(num_bytes*8)+:8];
             end
          end
          compare_data(.act_data(pcis_act_data), .exp_data(pcis_exp_data));
          $display("[%t] : Clear the memory before next size iteration", $realtime);
          tb.poke(.addr(64'h0), .data(512'h0), .size(DataSize::DATA_SIZE'(3)));
      end
    
      $display("[%t] : Waiting for PCIS write and read activity to complete", $realtime);
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
   end

   task compare_data(logic [511:0] act_data, exp_data);
      if(act_data !== exp_data) begin
         $display($time,,,"***ERROR*** : Data Mismatch. Actual Data:%0h <==> Expected Data: %0h",
                            act_data, exp_data);
         error_count ++;
      end
      else begin
         $display("Data Matched. Actual Data:%0h <==> Expected Data: %0h", act_data, exp_data);
      end
   endtask

   task disp_err (input string s);
      $display($time,,,"***ERROR*** : %s", s);
      error_count ++;
   endtask
endmodule // test_peek_poke_pcis_axsize
