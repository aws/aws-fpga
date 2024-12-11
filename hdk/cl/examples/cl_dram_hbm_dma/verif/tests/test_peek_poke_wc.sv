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
// This test is test multi DW pokes to CL. The poke_pcis_wc is a function that tests 
// write combine feature. Test does pokes with multiple DWs and reads the data back 
// and checks.

module test_peek_poke_wc();

   import tb_type_defines_pkg::*;   
	
   `include "base_test_utils.svh"
	
   logic [31:0] pcis_wr_data [$];
   logic [511:0] pcis_rd_data;
   logic [511:0] pcis_exp_data;
   logic [511:0] pcis_act_data;
   
   int           size;
   int           dw_cnt;
   logic [31:0]  addr;
   
   initial begin

	  tb.power_up();
	  initialize_ddr();

      size = 6;
      addr = 'h0;
      
      for (int cnt=0; cnt <4; cnt++) begin
         dw_cnt = $urandom_range(4, 10);
         addr = addr + 'h04;
                  
         $display("[%t] : Address of peek/poke = %0h", $realtime, addr);
         
         for (int num_dw =0; num_dw < dw_cnt; num_dw++) begin
            pcis_wr_data[num_dw] = $urandom();
            pcis_exp_data[(num_dw*32)+:32] = pcis_wr_data[num_dw];
         end
         
         tb.poke_pcis_wc(.addr(addr), .data(pcis_wr_data), .size(DataSize::DATA_SIZE'(size)));

         tb.peek(.addr(addr), .data(pcis_rd_data), .size(DataSize::DATA_SIZE'(size)));

         for (int num_dw =0; num_dw < dw_cnt; num_dw++) begin           
            pcis_act_data[(num_dw*32)+:32] = pcis_rd_data[(num_dw*32)+:32];
         end
         
         compare_data(.act_data(pcis_act_data), .exp_data(pcis_exp_data), .addr(addr));
         
         tb.nsec_delay(1000);
      end // for (int cnt=0; cnt <4; cnt++)
      
      tb.power_down();
      
      report_pass_fail_status();

      $finish;
   end // initial begin
endmodule // test_peek_poke_wc


      

      
         

         
