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

`define CFG_REG           64'h00
`define CNTL_REG          64'h08
`define NUM_INST          64'h10
`define MAX_RD_REQ        64'h14

`define WR_INSTR_INDEX    64'h1c
`define WR_ADDR_LOW       64'h20
`define WR_ADDR_HIGH      64'h24
`define WR_DATA           64'h28
`define WR_LEN            64'h2c

`define RD_INSTR_INDEX    64'h3c
`define RD_ADDR_LOW       64'h40
`define RD_ADDR_HIGH      64'h44
`define RD_DATA           64'h48
`define RD_LEN            64'h4c

`define RD_ERR            64'hb0
`define RD_ERR_ADDR_LOW   64'hb4
`define RD_ERR_ADDR_HIGH  64'hb8
`define RD_ERR_INDEX      64'hbc

`define WR_CYCLE_CNT_LOW  64'hf0
`define WR_CYCLE_CNT_HIGH 64'hf4
`define RD_CYCLE_CNT_LOW  64'hf8
`define RD_CYCLE_CNT_HIGH 64'hfc

`define WR_START_BIT   32'h00000001
`define RD_START_BIT   32'h00000002

   import tb_type_defines_pkg::*;   
   logic [31:0] pcis_wr_data [$];
   logic [511:0] pcis_rd_data;
   logic [511:0] pcis_exp_data;
   logic [511:0] pcis_act_data;
   
   logic [63:0]  cycle_count;
   logic [63:0]  error_addr;

   logic [3:0]   error_index;
   logic [7:0]   data_array[];

   int           data;
   int           timeout_count;

   int           error_count;
   int           fail;
   int           size;
   int           dw_cnt;
   logic [31:0]  addr;
   
   initial begin
      error_count = 0;
      fail = 0;

      tb.power_up();

      tb.nsec_delay(2000);
      tb.poke_stat(.addr(8'h0c), .ddr_idx(0), .data(32'h0000_0000));
      tb.poke_stat(.addr(8'h0c), .ddr_idx(1), .data(32'h0000_0000));
      tb.poke_stat(.addr(8'h0c), .ddr_idx(2), .data(32'h0000_0000));

      size = 6;

      addr = 'h0;
      
      for (int cnt=0; cnt <4; cnt++) begin
         dw_cnt = $urandom_range(4, 10);

         addr = addr + 'h04;
         
         tb.nsec_delay(1000);
         
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
         
         compare_data(.act_data(pcis_act_data), .exp_data(pcis_exp_data));

         #500ns;
      end // for (int cnt=0; cnt <4; cnt++)
      
      tb.power_down();
      
      //---------------------------
      // Report pass/fail status
      //---------------------------
      $display("[%t] : Checking total error count...", $realtime);
      if (error_count > 0) begin
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

   task compare_data(logic [511:0] act_data, exp_data);
      if(act_data !== exp_data) begin
         $display($time,,,"***ERROR*** : Data Mismatch. Actual Data:%0h <==> Expected Data: %0h",
                            act_data, exp_data);
         error_count ++;
      end
      else begin
         $display("Data Matched. Actual Data:%0h <==> Expected Data: %0h", act_data, exp_data);
      end
   endtask // compare_data
   
   task disp_err (input string s);
      $display($time,,,"***ERROR*** : %s", s);
      error_count ++;
   endtask // disp_err
   
endmodule // test_peek_poke_wc


      

      
         

         
