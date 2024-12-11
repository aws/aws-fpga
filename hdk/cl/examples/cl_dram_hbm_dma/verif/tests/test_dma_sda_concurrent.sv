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

// This test runs DMA and SDA tests in parallel

module test_dma_sda_concurrent();
   
   import tb_type_defines_pkg::*;

   `include "base_test_utils.svh";

   int         len0 = 17;

   logic [63:0]  sda_addr;
   logic [31:0]  sda_data;

   logic [31:0]  read_data;
   int timeout_count;

   initial begin

      tb.power_up(.clk_recipe_a(ClockRecipe::A1),
                  .clk_recipe_b(ClockRecipe::B0),
                  .clk_recipe_c(ClockRecipe::C0));
	  initialize_ddr();      
        
      fork begin
	     $display("[%t] : Initializing DDR buffers", $realtime); 
	     load_host_memory(.chan(`DDR_CHANNEL), .host_addr(64'h0000), .cl_addr(`DDR_BASE_ADDR), .data_pattern(8'hAA), .num_bytes(len0));
	               
		 $display("[%t] : Starting DDR H2C DMA channels ", $realtime);
		 tb.start_que_to_cl(.chan(`DDR_CHANNEL));
	     wait_for_dma_transfer_from_buffer_to_cl(.chan(`DDR_CHANNEL));
	     // DMA transfers are posted writes. The above code checks only if the dma transfer is setup and done. 
		 // We need to wait for writes to finish to memory before issuing reads.
		 $display("[%t] : Waiting for DDR DMA write transfers to complete", $realtime);
		 #2us;

         $display("[%t] : Transferring DDR data to host buffer", $realtime);    
         `define DDR_HOST_MEM_BUFFER_ADDR_0 64'h0_0001_0800
         tb.que_cl_to_buffer(.chan(`DDR_CHANNEL), .dst_addr(`DDR_HOST_MEM_BUFFER_ADDR_0), .cl_addr(`DDR_BASE_ADDR), .len(len0) );
         tb.start_que_to_buffer(.chan(`DDR_CHANNEL));

         wait_for_dma_transfer_from_cl_to_buffer(`DDR_CHANNEL);

         #1us;

         $display("[%t] : Comparing DMA buffer from DDR sequence 0 with expected pattern", $realtime);
         check_host_memory(.addr(`DDR_HOST_MEM_BUFFER_ADDR_0), .expected_data_pattern(8'hAA), .num_bytes(len0));
      end // fork begin
      begin   
         #100ns;
         //SDA test
         sda_addr  = 'h0;
         for (int i=0; i<32; i=i+4) begin
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
            
            timeout_count = 0;

            $display("[%t] : Waiting for SDA write and read activity to complete", $realtime);
         end // for (int i=0; i<32; i=i+4)
         #1us;
      end
      join      

      #500ns;
      tb.power_down();

      report_pass_fail_status();

      $finish;
   end // initial begin
endmodule // test_dma_sda_concurrent
