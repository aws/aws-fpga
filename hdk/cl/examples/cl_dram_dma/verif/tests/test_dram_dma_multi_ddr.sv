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


module test_dram_dma_multi_ddr();

   import tb_type_defines_pkg::*;

   int error_count;
   int timeout_count;
   int fail;
   logic [3:0] status;
   int         len0 = 64;
   int         len1 = 128;
   int         len2 = 6000;
   int         len3 = 300;
   logic       ddr_ready;
   logic       rdata;
   
   initial begin

      logic [63:0] host_memory_buffer_address;


      tb.power_up(.clk_recipe_a(ClockRecipe::A1),
                  .clk_recipe_b(ClockRecipe::B0),
                  .clk_recipe_c(ClockRecipe::C0));

      tb.nsec_delay(1000);
      tb.poke_stat(.addr(8'h0c), .ddr_idx(0), .data(32'h0000_0000));
      tb.poke_stat(.addr(8'h0c), .ddr_idx(1), .data(32'h0000_0000));
      tb.poke_stat(.addr(8'h0c), .ddr_idx(2), .data(32'h0000_0000));

      // de-select the ATG hardware

      tb.poke_ocl(.addr(64'h130), .data(0));
      tb.poke_ocl(.addr(64'h230), .data(0));
      tb.poke_ocl(.addr(64'h330), .data(0));
      tb.poke_ocl(.addr(64'h430), .data(0));

      // allow memory to initialize
      tb.nsec_delay(27000);

      $display("[%t] : Initializing buffers", $realtime);
 
`ifndef DDR_A_ABSENT     
      host_memory_buffer_address = 64'h0;
      //Queue data to be transfered to CL DDR
      tb.que_buffer_to_cl(.chan(0), .src_addr(host_memory_buffer_address), .cl_addr(64'h0000_0000_0002), .len(len0) ); // move buffer to DDR 0

      // Put test pattern in host memory
      for (int i = 0 ; i < len0 ; i++) begin
         tb.hm_put_byte(.addr(host_memory_buffer_address), .d(8'hAA));
         host_memory_buffer_address++;
      end
`endif

`ifndef DDR_B_ABSENT      
      
      host_memory_buffer_address = 64'h0_0000_3000;

      tb.que_buffer_to_cl(.chan(1), .src_addr(host_memory_buffer_address), .cl_addr(64'h0004_0000_0000), .len(len1) ); // move buffer to DDR 1

      for (int i = 0 ; i < len1 ; i++) begin
         tb.hm_put_byte(.addr(host_memory_buffer_address), .d(8'hBB));
         host_memory_buffer_address++;
      end
`endif

`ifndef DDR_D_ABSENT      
      host_memory_buffer_address = 64'h0_0000_9000;
      tb.que_buffer_to_cl(.chan(3), .src_addr(host_memory_buffer_address), .cl_addr(64'h000C_0000_0000), .len(len3) ); // move buffer to DDR 3

      for (int i = 0 ; i < len3 ; i++) begin
         tb.hm_put_byte(.addr(host_memory_buffer_address), .d(8'hDD));
         host_memory_buffer_address++;
      end
`endif
      $display("[%t] : starting H2C DMA channels ", $realtime);

      //Start transfers of data to CL DDR
`ifndef DDR_A_ABSENT      
      tb.start_que_to_cl(.chan(0));
`endif
`ifndef DDR_B_ABSENT      
      tb.start_que_to_cl(.chan(1));
`endif
`ifndef DDR_D_PRESENT      
      tb.start_que_to_cl(.chan(3));
`endif
      
      // wait for dma transfers to complete
      timeout_count = 0;
      do begin
`ifndef DDR_A_ABSENT          
         status[0] = tb.is_dma_to_cl_done(.chan(0));
`endif
`ifndef DDR_B_ABSENT         
         status[1] = tb.is_dma_to_cl_done(.chan(1));
`endif
`ifndef DDR_D_ABSENT         
         status[3] = tb.is_dma_to_cl_done(.chan(3));
`endif
         #10ns;
         timeout_count++;
      end while ((status != 4'hf) && (timeout_count < 4000));

      if (timeout_count >= 4000) begin
         $display("[%t] : *** ERROR *** Timeout waiting for dma transfers from cl", $realtime);
         error_count++;
      end

      $display("[%t] : starting C2H DMA channels ", $realtime);

      // read the data from cl and put it in the host memory
`ifndef DDR_A_ABSENT      
      host_memory_buffer_address = 64'h0_0001_0800;
      tb.que_cl_to_buffer(.chan(0), .dst_addr(host_memory_buffer_address), .cl_addr(64'h0000_0000_0002), .len(len0) ); // move DDR0 to buffer
`endif      

`ifndef DDR_B_ABSENT      
      host_memory_buffer_address = 64'h0_0002_1800;
      tb.que_cl_to_buffer(.chan(1), .dst_addr(host_memory_buffer_address), .cl_addr(64'h0004_0000_0000), .len(len1) ); // move DDR1 to buffer
`endif

`ifndef DDR_D_ABSENT      
      host_memory_buffer_address = 64'h0_0004_3800;
      tb.que_cl_to_buffer(.chan(3), .dst_addr(host_memory_buffer_address), .cl_addr(64'h000C_0000_0000), .len(len3) ); // move DDR3 to buffer
`endif
      
      //Start transfers of data from CL DDR
`ifndef DDR_A_ABSENT      
      tb.start_que_to_buffer(.chan(0));
`endif
`ifndef DDR_B_ABSENT      
      tb.start_que_to_buffer(.chan(1));
`endif
`ifndef DDR_D_ABSENT      
      tb.start_que_to_buffer(.chan(3));
`endif
      
      // wait for dma transfers to complete
      timeout_count = 0;
      do begin
`ifndef DDR_A_ABSENT         
         status[0] = tb.is_dma_to_buffer_done(.chan(0));
`endif
`ifndef DDR_B_ABSENT         
         status[1] = tb.is_dma_to_buffer_done(.chan(1));
`endif
`ifndef DDR_D_ABSENT         
         status[3] = tb.is_dma_to_buffer_done(.chan(3));
`endif         
         #10ns;
         timeout_count++;
      end while ((status != 4'hf) && (timeout_count < 1000));

      if (timeout_count >= 1000) begin
         $display("[%t] : *** ERROR *** Timeout waiting for dma transfers from cl", $realtime);
         error_count++;
      end

      #1us;

`ifndef DDR_A_ABSENT
      // DDR 0
      // Compare the data in host memory with the expected data
      $display("[%t] : DMA buffer from DDR 0", $realtime);

      host_memory_buffer_address = 64'h0_0001_0800;
      for (int i = 0 ; i<len0 ; i++) begin
         if (tb.hm_get_byte(.addr(host_memory_buffer_address + i)) !== 8'hAA) begin
            $display("[%t] : *** ERROR *** DDR0 Data mismatch, addr:%0x read data is: %0x",
                     $realtime, (host_memory_buffer_address + i), tb.hm_get_byte(.addr(host_memory_buffer_address + i)));
            error_count++;
         end
      end
`endif //  `ifndef DDR_A_ABSENT

`ifndef DDR_B_ABSENT      
      // DDR 1
      // Compare the data in host memory with the expected data
      $display("[%t] : DMA buffer from DDR 1", $realtime);

      host_memory_buffer_address = 64'h0_0002_1800;
      for (int i = 0 ; i< len1 ; i++) begin
         if (tb.hm_get_byte(.addr(host_memory_buffer_address)) !== 8'hBB) begin
            $display("[%t] : *** ERROR *** DDR1 Data mismatch, addr:%0x read data is: %0x",
                     $realtime, (host_memory_buffer_address + i), tb.hm_get_byte(.addr(host_memory_buffer_address + i)));
            error_count++;
         end
      end
`endif //  `ifndef DDR_B_ABSENT

`ifndef DDR_D_ABSENT      
      // DDR 3
      // Compare the data in host memory with the expected data
      $display("[%t] : DMA buffer from DDR 3", $realtime);

      host_memory_buffer_address = 64'h0_0004_3800;
      for (int i = 0 ; i< len3 ; i++) begin
         if (tb.hm_get_byte(.addr(host_memory_buffer_address)) !== 8'hDD) begin
            $display("[%t] : *** ERROR *** DDR3 Data mismatch, addr:%0x read data is: %0x",
                     $realtime, (host_memory_buffer_address + i), tb.hm_get_byte(.addr(host_memory_buffer_address + i)));
            error_count++;
         end
      end
`endif
      
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

      if (fail || (tb.chk_prot_err_stat())) begin
         $display("[%t] : *** TEST FAILED ***", $realtime);
      end else begin
         $display("[%t] : *** TEST PASSED ***", $realtime);
      end

      $finish;
   end // initial begin

endmodule // test_dram_dma