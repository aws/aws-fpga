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

// DMA test with random lengths.

module test_dram_dma_rnd();

   import tb_type_defines_pkg::*;

   int error_count;
   int timeout_count;
   int fail;
   logic [3:0] status;
   int         len0 = 17;
   int         len1 = 17;
   int         len2 = 17;
   int         len3 = 17;
   
   logic       ddr_ready;
   logic       rdata;
   
   initial begin

      logic [63:0] host_memory_buffer_address;
      logic [63:0] cl_addr_0, cl_addr_1, cl_addr_2, cl_addr_3;
      logic [63:0] cl_addr_4, cl_addr_5, cl_addr_6, cl_addr_7;
      
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

      len0 = $urandom_range(8,  64);
      $display("[%t] : Length0 is %d", $realtime, len0);
      
      len1 = $urandom_range(64, 127);
      $display("[%t] : Length1 is %d", $realtime, len1);

      len2 = $urandom_range(1000, 6000);
      $display("[%t] : Length2 is %d", $realtime, len2);
      
      len3 = $urandom_range(128, 256);
      $display("[%t] : Length3 is %d", $realtime, len3);
      
      cl_addr_0 = $urandom_range(64'h1d00,  64'h2000);
      cl_addr_0[5:0] = 6'b0;
      $display("[%t] : cl_addr_0 is %x", $realtime, cl_addr_0);

      cl_addr_1 = 64'h0004_0000_0000 + $urandom_range(64'h1000,  64'h1064);
      cl_addr_1[5:0] = 6'b0;
      $display("[%t] : cl_addr_1 is %x", $realtime, cl_addr_1);

      cl_addr_2 = 64'h0008_0000_0000 + $urandom_range(64'h0010,  64'h0080);
      cl_addr_2[5:0] = 6'b0;
      $display("[%t] : cl_addr_2 is %x", $realtime, cl_addr_2);

      cl_addr_3 = 64'h000C_0000_0000 + $urandom_range(64'h0f00,  64'h1000);
      cl_addr_3[5:0] = 6'b0;
      $display("[%t] : cl_addr_3 is %x", $realtime, cl_addr_3);
      
      host_memory_buffer_address = 64'h0;
      //Queue data to be transfered to CL DDR
      tb.que_buffer_to_cl(.chan(0), .src_addr(host_memory_buffer_address), .cl_addr(cl_addr_0), .len(len0) ); // move buffer to DDR 0

      // Put test pattern in host memory
      for (int i = 0 ; i < len0 ; i++) begin
         tb.hm_put_byte(.addr(host_memory_buffer_address), .d(8'hAA));
         host_memory_buffer_address++;
      end

      host_memory_buffer_address = 64'h0_0001_0000;
      tb.que_buffer_to_cl(.chan(1), .src_addr(host_memory_buffer_address), .cl_addr(cl_addr_1), .len(len1) ); // move buffer to DDR 1

      for (int i = 0 ; i < len1 ; i++) begin
         tb.hm_put_byte(.addr(host_memory_buffer_address), .d(8'hBB));
         host_memory_buffer_address++;
      end

      host_memory_buffer_address = 64'h0_0002_0000;
      tb.que_buffer_to_cl(.chan(2), .src_addr(host_memory_buffer_address), .cl_addr(cl_addr_2), .len(len2) ); // move buffer to DDR 2

      for (int i = 0 ; i < len2 ; i++) begin
         tb.hm_put_byte(.addr(host_memory_buffer_address), .d(8'hCC));
         host_memory_buffer_address++;
      end

      host_memory_buffer_address = 64'h0_0003_0000;
      tb.que_buffer_to_cl(.chan(3), .src_addr(host_memory_buffer_address), .cl_addr(cl_addr_3), .len(len3) ); // move buffer to DDR 3

      for (int i = 0 ; i < len3 ; i++) begin
         tb.hm_put_byte(.addr(host_memory_buffer_address), .d(8'hDD));
         host_memory_buffer_address++;
      end

      //Start transfers of data to CL DDR
      tb.start_que_to_cl(.chan(0));
      tb.start_que_to_cl(.chan(1));
      tb.start_que_to_cl(.chan(2));
      tb.start_que_to_cl(.chan(3));

      // wait for dma transfers to complete
      timeout_count = 0;
      do begin
         status[0] = tb.is_dma_to_cl_done(.chan(0));
         status[1] = tb.is_dma_to_cl_done(.chan(1));
         status[2] = tb.is_dma_to_cl_done(.chan(2));
         status[3] = tb.is_dma_to_cl_done(.chan(3));
         #10ns;
         timeout_count++;
      end while ((status != 4'hf) && (timeout_count < 10000));

      if (timeout_count >= 10000) begin
         $display("[%t] : *** ERROR *** Timeout waiting for dma transfers from cl", $realtime);
         error_count++;
      end
     
      #10us;
      
      $display("[%t] : starting C2H DMA channels ", $realtime);

      // read the data from cl and put it in the host memory
      host_memory_buffer_address = 64'h0_000A_0000;
      tb.que_cl_to_buffer(.chan(0), .dst_addr(host_memory_buffer_address), .cl_addr(cl_addr_0), .len(len0) ); // move DDR0 to buffer

      host_memory_buffer_address = 64'h0_000B_0000;
      tb.que_cl_to_buffer(.chan(1), .dst_addr(host_memory_buffer_address), .cl_addr(cl_addr_1), .len(len1) ); // move DDR1 to buffer

      host_memory_buffer_address = 64'h0_000C_0000;
      tb.que_cl_to_buffer(.chan(2), .dst_addr(host_memory_buffer_address), .cl_addr(cl_addr_2), .len(len2) ); // move DDR2 to buffer

      host_memory_buffer_address = 64'h0_000D_0000;
      tb.que_cl_to_buffer(.chan(3), .dst_addr(host_memory_buffer_address), .cl_addr(cl_addr_3), .len(len3) ); // move DDR3 to buffer

      //Start transfers of data from CL DDR
      tb.start_que_to_buffer(.chan(0));
      tb.start_que_to_buffer(.chan(1));
      tb.start_que_to_buffer(.chan(2));
      tb.start_que_to_buffer(.chan(3));

      // wait for dma transfers to complete
      timeout_count = 0;
      do begin
         status[0] = tb.is_dma_to_buffer_done(.chan(0));
         status[1] = tb.is_dma_to_buffer_done(.chan(1));
         status[2] = tb.is_dma_to_buffer_done(.chan(2));
         status[3] = tb.is_dma_to_buffer_done(.chan(3));
         #10ns;
         timeout_count++;
      end while ((status != 4'hf) && (timeout_count < 10000));

      if (timeout_count >= 10000) begin
         $display("[%t] : *** ERROR *** Timeout waiting for dma transfers from cl", $realtime);
         error_count++;
      end

      #30us;

      // DDR 0
      // Compare the data in host memory with the expected data
      $display("[%t] : DMA buffer from DDR 0", $realtime);

      host_memory_buffer_address = 64'h0_000A_0000;
      for (int i = 0 ; i<len0 ; i++) begin
         if (tb.hm_get_byte(.addr(host_memory_buffer_address + i)) !== 8'hAA) begin
            $display("[%t] : *** ERROR *** DDR0 Data mismatch, addr:%0x read data is: %0x",
                     $realtime, (host_memory_buffer_address + i), tb.hm_get_byte(.addr(host_memory_buffer_address + i)));
            error_count++;
         end
      end

      // DDR 1
      // Compare the data in host memory with the expected data
      $display("[%t] : DMA buffer from DDR 1", $realtime);

      host_memory_buffer_address = 64'h0_000B_0000;
      for (int i = 0 ; i< len1 ; i++) begin
         if (tb.hm_get_byte(.addr(host_memory_buffer_address)) !== 8'hBB) begin
            $display("[%t] : *** ERROR *** DDR1 Data mismatch, addr:%0x read data is: %0x",
                     $realtime, (host_memory_buffer_address + i), tb.hm_get_byte(.addr(host_memory_buffer_address + i)));
            error_count++;
         end
      end

      // DDR 2
      // Compare the data in host memory with the expected data
      $display("[%t] : DMA buffer from DDR 2", $realtime);

      host_memory_buffer_address = 64'h0_000C_0000;
      for (int i = 0 ; i< len2 ; i++) begin
         if (tb.hm_get_byte(.addr(host_memory_buffer_address)) !== 8'hCC) begin
            $display("[%t] : *** ERROR *** DDR2 Data mismatch, addr:%0x read data is: %0x",
                     $realtime, (host_memory_buffer_address + i), tb.hm_get_byte(.addr(host_memory_buffer_address + i)));
            error_count++;
         end
      end

      // DDR 3
      // Compare the data in host memory with the expected data
      $display("[%t] : DMA buffer from DDR 3", $realtime);

      host_memory_buffer_address = 64'h0_000D_0000;
      for (int i = 0 ; i< len3 ; i++) begin
         if (tb.hm_get_byte(.addr(host_memory_buffer_address)) !== 8'hDD) begin
            $display("[%t] : *** ERROR *** DDR3 Data mismatch, addr:%0x read data is: %0x",
                     $realtime, (host_memory_buffer_address + i), tb.hm_get_byte(.addr(host_memory_buffer_address + i)));
            error_count++;
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

      if (fail || (tb.chk_prot_err_stat())) begin
         $display("[%t] : *** TEST FAILED ***", $realtime);
      end else begin
         $display("[%t] : *** TEST PASSED ***", $realtime);
      end

      $finish;
   end // initial begin

endmodule // test_dram_dma_rnd
