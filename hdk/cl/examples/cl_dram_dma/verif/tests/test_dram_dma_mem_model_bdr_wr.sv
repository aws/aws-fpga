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
// This test bypasses Micron DDR models and uses AXI memory model.
// Please refer to readme for more information about AXI memoryy model.
// This test backdoor writes and front door reads AXI memory model.

module test_dram_dma_mem_model_bdr_wr();

   import tb_type_defines_pkg::*;

   int error_count;
   int timeout_count;
   int fail;
   logic [3:0] status;

   //transfer1 - length less than 64 byte.
   int         len0 = 17;
   //transfer2 - length between 64 and 256 bytes.
   int         len1 = 128;
   //transfer3 - length greater than 4k bytes.
   int         len2 = 6000;
   //transfer4 - length between 256 and 512 bytes.
   int         len3 = 300;
   logic       ddr_ready;
   logic       rdata;
   
   initial begin

      logic [63:0] host_memory_buffer_address;
      logic [63:0] ddr_A_addr, ddr_B_addr, ddr_C_addr, ddr_D_addr;

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

      
      $display("backdoor load memory to DDR A \n");

      ddr_A_addr = 64'h0;

      // Put test pattern in host memory
      for (int i = 0 ; i < len0 ; i++) begin
         tb.card.fpga.CL.SH_DDR.u_mem_model.bfm_inst[0].u_bfm.axi_mem_bdr_write(.addr(ddr_A_addr), .d(8'hAA));
         ddr_A_addr++;
      end

      $display("backdoor load memory to DDR B \n");

      ddr_B_addr = 64'h0;

      // Put test pattern in host memory
      for (int i = 0 ; i < len0 ; i++) begin
         tb.card.fpga.CL.SH_DDR.u_mem_model.bfm_inst[1].u_bfm.axi_mem_bdr_write(.addr(ddr_B_addr), .d(8'hBB));
         ddr_B_addr++;
      end

      $display("backdoor load memory to DDR C \n");

      ddr_C_addr = 64'h0;

      // Put test pattern in host memory
      for (int i = 0 ; i < len0 ; i++) begin
         tb.card.fpga.sh.u_mem_model.axi_mem_bdr_write(.addr(ddr_C_addr), .d(8'hCC));
         ddr_C_addr++;
      end

      ddr_D_addr = 64'h0;

      // Put test pattern in host memory
      for (int i = 0 ; i < len0 ; i++) begin
         tb.card.fpga.CL.SH_DDR.u_mem_model.bfm_inst[2].u_bfm.axi_mem_bdr_write(.addr(ddr_D_addr), .d(8'hDD));
         ddr_D_addr++;
      end
      
      $display("[%t] : starting C2H DMA channels ", $realtime);

      //read the data from cl and put it in the host memory
      host_memory_buffer_address = 64'h0_0001_0800;
      tb.que_cl_to_buffer(.chan(0), .dst_addr(host_memory_buffer_address), .cl_addr(64'h0000_0000_0000), .len(len0) ); // move DDR0 to buffer

      host_memory_buffer_address = 64'h0_0002_1800;
      tb.que_cl_to_buffer(.chan(1), .dst_addr(host_memory_buffer_address), .cl_addr(64'h0004_0000_0000), .len(len1) ); // move DDR1 to buffer

      host_memory_buffer_address = 64'h0_0003_2800;
      tb.que_cl_to_buffer(.chan(2), .dst_addr(host_memory_buffer_address), .cl_addr(64'h0008_0000_0000), .len(len2) ); // move DDR2 to buffer

      host_memory_buffer_address = 64'h0_0004_3800;
      tb.que_cl_to_buffer(.chan(3), .dst_addr(host_memory_buffer_address), .cl_addr(64'h000C_0000_0000), .len(len3) ); // move DDR3 to buffer
      
      //Start transfers of data from CL DDR
      tb.start_que_to_buffer(.chan(0));
      tb.start_que_to_buffer(.chan(1));
      tb.start_que_to_buffer(.chan(2));
      tb.start_que_to_buffer(.chan(3));

      // wait for dma transfers to complete
      timeout_count = 0;
      do begin
         status[0] = tb.is_dma_to_buffer_done(.chan(0));
         #10ns;
         timeout_count++;
      end while ((status != 4'hf) && (timeout_count < 1000));

      if (timeout_count >= 1000) begin
         $display("[%t] : *** ERROR *** Timeout waiting for dma transfers from cl", $realtime);
         error_count++;
      end

      #1us;

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

      // DDR 2
      // Compare the data in host memory with the expected data
      $display("[%t] : DMA buffer from DDR 2", $realtime);

      host_memory_buffer_address = 64'h0_0003_2800;
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

      host_memory_buffer_address = 64'h0_0004_3800;
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

endmodule // test_dram_dma_mem_model_bdr_wr

