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
// This test frontdoor writes and backdoor reads AXI memory model.

module test_dram_dma_mem_model_bdr_rd();

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

      // allow memory to initialize
      $display("[%t] : Initializing buffers", $realtime);

      host_memory_buffer_address = 64'h0;

      //Queue data to be transfered to CL DDR
      tb.que_buffer_to_cl(.chan(0), .src_addr(host_memory_buffer_address), .cl_addr(64'h0000_0000_1f00), .len(len0) ); // move buffer to DDR 0

      // Put test pattern in host memory
      for (int i = 0 ; i < len0 ; i++) begin
         tb.hm_put_byte(.addr(host_memory_buffer_address), .d(8'hAA));
         host_memory_buffer_address++;
      end

      host_memory_buffer_address = 64'h0_0000_3000;

      tb.que_buffer_to_cl(.chan(1), .src_addr(host_memory_buffer_address), .cl_addr(64'h0004_0000_0000), .len(len1) ); // move buffer to DDR 1

      for (int i = 0 ; i < len1 ; i++) begin
         tb.hm_put_byte(.addr(host_memory_buffer_address), .d(8'hBB));
         host_memory_buffer_address++;
      end

      host_memory_buffer_address = 64'h0_0000_6000;
      tb.que_buffer_to_cl(.chan(2), .src_addr(host_memory_buffer_address), .cl_addr(64'h0008_0000_0000), .len(len2) ); // move buffer to DDR 2

      for (int i = 0 ; i < len2 ; i++) begin
         tb.hm_put_byte(.addr(host_memory_buffer_address), .d(8'hCC));
         host_memory_buffer_address++;
      end

      host_memory_buffer_address = 64'h0_0000_9000;
      tb.que_buffer_to_cl(.chan(3), .src_addr(host_memory_buffer_address), .cl_addr(64'h000C_0000_0000), .len(len3) ); // move buffer to DDR 3

      for (int i = 0 ; i < len3 ; i++) begin
         tb.hm_put_byte(.addr(host_memory_buffer_address), .d(8'hDD));
         host_memory_buffer_address++;
      end

      $display("[%t] : starting H2C DMA channels ", $realtime);

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
      end while ((status != 4'hf) && (timeout_count < 4000));

      if (timeout_count >= 4000) begin
         $display("[%t] : *** ERROR *** Timeout waiting for dma transfers from cl", $realtime);
         error_count++;
      end

      #1us;
      
      $display("backdoor read memory from DDR A \n");

      ddr_A_addr = 64'h0000_0000_1f00;

      // Put test pattern in host memory
      for (int i = 0 ; i < len0 ; i++) begin
         if (tb.card.fpga.CL.SH_DDR.u_mem_model.bfm_inst[0].u_bfm.axi_mem_bdr_read(.addr(ddr_A_addr)) !== 8'hAA) begin
            $display("[%t] : *** ERROR *** DDR0 Data mismatch, addr:%0x read data is: %0x",
                     $realtime, ddr_A_addr, (tb.card.fpga.CL.SH_DDR.u_mem_model.bfm_inst[0].u_bfm.axi_mem_bdr_read(.addr(ddr_A_addr))));
            error_count++;
         end
         ddr_A_addr++;
      end


      $display("backdoor read memory from DDR B \n");

      ddr_B_addr = 64'h0;

      // Put test pattern in host memory
      for (int i = 0 ; i < len1 ; i++) begin
         if (tb.card.fpga.CL.SH_DDR.u_mem_model.bfm_inst[1].u_bfm.axi_mem_bdr_read(.addr(ddr_B_addr)) !== 8'hBB) begin
            $display("[%t] : *** ERROR *** DDR1 Data mismatch, addr:%0x read data is: %0x",
                     $realtime, ddr_B_addr, (tb.card.fpga.CL.SH_DDR.u_mem_model.bfm_inst[1].u_bfm.axi_mem_bdr_read(.addr(ddr_B_addr))));
            error_count++;
         end
         ddr_B_addr++;
      end

      $display("backdoor read memory from DDR C \n");

      ddr_C_addr = 64'h0;

      // Put test pattern in hst memory
      for (int i = 0 ; i < len2 ; i++) begin
         if (tb.card.fpga.sh.u_mem_model.axi_mem_bdr_read(.addr(ddr_C_addr)) !== 8'hCC) begin
            $display("[%t] : *** ERROR *** DDR2 Data mismatch, addr:%0x read data is: %0x",
                     $realtime, ddr_C_addr, (tb.card.fpga.sh.u_mem_model.axi_mem_bdr_read(.addr(ddr_C_addr))));
            error_count++;
         end
         ddr_C_addr++;
      end
      
      $display("backdoor read memory from DDR D \n");

      ddr_D_addr = 64'h0;

      // Put test pattern in host memory
      for (int i = 0 ; i < len3 ; i++) begin
         if (tb.card.fpga.CL.SH_DDR.u_mem_model.bfm_inst[2].u_bfm.axi_mem_bdr_read(.addr(ddr_D_addr)) !== 8'hDD) begin
            $display("[%t] : *** ERROR *** DDR3 Data mismatch, addr:%0x read data is: %0x",
                     $realtime, ddr_D_addr, (tb.card.fpga.CL.SH_DDR.u_mem_model.bfm_inst[2].u_bfm.axi_mem_bdr_read(.addr(ddr_D_addr))));
            error_count++;
         end
         ddr_D_addr++;
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

endmodule // test_dram_dma_mem_model_bdr_rd

