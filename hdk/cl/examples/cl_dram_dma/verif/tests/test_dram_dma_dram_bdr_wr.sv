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


module test_dram_dma_dram_bdr_wr();

   import tb_type_defines_pkg::*;
   
   //transfer1 - length 64bits.
   int         len0 = 64;
   int         fp;

`include "test_dram_dma_bdr_common.svh"
   
   initial begin

      logic [63:0] host_memory_buffer_address;

      logic [63:0] bdr_data;

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

      //Disable ECC
      //Write ECC register address in DRAM controller
      tb.poke_stat(.addr(8'h10), .ddr_idx(0), .data(32'h0000_0008));
      tb.poke_stat(.addr(8'h10), .ddr_idx(1), .data(32'h0000_0008));
      tb.poke_stat(.addr(8'h10), .ddr_idx(2), .data(32'h0000_0008));

      tb.poke_stat(.addr(8'h14), .ddr_idx(0), .data(32'h0000_0000));
      tb.poke_stat(.addr(8'h14), .ddr_idx(1), .data(32'h0000_0000));
      tb.poke_stat(.addr(8'h14), .ddr_idx(2), .data(32'h0000_0000));
      
      host_memory_buffer_address = 64'h0;

      $display("backdoor load memory \n");

      fp = $fopen("ddr4.mem","wa+");

      tb.card.write_cfg_info_to_file(fp);
      tb.card.write_bdr_ld_data_to_file(fp, 64'h0004_0000_0000, 'h22221111);

      $fclose(fp);
      
      tb.card.ddr_bdr_ld("ddr4.mem");
      
      tb.nsec_delay(2000);
      
      $display("[%t] : starting C2H DMA channels ", $realtime);

      dma_c2h_transfers(64'h0004_0000_0000, 1, 64);
      
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

endmodule // test_dram_dma_dram_bdr_wr


