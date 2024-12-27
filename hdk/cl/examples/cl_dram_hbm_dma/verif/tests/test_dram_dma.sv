// ============================================================================
// Amazon FPGA Hardware Development Kit
//
// Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
// ============================================================================


module test_dram_dma();

   import tb_type_defines_pkg::*;

   `include "base_test_utils.svh";

   //transfer1 - length less than 64 byte.
   int         len0 = 8;
   //transfer2 - length between 64 and 256 bytes.
   int         len1 = 128;
   //transfer3 - length greater than 4k bytes.
   int         len2 = 6000;
   //transfer4 - length between 256 and 512 bytes.
   int         len3 = 300;

   initial begin

      tb.power_up(.clk_recipe_a(ClockRecipe::A1),
                  .clk_recipe_b(ClockRecipe::B0),
                  .clk_recipe_c(ClockRecipe::C0));
      `ifdef AWS_CLKGEN_BASE_REG
          aws_clkgen_dsrt_rst();
      `endif
      initialize_ddr();

      initialize_hbm();


      deselect_cl_tst_hw();

      $display("[%t] : Initializing DDR buffers", $realtime);
	  load_host_memory(.chan(`DDR_CHANNEL), .host_addr(64'h0000), .cl_addr(`DDR_BASE_ADDR), .data_pattern(8'hAA), .num_bytes(len0));
	  load_host_memory(.chan(`DDR_CHANNEL), .host_addr(64'h3000), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_1), .data_pattern(8'hBB), .num_bytes(len1));
	  load_host_memory(.chan(`DDR_CHANNEL), .host_addr(64'h6000), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_2), .data_pattern(8'hCC), .num_bytes(len2));
	  load_host_memory(.chan(`DDR_CHANNEL), .host_addr(64'h9000), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_3), .data_pattern(8'hDD), .num_bytes(len3));

      $display("[%t] : Starting DDR H2C DMA channels ", $realtime);
      tb.start_que_to_cl(.chan(`DDR_CHANNEL));
	  wait_for_dma_transfer_from_buffer_to_cl(.chan(`DDR_CHANNEL));
      // DMA transfers are posted writes. The above code checks only if the dma transfer is setup and done.
      // We need to wait for writes to finish to memory before issuing reads.
      $display("[%t] : Waiting for DDR DMA write transfers to complete", $realtime);
      #2us;

      $display("[%t] : Transferring DDR data to host buffer", $realtime);
      `define DDR_HOST_MEM_BUFFER_ADDR_0 64'h0_0001_0800
      `define DDR_HOST_MEM_BUFFER_ADDR_1 64'h0_0002_1800
      `define DDR_HOST_MEM_BUFFER_ADDR_2 64'h0_0003_2800
      `define DDR_HOST_MEM_BUFFER_ADDR_3 64'h0_0004_3800

      tb.que_cl_to_buffer(.chan(`DDR_CHANNEL), .dst_addr(`DDR_HOST_MEM_BUFFER_ADDR_0), .cl_addr(`DDR_BASE_ADDR), .len(len0));
      tb.que_cl_to_buffer(.chan(`DDR_CHANNEL), .dst_addr(`DDR_HOST_MEM_BUFFER_ADDR_1), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_1), .len(len1));
      tb.que_cl_to_buffer(.chan(`DDR_CHANNEL), .dst_addr(`DDR_HOST_MEM_BUFFER_ADDR_2), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_2), .len(len2));
      tb.que_cl_to_buffer(.chan(`DDR_CHANNEL), .dst_addr(`DDR_HOST_MEM_BUFFER_ADDR_3), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_3), .len(len3));
      tb.start_que_to_buffer(.chan(`DDR_CHANNEL));

      wait_for_dma_transfer_from_cl_to_buffer(`DDR_CHANNEL);

      #1us;

      $display("[%t] : Comparing DMA buffer from DDR sequence 0 with expected pattern", $realtime);
      check_host_memory(.addr(`DDR_HOST_MEM_BUFFER_ADDR_0), .expected_data_pattern(8'hAA), .num_bytes(len0));

      $display("[%t] : Comparing DMA buffer from DDR sequence 1 with expected pattern", $realtime);
      check_host_memory(.addr(`DDR_HOST_MEM_BUFFER_ADDR_1), .expected_data_pattern(8'hBB), .num_bytes(len1));

      $display("[%t] : Comparing DMA buffer from DDR sequence 2 with expected pattern", $realtime);
      check_host_memory(.addr(`DDR_HOST_MEM_BUFFER_ADDR_2), .expected_data_pattern(8'hCC), .num_bytes(len2));

      $display("[%t] : Comparing DMA buffer from DDR sequence 3 with expected pattern", $realtime);
      check_host_memory(.addr(`DDR_HOST_MEM_BUFFER_ADDR_3), .expected_data_pattern(8'hDD), .num_bytes(len3));

      check_peek_poke(`DDR_BASE_ADDR, 64'h1, DataSize::UINT64);
      check_peek_poke(`DDR_BASE_ADDR + `DDR_LEVEL_1, 64'h1, DataSize::UINT64);
      check_peek_poke(`DDR_BASE_ADDR + `DDR_LEVEL_2, 64'h1, DataSize::UINT64);
      check_peek_poke(`DDR_BASE_ADDR + `DDR_LEVEL_3, 64'h1, DataSize::UINT64);


      $display("[%t] : Initializing HBM buffers", $realtime);
	  load_host_memory(.chan(`HBM_CHANNEL), .host_addr(64'hC000), .cl_addr(`HBM_BASE_ADDR), .data_pattern(8'hAB), .num_bytes(len2));
	  load_host_memory(.chan(`HBM_CHANNEL), .host_addr(64'hF000), .cl_addr(`HBM_BASE_ADDR + `_8_GB), .data_pattern(8'hCD), .num_bytes(len3));

      $display("[%t] : Starting HBM H2C DMA channels ", $realtime);
      tb.start_que_to_cl(.chan(`HBM_CHANNEL));
	  wait_for_dma_transfer_from_buffer_to_cl(.chan(`HBM_CHANNEL));
      // DMA transfers are posted writes. The above code checks only if the dma transfer is setup and done.
      // We need to wait for writes to finish to memory before issuing reads.
      $display("[%t] : Waiting for DMA write transfers to complete", $realtime);
      #2us;

      $display("[%t] : Transferring HBM data to host buffer", $realtime);
      `define HBM_HOST_MEM_BUFFER_ADDR_0 64'h0_0005_4800
      `define HBM_HOST_MEM_BUFFER_ADDR_1 64'h0_0006_5800
      tb.que_cl_to_buffer(.chan(`HBM_CHANNEL), .dst_addr(`HBM_HOST_MEM_BUFFER_ADDR_0), .cl_addr(`HBM_BASE_ADDR), .len(len2));
      tb.que_cl_to_buffer(.chan(`HBM_CHANNEL), .dst_addr(`HBM_HOST_MEM_BUFFER_ADDR_1), .cl_addr(`HBM_BASE_ADDR + `_8_GB), .len(len3));
      tb.start_que_to_buffer(.chan(`HBM_CHANNEL));

      wait_for_dma_transfer_from_cl_to_buffer(`HBM_CHANNEL);

      #1us;

      $display("[%t] : Comparing DMA buffer from HBM base address with expected pattern", $realtime);
      check_host_memory(.addr(`HBM_HOST_MEM_BUFFER_ADDR_0), .expected_data_pattern(8'hAB), .num_bytes(len2));

      $display("[%t] : Comparing DMA buffer from HBM offset 8 GB with expected pattern", $realtime);
      check_host_memory(.addr(`HBM_HOST_MEM_BUFFER_ADDR_1), .expected_data_pattern(8'hCD), .num_bytes(len3));

	  check_peek_poke(`HBM_BASE_ADDR, 64'h1, DataSize::UINT64);
      check_peek_poke(`HBM_BASE_ADDR + `_8_GB, 64'h1, DataSize::UINT64);


      #500ns;
      tb.power_down();

	  report_pass_fail_status();

      $finish;
   end // initial begin

endmodule // test_dram_dma
