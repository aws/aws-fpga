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

   `include "base_test_utils.svh";

   int len0, len1, len2, len3;

   initial begin

      logic [63:0] host_memory_buffer_address;
      logic [63:0] cl_addr_0, cl_addr_1, cl_addr_2, cl_addr_3;

      tb.power_up(.clk_recipe_a(ClockRecipe::A1),
                  .clk_recipe_b(ClockRecipe::B0),
                  .clk_recipe_c(ClockRecipe::C0));
      `ifdef AWS_CLKGEN_BASE_REG
          aws_clkgen_dsrt_rst();
      `endif
      initialize_ddr();

      initialize_hbm();


      deselect_cl_tst_hw();

      len0 = $urandom_range(8,  64);
      $display("[%t] : Length0 is %d", $realtime, len0);

      len1 = $urandom_range(64, 127);
      $display("[%t] : Length1 is %d", $realtime, len1);

      len2 = $urandom_range(1000, 6000);
      $display("[%t] : Length2 is %d", $realtime, len2);

      len3 = $urandom_range(128, 256);
      $display("[%t] : Length3 is %d", $realtime, len3);

      cl_addr_0 = `DDR_BASE_ADDR + $urandom_range(64'h1d00,  64'h2000);
      cl_addr_0[5:0] = 6'b0;
      $display("[%t] : cl_addr_0 is %x", $realtime, cl_addr_0);

      cl_addr_1 = `DDR_BASE_ADDR + `DDR_LEVEL_1 + $urandom_range(64'h1000,  64'h1064);
      cl_addr_1[5:0] = 6'b0;
      $display("[%t] : cl_addr_1 is %x", $realtime, cl_addr_1);

      cl_addr_2 = `DDR_BASE_ADDR + `DDR_LEVEL_2 + $urandom_range(64'h0010,  64'h0080);
      cl_addr_2[5:0] = 6'b0;
      $display("[%t] : cl_addr_2 is %x", $realtime, cl_addr_2);

      cl_addr_3 = `DDR_BASE_ADDR + `DDR_LEVEL_3 + $urandom_range(64'h0f00,  64'h1000);
      cl_addr_3[5:0] = 6'b0;
      $display("[%t] : cl_addr_3 is %x", $realtime, cl_addr_3);

      $display("[%t] : Initializing DDR buffers", $realtime);
	  load_host_memory(.chan(`DDR_CHANNEL), .host_addr(64'h0000_0000), .cl_addr(cl_addr_0), .data_pattern(8'hAA), .num_bytes(len0));
	  load_host_memory(.chan(`DDR_CHANNEL), .host_addr(64'h0001_0000), .cl_addr(cl_addr_1), .data_pattern(8'hBB), .num_bytes(len1));
	  load_host_memory(.chan(`DDR_CHANNEL), .host_addr(64'h0002_0000), .cl_addr(cl_addr_2), .data_pattern(8'hCC), .num_bytes(len2));
	  load_host_memory(.chan(`DDR_CHANNEL), .host_addr(64'h0003_0000), .cl_addr(cl_addr_3), .data_pattern(8'hDD), .num_bytes(len3));

      $display("[%t] : Starting DDR H2C DMA channels ", $realtime);
      tb.start_que_to_cl(.chan(`DDR_CHANNEL));
	  wait_for_dma_transfer_from_buffer_to_cl(.chan(`DDR_CHANNEL));
      // DMA transfers are posted writes. The above code checks only if the dma transfer is setup and done.
      // We need to wait for writes to finish to memory before issuing reads.
      $display("[%t] : Waiting for DDR DMA write transfers to complete", $realtime);
      #10us;

      $display("[%t] : Transferring DDR data to host buffer", $realtime);
      `define DDR_HOST_MEM_BUFFER_ADDR_0 64'h0_000A_0000
      `define DDR_HOST_MEM_BUFFER_ADDR_1 64'h0_000B_0000
      `define DDR_HOST_MEM_BUFFER_ADDR_2 64'h0_000C_0000
      `define DDR_HOST_MEM_BUFFER_ADDR_3 64'h0_000D_0000

      tb.que_cl_to_buffer(.chan(`DDR_CHANNEL), .dst_addr(`DDR_HOST_MEM_BUFFER_ADDR_0), .cl_addr(cl_addr_0), .len(len0) );
      tb.que_cl_to_buffer(.chan(`DDR_CHANNEL), .dst_addr(`DDR_HOST_MEM_BUFFER_ADDR_1), .cl_addr(cl_addr_1), .len(len1) );
      tb.que_cl_to_buffer(.chan(`DDR_CHANNEL), .dst_addr(`DDR_HOST_MEM_BUFFER_ADDR_2), .cl_addr(cl_addr_2), .len(len2) );
      tb.que_cl_to_buffer(.chan(`DDR_CHANNEL), .dst_addr(`DDR_HOST_MEM_BUFFER_ADDR_3), .cl_addr(cl_addr_3), .len(len3) );
      tb.start_que_to_buffer(.chan(`DDR_CHANNEL));

      wait_for_dma_transfer_from_cl_to_buffer(`DDR_CHANNEL);

      #30us;

      $display("[%t] : Comparing DMA buffer from DDR sequence 0 with expected pattern", $realtime);
      check_host_memory(.addr(`DDR_HOST_MEM_BUFFER_ADDR_0), .expected_data_pattern(8'hAA), .num_bytes(len0));

      $display("[%t] : Comparing DMA buffer from DDR sequence 1 with expected pattern", $realtime);
      check_host_memory(.addr(`DDR_HOST_MEM_BUFFER_ADDR_1), .expected_data_pattern(8'hBB), .num_bytes(len1));

      $display("[%t] : Comparing DMA buffer from DDR sequence 2 with expected pattern", $realtime);
      check_host_memory(.addr(`DDR_HOST_MEM_BUFFER_ADDR_2), .expected_data_pattern(8'hCC), .num_bytes(len2));

      $display("[%t] : Comparing DMA buffer from DDR sequence 3 with expected pattern", $realtime);
      check_host_memory(.addr(`DDR_HOST_MEM_BUFFER_ADDR_3), .expected_data_pattern(8'hDD), .num_bytes(len3));

      $display("[%t] : Initializing HBM buffers", $realtime);
	  load_host_memory(.chan(`HBM_CHANNEL), .host_addr(64'h0004_000), .cl_addr(`HBM_BASE_ADDR + cl_addr_0), .data_pattern(8'hAB), .num_bytes(len2));
	  load_host_memory(.chan(`HBM_CHANNEL), .host_addr(64'h0005_000), .cl_addr(`HBM_BASE_ADDR + `_8_GB + cl_addr_1), .data_pattern(8'hCD), .num_bytes(len3));

      $display("[%t] : Starting HBM H2C DMA channels ", $realtime);
      tb.start_que_to_cl(.chan(`HBM_CHANNEL));
	  wait_for_dma_transfer_from_buffer_to_cl(.chan(`HBM_CHANNEL));
      // DMA transfers are posted writes. The above code checks only if the dma transfer is setup and done.
      // We need to wait for writes to finish to memory before issuing reads.
      $display("[%t] : Waiting for DMA write transfers to complete", $realtime);
      #10us;

      $display("[%t] : Transferring HBM data to host buffer", $realtime);
      `define HBM_HOST_MEM_BUFFER_ADDR_0 64'h0_000E_0000
      `define HBM_HOST_MEM_BUFFER_ADDR_1 64'h0_000F_0000
      tb.que_cl_to_buffer(.chan(`HBM_CHANNEL), .dst_addr(`HBM_HOST_MEM_BUFFER_ADDR_0), .cl_addr(`HBM_BASE_ADDR + cl_addr_0), .len(len2) );
      tb.que_cl_to_buffer(.chan(`HBM_CHANNEL), .dst_addr(`HBM_HOST_MEM_BUFFER_ADDR_1), .cl_addr(`HBM_BASE_ADDR + `_8_GB + cl_addr_1), .len(len3) );
      tb.start_que_to_buffer(.chan(`HBM_CHANNEL));

      wait_for_dma_transfer_from_cl_to_buffer(`HBM_CHANNEL);

      #10us;

      $display("[%t] : Comparing DMA buffer from HBM base address with expected pattern", $realtime);
      check_host_memory(.addr(`HBM_HOST_MEM_BUFFER_ADDR_0), .expected_data_pattern(8'hAB), .num_bytes(len2));

      $display("[%t] : Comparing DMA buffer from HBM offset 8 GB with expected pattern", $realtime);
      check_host_memory(.addr(`HBM_HOST_MEM_BUFFER_ADDR_1), .expected_data_pattern(8'hCD), .num_bytes(len3));


      #500ns;
      tb.power_down();

	  report_pass_fail_status();

      $finish;
   end // initial begin

endmodule // test_dram_dma_rnd
