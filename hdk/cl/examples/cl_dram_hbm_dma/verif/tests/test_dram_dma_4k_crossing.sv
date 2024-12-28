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


// DMA 4k crossing test

module test_dram_dma_4k_crossing();

  import tb_type_defines_pkg::*;

  `include "base_test_utils.svh";

  //Lengths are kept same for all 4 channels to start 4k crossing at different points
  int         len0 = 1000;
  int         len1 = 1000;
  int         len2 = 1000;
  int         len3 = 1000;

  initial begin

    tb.power_up(.clk_recipe_a(ClockRecipe::A1),
                .clk_recipe_b(ClockRecipe::B0),
                .clk_recipe_c(ClockRecipe::C0));

    `ifdef AWS_CLKGEN_BASE_REG
      aws_clkgen_dsrt_rst();
    `endif

    initialize_ddr();

    initialize_hbm();

    `ifdef AWS_CLKGEN_BASE_REG
      aws_clkgen_dsrt_rst();
      // Toggle reset per smartconnect IP requirement
      aws_clkgen_asrt_rst();
      tb.wait_clock(100);
      aws_clkgen_dsrt_rst();
    `endif

    deselect_cl_tst_hw();

    $display("[%t] : Initializing DDR buffers", $realtime);
    load_host_memory(.chan(`DDR_CHANNEL), .host_addr(64'h0000), .cl_addr(`DDR_BASE_ADDR + 64'h0F00), .data_pattern(8'hAA), .num_bytes(len0));
    load_host_memory(.chan(`DDR_CHANNEL), .host_addr(64'h3000), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_1 + 64'h1F40), .data_pattern(8'hBB), .num_bytes(len1));
    load_host_memory(.chan(`DDR_CHANNEL), .host_addr(64'h6000), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_2 + 64'h2F80), .data_pattern(8'hCC), .num_bytes(len2));
    load_host_memory(.chan(`DDR_CHANNEL), .host_addr(64'h9000), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_3 + 64'h3FC0), .data_pattern(8'hDD), .num_bytes(len3));

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

    tb.que_cl_to_buffer(.chan(`DDR_CHANNEL), .dst_addr(`DDR_HOST_MEM_BUFFER_ADDR_0), .cl_addr(`DDR_BASE_ADDR + 64'h0F00), .len(len0) );
    tb.que_cl_to_buffer(.chan(`DDR_CHANNEL), .dst_addr(`DDR_HOST_MEM_BUFFER_ADDR_1), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_1 + 64'h1F40), .len(len1) );
    tb.que_cl_to_buffer(.chan(`DDR_CHANNEL), .dst_addr(`DDR_HOST_MEM_BUFFER_ADDR_2), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_2 + 64'h2F80), .len(len2) );
    tb.que_cl_to_buffer(.chan(`DDR_CHANNEL), .dst_addr(`DDR_HOST_MEM_BUFFER_ADDR_3), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_3 + 64'h3FC0), .len(len3) );
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

    check_peek_poke(`DDR_BASE_ADDR + 64'h0F00, 64'h1, DataSize::UINT64);
    check_peek_poke(`DDR_BASE_ADDR + `DDR_LEVEL_1 + 64'h1F40, 64'h1, DataSize::UINT64);
    check_peek_poke(`DDR_BASE_ADDR + `DDR_LEVEL_2 + 64'h2F80, 64'h1, DataSize::UINT64);
    check_peek_poke(`DDR_BASE_ADDR + `DDR_LEVEL_3 + 64'h3FC0, 64'h1, DataSize::UINT64);


    $display("[%t] : Initializing HBM buffers", $realtime);
    load_host_memory(.chan(`HBM_CHANNEL), .host_addr(64'hC000), .cl_addr(`HBM_BASE_ADDR + 64'h0F00), .data_pattern(8'hAB), .num_bytes(len2));
    load_host_memory(.chan(`HBM_CHANNEL), .host_addr(64'hF000), .cl_addr(`HBM_BASE_ADDR + `_8_GB + 64'h1F40), .data_pattern(8'hCD), .num_bytes(len3));

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
    tb.que_cl_to_buffer(.chan(`HBM_CHANNEL), .dst_addr(`HBM_HOST_MEM_BUFFER_ADDR_0), .cl_addr(`HBM_BASE_ADDR + 64'h0F00), .len(len2));
    tb.que_cl_to_buffer(.chan(`HBM_CHANNEL), .dst_addr(`HBM_HOST_MEM_BUFFER_ADDR_1), .cl_addr(`HBM_BASE_ADDR + `_8_GB + 64'h1F40), .len(len3));
    tb.start_que_to_buffer(.chan(`HBM_CHANNEL));

    wait_for_dma_transfer_from_cl_to_buffer(`HBM_CHANNEL);

    #1us;

    $display("[%t] : Comparing DMA buffer from HBM base address with expected pattern", $realtime);
    check_host_memory(.addr(`HBM_HOST_MEM_BUFFER_ADDR_0), .expected_data_pattern(8'hAB), .num_bytes(len2));

    $display("[%t] : Comparing DMA buffer from HBM offset 8 GB with expected pattern", $realtime);
    check_host_memory(.addr(`HBM_HOST_MEM_BUFFER_ADDR_1), .expected_data_pattern(8'hCD), .num_bytes(len3));

    check_peek_poke(`HBM_BASE_ADDR + 64'h0F00, 64'h1, DataSize::UINT64);
    check_peek_poke(`HBM_BASE_ADDR + `_8_GB + 64'h1F40, 64'h1, DataSize::UINT64);


    #500ns;
    tb.power_down();

    report_pass_fail_status();

    $finish;

   end // initial begin
endmodule // test_dram_dma_4k_crossing
