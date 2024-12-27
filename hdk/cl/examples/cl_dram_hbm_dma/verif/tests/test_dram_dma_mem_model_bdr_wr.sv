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


// This test bypasses Micron DDR models and uses AXI memory model.
// Please refer to readme for more information about AXI memoryy model.
// This test backdoor writes and front door reads AXI memory model.

module test_dram_dma_mem_model_bdr_wr();

   import tb_type_defines_pkg::*;

   `include "base_test_utils.svh";

   //transfer1 - length less than 64 byte.
   int         len0 = 17;
   //transfer2 - length between 64 and 256 bytes.
   int         len1 = 128;
   //transfer3 - length greater than 4k bytes.
   int         len2 = 6000;
   //transfer4 - length between 256 and 512 bytes.
   int         len3 = 300;

   initial begin
      logic [63:0] ddr_addr_0, ddr_addr_1, ddr_addr_2, ddr_addr_3;

	  tb.power_up(.clk_recipe_a(ClockRecipe::A1),
                  .clk_recipe_b(ClockRecipe::B0),
                  .clk_recipe_c(ClockRecipe::C0));
	  initialize_ddr();
      deselect_cl_tst_hw();

	  #10000ns;

      $display("[%t] Back door load memory to DDR Base Address \n", $realtime);
      ddr_addr_0 = `DDR_BASE_ADDR;
      for (int i = 0 ; i < len0 ; i++) begin
         $display("[%t]:[%d] back door load memory model to DDR Base Address mapped address: addr %h data 8'hAA. \n", $realtime, i,ddr_addr_0);
	 tb.card.fpga.CL.SH_DDR.u_mem_model.axi_mem_bdr_write(.addr(ddr_addr_0), .d(8'hAA));
         ddr_addr_0++;
      end

      $display("[%t] Back door load memory to DDR Offset 8 GB \n", $realtime);
      ddr_addr_1 = `DDR_BASE_ADDR + `DDR_LEVEL_1;
      for (int i = 0 ; i < len0 ; i++) begin
         $display("[%t]:[%d] back door load memory model to DDR Offset 8 GB mapped address: addr %h data 8'hBB. \n", $realtime, i,ddr_addr_1);
	 tb.card.fpga.CL.SH_DDR.u_mem_model.axi_mem_bdr_write(.addr(ddr_addr_1), .d(8'hBB));
         ddr_addr_1++;
      end

      $display("[%t] Back door load memory to DDR Offset 16 GB \n", $realtime);
      ddr_addr_2 = `DDR_BASE_ADDR + `DDR_LEVEL_2;
      for (int i = 0 ; i < len0 ; i++) begin
         $display("[%t]:[%d] back door load memory model to DDR Offset 16 GB mapped address: addr %h data 8'hCC. \n", $realtime, i,ddr_addr_2);
	 tb.card.fpga.CL.SH_DDR.u_mem_model.axi_mem_bdr_write(.addr(ddr_addr_2), .d(8'hCC));
         ddr_addr_2++;
      end

      $display("[%t] Back door load memory to DDR Offset 24 GB \n", $realtime);
      ddr_addr_3 = `DDR_BASE_ADDR + `DDR_LEVEL_3;
      for (int i = 0 ; i < len0 ; i++) begin
         $display("[%t]:[%d] back door load memory model to DDR Offset 24 GB mapped address: addr %h data 8'hDD. \n", $realtime, i,ddr_addr_3);
         tb.card.fpga.CL.SH_DDR.u_mem_model.axi_mem_bdr_write(.addr(ddr_addr_3), .d(8'hDD));
         ddr_addr_3++;
      end

      $display("[%t] : starting C2H DMA channels ", $realtime);
      `define DDR_HOST_MEM_BUFFER_ADDR_0 64'h0_0001_0800
      `define DDR_HOST_MEM_BUFFER_ADDR_1 64'h0_0002_1800
      `define DDR_HOST_MEM_BUFFER_ADDR_2 64'h0_0003_2800
      `define DDR_HOST_MEM_BUFFER_ADDR_3 64'h0_0004_3800

      tb.que_cl_to_buffer(.chan(`DDR_CHANNEL), .dst_addr(`DDR_HOST_MEM_BUFFER_ADDR_0), .cl_addr(`DDR_BASE_ADDR), .len(len0));
      tb.que_cl_to_buffer(.chan(`DDR_CHANNEL), .dst_addr(`DDR_HOST_MEM_BUFFER_ADDR_1), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_1), .len(len1));
      tb.que_cl_to_buffer(.chan(`DDR_CHANNEL), .dst_addr(`DDR_HOST_MEM_BUFFER_ADDR_2), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_2), .len(len2));
      tb.que_cl_to_buffer(.chan(`DDR_CHANNEL), .dst_addr(`DDR_HOST_MEM_BUFFER_ADDR_3), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_3), .len(len3));
      tb.start_que_to_buffer(.chan(`DDR_CHANNEL));

      wait_for_dma_transfer_from_cl_to_buffer(.chan(`DDR_CHANNEL));

      #1us;

      $display("[%t] : Comparing DMA buffer from DDR sequence 0 with expected pattern", $realtime);
      check_host_memory(.addr(`DDR_HOST_MEM_BUFFER_ADDR_0), .expected_data_pattern(8'hAA), .num_bytes(len0));

      $display("[%t] : Comparing DMA buffer from DDR sequence 1 with expected pattern", $realtime);
      check_host_memory(.addr(`DDR_HOST_MEM_BUFFER_ADDR_1), .expected_data_pattern(8'hBB), .num_bytes(len1));

      $display("[%t] : Comparing DMA buffer from DDR sequence 2 with expected pattern", $realtime);
      check_host_memory(.addr(`DDR_HOST_MEM_BUFFER_ADDR_2), .expected_data_pattern(8'hCC), .num_bytes(len2));

      $display("[%t] : Comparing DMA buffer from DDR sequence 3 with expected pattern", $realtime);
      check_host_memory(.addr(`DDR_HOST_MEM_BUFFER_ADDR_3), .expected_data_pattern(8'hDD), .num_bytes(len3));

      #500ns;
      tb.power_down();

      report_pass_fail_status();

      $finish;
   end // initial begin

endmodule // test_dram_dma_mem_model_bdr_wr
