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
// This test frontdoor writes and backdoor reads AXI memory model.

module test_dram_dma_mem_model_bdr_rd();

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

      $display("[%t] : Initializing DDR buffers", $realtime);
	  load_host_memory(.chan(`DDR_CHANNEL), .host_addr(64'h0000), .cl_addr(`DDR_BASE_ADDR), .data_pattern(8'hAA), .num_bytes(len0));
	  load_host_memory(.chan(`DDR_CHANNEL), .host_addr(64'h3000), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_1), .data_pattern(8'hBB), .num_bytes(len1));
	  load_host_memory(.chan(`DDR_CHANNEL), .host_addr(64'h6000), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_2), .data_pattern(8'hCC), .num_bytes(len2));
	  load_host_memory(.chan(`DDR_CHANNEL), .host_addr(64'h9000), .cl_addr(`DDR_BASE_ADDR + `DDR_LEVEL_3), .data_pattern(8'hDD), .num_bytes(len3));

      $display("[%t] : starting H2C DMA channels ", $realtime);
      tb.start_que_to_cl(.chan(`DDR_CHANNEL));
	  wait_for_dma_transfer_from_buffer_to_cl(.chan(`DDR_CHANNEL));
      #1us;

      $display("Back door read memory from DDR Base Address \n");
      ddr_addr_0 = `DDR_BASE_ADDR;
      for (int i = 0 ; i < len0 ; i++) begin
         if (tb.card.fpga.CL.SH_DDR.u_mem_model.axi_mem_bdr_read(.addr(ddr_addr_0)) !== 8'hAA) begin
            $error("[%t] : *** ERROR *** DDR Sequence 0 Data mismatch, addr:%0x read data is: %0x",
                     $realtime, ddr_addr_0, (tb.card.fpga.CL.SH_DDR.u_mem_model.axi_mem_bdr_read(.addr(ddr_addr_0))));
            error_count++;
         end
         ddr_addr_0++;
      end


      $display("Back door read memory from DDR Offset 8 GB \n");
      ddr_addr_1 = `DDR_BASE_ADDR + `DDR_LEVEL_1;
      for (int i = 0 ; i < len1 ; i++) begin
         if (tb.card.fpga.CL.SH_DDR.u_mem_model.axi_mem_bdr_read(.addr(ddr_addr_1)) !== 8'hBB) begin
            $error("[%t] : *** ERROR *** DDR Sequence 1 Data mismatch, addr:%0x read data is: %0x",
                     $realtime, ddr_addr_1, (tb.card.fpga.CL.SH_DDR.u_mem_model.axi_mem_bdr_read(.addr(ddr_addr_1))));
            error_count++;
         end
         ddr_addr_1++;
      end

      $display("Back door read memory from DDR Offset 16 GB \n");
      ddr_addr_2 = `DDR_BASE_ADDR + `DDR_LEVEL_2;
      for (int i = 0 ; i < len2 ; i++) begin
         if (tb.card.fpga.CL.SH_DDR.u_mem_model.axi_mem_bdr_read(.addr(ddr_addr_2)) !== 8'hCC) begin
            $error("[%t] : *** ERROR *** DDR Sequence 2 Data mismatch, addr:%0x read data is: %0x",
                     $realtime, ddr_addr_2, (tb.card.fpga.CL.SH_DDR.u_mem_model.axi_mem_bdr_read(.addr(ddr_addr_2))));
            error_count++;
         end
         ddr_addr_2++;
      end

      $display("Back door read memory from DDR Offset 24 GB \n");
      ddr_addr_3 = `DDR_BASE_ADDR + `DDR_LEVEL_3;
      for (int i = 0 ; i < len3 ; i++) begin
         if (tb.card.fpga.CL.SH_DDR.u_mem_model.axi_mem_bdr_read(.addr(ddr_addr_3)) !== 8'hDD) begin
            $error("[%t] : *** ERROR *** DDR Sequence 3 Data mismatch, addr:%0x read data is: %0x",
                     $realtime, ddr_addr_3, (tb.card.fpga.CL.SH_DDR.u_mem_model.axi_mem_bdr_read(.addr(ddr_addr_3))));
            error_count++;
         end
         ddr_addr_3++;
      end

      #500ns;
      tb.power_down();

	  report_pass_fail_status();

      $finish;
   end // initial begin

endmodule // test_dram_dma_mem_model_bdr_rd
