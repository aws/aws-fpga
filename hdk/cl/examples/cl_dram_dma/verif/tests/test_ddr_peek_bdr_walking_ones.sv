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
// This test shows example of backdoor loading DRAM micron memory and frontdoor reading through DMA.
// The test covers valid rows, bank groups, banks and columns
// The test also covers some row, bank group, bank and column combinations.

module test_ddr_peek_bdr_walking_ones();

   import tb_type_defines_pkg::*;

   int error_count;
   int timeout_count;
   int fail;
   logic [3:0] status;

   //transfer1 - length 64bits.
   int         len0 = 8;
   int         fp;
   int         r;
   reg [1000:0] hdk_name;
   string       file_name;
                       
   initial begin

      logic [63:0] bdr_addr, host_memory_buffer_address;

      logic [63:0] read_data;

      logic [511:0] data;
      
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

      r = $value$plusargs("HDKDIR=%s", hdk_name);
      $display("Value is %0s", hdk_name);
      
      $display("backdoor load memory \n");

      file_name = $sformatf("%0s/cl/examples/cl_dram_dma/verif/scripts/axi_bkdr.mem", hdk_name);

      $display("file_name is %0s", file_name);
      
      fp = $fopen(file_name, "w");

      //Backdoor load data
      bdr_addr = 'h0;
      //Write 8*64 bits of data starting at address 'h0
      //Covers different columns
      $fdisplay(fp, "%0h %0h", bdr_addr, 512'h7777777777777776666666666666666555555555555555544444444444444443333333333333333222222222222222211111111111111100000000000000000);

      bdr_addr = 'h100;
      //Write 8*64 bits of data starting at address 'h100
      //Covers different columns
      $fdisplay(fp, "%0h %0h", bdr_addr, 512'h7777777777777776666666666666666555555555555555544444444444444443333333333333333222222222222222211111111111111100000000000000000);

      //Covers rows
      for ( int i=0; i<4; i++) begin
         bdr_addr = 'h20000 << i;
         $fdisplay(fp, "%0h %0h", bdr_addr, 512'h7777777777777776666666666666666555555555555555544444444444444443333333333333333222222222222222211111111111111100000000000000000);
      end
      //Covers some row, bank group, bank and column combinations
      for ( int i=0; i<4; i++) begin
         bdr_addr = 'h20040 << i;
          //Write 8*64 bits of data starting at address 'h100
         //Covers different columns
         $fdisplay(fp, "%0h %0h", bdr_addr, 512'h7777777777777776666666666666666555555555555555544444444444444443333333333333333222222222222222211111111111111100000000000000000);
      end

      bdr_addr = 'h300;
      //Write 8*64 bits of data starting at address 'h100
      //Covers different columns
      $fdisplay(fp, "%0h %0h", bdr_addr, 512'h7777777777777776666666666666666555555555555555544444444444444443333333333333333222222222222222211111111111111100000000000000000);

      bdr_addr = 'h1000;
      //Write 8*64 bits of data starting at address 'h100
      //Covers different columns
      $fdisplay(fp, "%0h %0h", bdr_addr, 512'h7777777777777776666666666666666555555555555555544444444444444443333333333333333222222222222222211111111111111100000000000000000);
      
      // end
      $fclose(fp);
      
      tb.card.ddr_bdr_ld(file_name);
      
      tb.nsec_delay(500);

      data = 512'h7777777777777776666666666666666555555555555555544444444444444443333333333333333222222222222222211111111111111100000000000000000;
      //Backdoor load data
      bdr_addr = 'h0;
      //Write 8*64 bits of data starting at address 'h0
      //Covers different columns
      ddr_peeks(bdr_addr, 1, data);

      bdr_addr = 'h100;
      //Write 8*64 bits of data starting at address 'h100
      //Covers different columns
      ddr_peeks(bdr_addr, 1, data);

      //Covers rows
      for ( int i=0; i<4; i++) begin
         bdr_addr = 'h20000 << i;
      //Front Door read data
         ddr_peeks(bdr_addr, 1, data);
      end
      //Covers some row, bank group, bank and column combinations
      for ( int i=0; i<4; i++) begin
         bdr_addr = 'h20040 << i;
      //Front Door read data
         ddr_peeks(bdr_addr, 1, data);
      end
   
      tb.nsec_delay(2000);
      
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

   task ddr_peeks(logic [63:0] addr, int num_xfers, logic [511:0] data);
      logic [63:0] bdr_addr;
      logic [511:0] read_data;
      //Front Door read data
      for ( int i=0; i<num_xfers; i++) begin
         bdr_addr = addr << i;
         tb.peek(.addr(bdr_addr), .data(read_data), .size(DataSize::UINT512));
         $display("Read Data for Addr %h: Act %h", bdr_addr, read_data);

         if (read_data != data) begin
            $display("Read Data mismatch for Addr %h: Exp %h, Act %h", bdr_addr, data, read_data);
            error_count++;
         end
      end
   endtask // ddr_peeks
   
endmodule // test_ddr_peek_bdr_walking_ones



