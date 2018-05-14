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
// This test tests add, delete and find operations of a URAM.

module test_uram_example();

import tb_type_defines_pkg::*;
`include "cl_common_defines.vh" // CL Defines with register addresses

// AXI ID
parameter [5:0] AXI_ID = 6'h0;

logic [31:0] rdata;
logic [15:0] vdip_value;
logic [15:0] vled_value;
int rc;
int timeout;
   
logic [31:0] value = 0;
logic [31:0] find_ok = 0;
logic [31:0] find_ko = 0;
logic [31:0] busy = 0;
logic [31:0] del_info;
logic [31:0] glb_value;

   task uram_task(input [31:0] value);

      del_info = value[29];
                 
      tb.poke(.addr(64'h500), .data(value), .intf(AxiPort::PORT_OCL));

      // Wait for the busy status to be cleared
      
      busy = 1;
      do begin 
         if (timeout == 10) begin
            $display("Timeout - Something went wrong with the HW. Please do\n");
            $finish;
         end
         if (timeout) begin
            $display("Please wait, it may take time ...\n");
         end
         // Wait for the HW to process
         tb.nsec_delay(10000);
         timeout++;

         // Read
         tb.peek(.addr(64'h500), .data(value), .intf(AxiPort::PORT_OCL));

         find_ok = value[31];
         find_ko = value[30];
         busy = value[29];
         value = value & 32'h1fffffff;
         $display("Read 0x%08x find_ok=%d find_ko=%d, busy=%d\n", value, find_ok, find_ko, busy);
      end while (busy == 1);
      
      if (find_ok == 1) begin
         if (del_info == 1) begin
            $display("Deletion OK : The value 0x%x has been deleted successfully\n", value);
         end
         else begin
            $display("Find OK : The value 0x%x is present in the URAM\n", value); 
         end
      end
      else begin
         if (find_ko == 1) begin
            $display("Find KO : The value 0x%x is NOT present in the URAM\n", value); 
         end 
         else begin
            $display("The value 0x%x has been added to the URAM successfully\n", value);
         end
      end // if (find_ok == 1)
   endtask // uram_task
   
   initial begin

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

      tb.nsec_delay(27000);
      
      $display("Execute command Find FEEDBABE \n");

      value = 32'hFEEDBABE;

      value = value | 32'h80000000;

      $display("Writing 0x%08x\n", value);

      uram_task(value);

      $display("Execute command Add CAFE4B1D \n");

      value = 32'hCAFE4B1D;

      value = value | 32'h40000000;

      $display("Writing 0x%08x\n", value);

      uram_task(value);

      $display("Execute command Del DEADDEAD \n");

      value = 32'hDEADDEAD;

      value = value | 32'ha0000000;

      $display("Writing 0x%08x\n", value);

      uram_task(value);

      $finish;
   end
   
endmodule // test_uram_example
