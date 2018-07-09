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


module test_cl();

import tb_type_defines_pkg::*;


`define GPIO_REG_ADDR 64'h00
`define GPIO2_REG_ADDR 64'h08


`define MEM_BASE 64'hC0000000


// AXI ID
parameter [5:0] AXI_ID = 6'h0;

logic [31:0] rdata;
logic [15:0] vdip_value;
logic [15:0] vled_value;
integer i;

   initial begin

      tb.power_up();


      #1000ns;

      //Reading from to GPIO for VDIP value
     
      //Writing to GPIO for VLED
       tb.poke(.addr(`GPIO_REG_ADDR), .data(32'h0000_AAAA), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1)); // write register
      #1000ns;

      vled_value = tb.get_virtual_led();
      $display ("value of vled:%0x", vled_value);      

     
      tb.poke(.addr(`MEM_BASE + 32'h00000000), .data(32'h6C6C_6548), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_DMA_PCIS)); // write register
      tb.poke(.addr(`MEM_BASE + 32'h00000004), .data(32'h6F57_206F), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_DMA_PCIS)); // write register
      tb.poke(.addr(`MEM_BASE + 32'h00000008), .data(32'h2164_6C72), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_DMA_PCIS)); // write register

        for(i = 0; i < 3; i = i +1) begin
          tb.peek(.addr(`MEM_BASE + i*32'h00000004), .data(rdata), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_DMA_PCIS));
          $display ("%c", rdata[7:0]);
          $display ("%c", rdata[15:8]);                
          $display ("%c", rdata[23:16]);
          $display ("%c", rdata[31:24]);
        end


      tb.kernel_reset();

      tb.power_down();
      
      $finish;
   end

endmodule // test_hello_world
