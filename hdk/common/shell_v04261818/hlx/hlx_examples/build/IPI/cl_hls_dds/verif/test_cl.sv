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
//`include "cl_common_defines.vh" // CL Defines with register addresses

`define DDS_REG_ADDR_CONTROL 64'h00000000
`define DDS_REG_ADDR_NOFSAMP 64'h00000010
`define DDS_REG_ADDR_INCR_V 64'h00000018

`define DDS_REG_ADDR_INT_ENABLE 64'h00000008
`define DDS_REG_ADDR_INT_STAT 64'h0000000C

`define USR_GPIO_ADDR 64'h00010000


`define MEM_BASE_READ_0 64'h81000000
`define MEM_BASE_READ_1 64'h82000000



// AXI ID
parameter [5:0] AXI_ID = 6'h0;

logic [31:0] rdata;
logic [15:0] vdip_value;
logic [15:0] vled_value;


   initial begin

       tb.power_up(.clk_recipe_a(ClockRecipe::A1));
       
       tb.nsec_delay(500);



      tb.peek(.addr(`USR_GPIO_ADDR), .data(rdata), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1));         // start read & write
      
      while (rdata != 32'h00000001) begin
      tb.peek(.addr(`USR_GPIO_ADDR), .data(rdata), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1));         // start read & write
      end
       $display ("DDR4 SH is Ready!");


       $display ("Configuring HLS IP");   

      tb.poke(.addr(`DDS_REG_ADDR_INCR_V), .data(32'h0020_C49C), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1)); // write register
      tb.poke(.addr(`DDS_REG_ADDR_NOFSAMP), .data(32'h0000_0800), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1)); // write register
      tb.poke(.addr(`DDS_REG_ADDR_INT_ENABLE), .data(32'h0000_0001), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1)); // write register


       $display ("Writing to HLS Control to Start Transfer");   
      #1000ns;
      
      tb.poke(.addr(`DDS_REG_ADDR_CONTROL), .data(32'h0000_0001), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1)); // write register

      tb.peek(.addr(`DDS_REG_ADDR_INT_STAT), .data(rdata), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1));         // start read & write
      

      while (rdata != 32'h00000001) begin
      tb.peek(.addr(`DDS_REG_ADDR_INT_STAT), .data(rdata), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1));         // start read & write
      end
      
      $display ("Reading 0x%x from address 0x%x", rdata, `DDS_REG_ADDR_INT_STAT);

      tb.peek(.addr(`MEM_BASE_READ_0), .data(rdata), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_DMA_PCIS));         // start read & write
      $display ("Reading 0x%x from address 0x%x", rdata, `MEM_BASE_READ_0);


      tb.kernel_reset();

      tb.power_down();
      
      $finish;
   end

endmodule // test_hello_world
