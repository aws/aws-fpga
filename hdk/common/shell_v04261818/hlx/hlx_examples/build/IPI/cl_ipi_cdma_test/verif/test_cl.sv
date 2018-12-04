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
`define OCL_GPIO_ADDR 64'h0
`define SDA_GPIO_ADDR 64'h0

`define CDMA_REG_ADDR_CONTROL 64'h00
`define CDMA_REG_ADDR_STATUS 64'h04

`define CDMA_REG_ADDR_SRC_ADDR 64'h18
`define CDMA_REG_ADDR_SRC_MSB_ADDR 64'h1C

`define CDMA_REG_ADDR_DST_ADDR 64'h20
`define CDMA_REG_ADDR_DST_MSB_ADDR 64'h24

`define CDMA_REG_ADDR_BYTES 64'h28

`define MEM_BASE_WRITE 64'hE01000000
`define MEM_BASE_READ 64'hD02000000


// AXI ID
parameter [5:0] AXI_ID = 6'h0;

logic [31:0] rdata;
logic [15:0] vdip_value;
logic [15:0] vled_value;


   initial begin

      tb.power_up();
      
       tb.nsec_delay(500);
       tb.poke_stat(.addr(8'h0c), .ddr_idx(0), .data(32'h0000_0000));
       tb.poke_stat(.addr(8'h0c), .ddr_idx(1), .data(32'h0000_0000));
       tb.poke_stat(.addr(8'h0c), .ddr_idx(2), .data(32'h0000_0000));




      tb.peek(.addr(`SDA_GPIO_ADDR), .data(rdata), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_SDA));         // start read & write
      
      while (rdata != 32'h00000008) begin
      tb.peek(.addr(`SDA_GPIO_ADDR), .data(rdata), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_SDA));         // start read & write
      end
       $display ("DDR4 All Memory are Ready!");
       

      tb.poke(.addr(`MEM_BASE_WRITE), .data(32'hDEAD_BEEF), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_DMA_PCIS)); // write register
      
      tb.poke(.addr(`CDMA_REG_ADDR_SRC_ADDR), .data(32'h0100_0000), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1)); // write register
      tb.poke(.addr(`CDMA_REG_ADDR_SRC_MSB_ADDR), .data(32'h0000_000E), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1)); // write register

      #1000ns;
 
       tb.poke(.addr(`CDMA_REG_ADDR_DST_ADDR), .data(32'h0200_0000), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1)); // write register
       tb.poke(.addr(`CDMA_REG_ADDR_DST_MSB_ADDR), .data(32'h0000_000D), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1)); // write register

      
      #1000ns;
       tb.poke(.addr(`CDMA_REG_ADDR_BYTES), .data(32'h0000_4000), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1)); // write register
      

      tb.peek(.addr(`CDMA_REG_ADDR_STATUS), .data(rdata), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1));         // start read & write
      

      while (rdata != 32'h00001002) begin
      tb.peek(.addr(`CDMA_REG_ADDR_STATUS), .data(rdata), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1));         // start read & write
      end
      
      $display ("Reading 0x%x from address 0x%x", rdata, `CDMA_REG_ADDR_STATUS);
     
      tb.peek(.addr(`MEM_BASE_READ), .data(rdata), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_DMA_PCIS));         // start read & write
      $display ("Reading 0x%x from address 0x%x", rdata, `MEM_BASE_READ);

      //Writing to GPIO for VLED
       tb.poke(.addr(`SDA_GPIO_ADDR), .data(32'h0000_AAAA), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_OCL)); // write register
      #1000ns;

      vled_value = tb.get_virtual_led();

      $display ("value of vled:%0x", vled_value);      

      tb.kernel_reset();

      tb.power_down();
      
      $finish;
   end

endmodule // test_hello_world
