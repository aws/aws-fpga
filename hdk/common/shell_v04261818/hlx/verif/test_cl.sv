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
//Change the below base address based upon design
`define OCL_ADDR 64'h0
`define SDA_ADDR 64'h0
`define BAR1_ADDR 64'h0

//Change the below base address for DDR4 memory or slave memory in CL
`define MEM_BASE_WRITE 64'hE01000000
`define MEM_BASE_READ 64'hE01000000


// AXI ID
parameter [5:0] AXI_ID = 6'h0;

logic [31:0] rdata;
logic [15:0] vdip_value;
logic [15:0] vled_value;


   initial begin

      tb.power_up();
      
       tb.nsec_delay(500);
       
       //Comment back in if DDR4 in the CL is used
       //tb.poke_stat(.addr(8'h0c), .ddr_idx(0), .data(32'h0000_0000));
       //tb.poke_stat(.addr(8'h0c), .ddr_idx(1), .data(32'h0000_0000));
       //tb.poke_stat(.addr(8'h0c), .ddr_idx(2), .data(32'h0000_0000));


      //Example for write and read BAR1_ADDR
      //tb.poke(.addr(`BAR1_ADDR), .data(32'hDEAD_BEEF), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1));       
      //tb.peek(.addr(`BAR1_ADDR), .data(rdata), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1));
      //$display ("Reading 0x%x from address 0x%x", rdata, `BAR1_ADDR);
      
      //Example for write and read OCL_ADDR
      //tb.poke(.addr(`OCL_ADDR), .data(32'hDEAD_BEEF), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_OCL));       
      //tb.peek(.addr(`OCL_ADDR), .data(rdata), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_OCL));
      //$display ("Reading 0x%x from address 0x%x", rdata, `OCL_ADDR);
      
      //Example for write and read SDA_ADDR
      //tb.poke(.addr(`SDA_ADDR), .data(32'hDEAD_BEEF), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_SDA));       
      //tb.peek(.addr(`SDA_ADDR), .data(rdata), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_SDA));
      //$display ("Reading 0x%x from address 0x%x", rdata, `SDA_ADDR);
      
      //Example for write and read for DMA_PCIS (to DDR4 memory address or other slave address in CL)
      //tb.poke(.addr(`MEM_BASE_WRITE), .data(32'hDEAD_BEEF), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_DMA_PCIS));
      //tb.peek(.addr(`MEM_BASE_READ), .data(rdata), .id(AXI_ID), .size(DataSize::UINT32), .intf(AxiPort::PORT_DMA_PCIS));
      //$display ("Reading 0x%x from address 0x%x", rdata, `MEM_BASE_READ);
      
      //Setting VDIP
      //tb.set_virtual_dip_switch(.dip(16'hAAAA));
      
      //Reading VLED
      //vled_value = tb.get_virtual_led();
      //$display ("value of vled:%0x", vled_value);      
      

      tb.kernel_reset();

      tb.power_down();
      
      $finish;
   end

endmodule 
