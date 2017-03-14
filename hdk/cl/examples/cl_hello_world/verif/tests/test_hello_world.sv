// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

module test_hello_world();

import tb_type_defines_pkg::*;
`include "cl_common_defines.vh" // CL Defines with register addresses

// AXI Transaction Size
parameter SIZE_1B = 0, // 1 Byte
          SIZE_2B = 1, // 2 Bytes
          SIZE_4B = 2, // 4 Bytes
          SIZE_8B = 3; // 8 Bytes

// AXI ID
parameter [5:0] AXI_ID = 6'h0;

logic [31:0] rdata;
logic [15:0] vdip_value;
logic [15:0] vled_value;


   initial begin

      tb.card.fpga.sh.power_up();
      
      tb.card.fpga.sh.set_virtual_dip_switch(0);

      vdip_value = tb.card.fpga.sh.read_virtual_dip_switch(0);

      $display ("value of vdip:%0x", vdip_value);

      $display ("Writing 0xDEAD_BEEF to address 0x%x", `HELLO_WORLD_REG_ADDR);
      tb.card.fpga.sh.poke(`HELLO_WORLD_REG_ADDR, 32'hDEAD_BEEF, AXI_ID, SIZE_2B, AxiPort::PORT_OCL); // write register

      tb.card.fpga.sh.peek(`HELLO_WORLD_REG_ADDR, rdata, AXI_ID, SIZE_2B, AxiPort::PORT_OCL);         // start read & write
      $display ("Reading 0x%x from address 0x%x", rdata, `HELLO_WORLD_REG_ADDR);

      if (rdata == 32'hEFBE_ADDE) // Check for byte swap in register read
        $display ("Test PASSED");
      else
        $display ("Test FAILED");

      tb.card.fpga.sh.peek(`VLED_REG_ADDR, rdata, AXI_ID, SIZE_2B, AxiPort::PORT_OCL);         // start read
      $display ("Reading 0x%x from address 0x%x", rdata, `VLED_REG_ADDR);

      if (rdata == 32'h0000_BEEF) // Check for LED register read
        $display ("Test PASSED");
      else
        $display ("Test FAILED");

      vled_value = tb.card.fpga.sh.read_virtual_led(0);

      $display ("value of vled:%0x", vled_value);

      tb.card.fpga.sh.kernel_reset();

      tb.card.fpga.sh.power_down();
      
      $finish;
   end

endmodule // test_hello_world
