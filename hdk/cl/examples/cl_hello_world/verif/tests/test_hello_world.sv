// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

module test_hello_world();

`define HELLO_WORLD_REG_ADDR 64'h00

logic [31:0] rdata;

   initial begin

      tb.sh.power_up();

      $display ("Writing 0xDEAD_BEEF to address 0x%x", `HELLO_WORLD_REG_ADDR);
      tb.sh.poke(`HELLO_WORLD_REG_ADDR, 32'hDEAD_BEEF); // write register

      tb.sh.peek(`HELLO_WORLD_REG_ADDR, rdata);         // start read & write
      $display ("Reading 0x%x from address 0x%x", rdata, `HELLO_WORLD_REG_ADDR);

      if (rdata == 32'hEFBE_ADDE) // Check for byte swap in register read
        $display ("Test PASSED");
      else
        $display ("Test FAILED");

      tb.sh.power_down();
      
      $finish;
   end

endmodule // test_hello_world
