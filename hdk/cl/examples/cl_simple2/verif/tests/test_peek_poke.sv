// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

module test_peek_poke();

`define WR_INSTR_INDEX 64'h1c
`define WR_ADDR_LOW    64'h20
`define WR_ADDR_HIGH   64'h24
`define WR_DATA        64'h28
`define WR_SIZE        64'h2c

`define RD_INSTR_INDEX 64'h3c
`define RD_ADDR_LOW    64'h40
`define RD_ADDR_HIGH   64'h44
`define RD_DATA        64'h48
`define RD_SIZE        64'h4c

`define CNTL_REG       64'h08

`define WR_START_BIT   32'h00000001
`define RD_START_BIT   32'h00000002
   
   logic [63:0] pcim_address = 64'h0000_0000_1234_0000;
   
   initial begin

      tb.sh.power_up();

      tb.sh.poke(`WR_INSTR_INDEX, 0);                   // write index
      tb.sh.poke(`WR_ADDR_LOW, pcim_address[31:0]);     // write address low
      tb.sh.poke(`WR_ADDR_HIGH, pcim_address[63:32]);   // write address high
      tb.sh.poke(`WR_DATA, 32'h0000_0000);              // write data
      tb.sh.poke(`WR_SIZE, 32'h0000_0002);              // write 32b

      tb.sh.poke(`RD_INSTR_INDEX, 0);                   // read index
      tb.sh.poke(`RD_ADDR_LOW, pcim_address[31:0]);     // read address low
      tb.sh.poke(`RD_ADDR_HIGH, pcim_address[63:32]);   // read address high
      tb.sh.poke(`RD_DATA, 32'h0000_0000);              // read data
      tb.sh.poke(`RD_SIZE, 32'h0000_0002);              // read 32b

      tb.sh.poke(`CNTL_REG, 32'h0003);                  // start read & write

      #500ns;   // give the hardware time to run

      tb.sh.power_down();
      
      $finish;
   end

endmodule // test_peek_poke
