// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

module test_peek_poke();

   logic [63:0] pcim_address = 64'h0000_0000_1234_0000;
   

   initial begin
      tb.sh.power_up();

//      tb.sh.peek(64'h0, read_data);
//      $display("read_data: %x", read_data);
      
//      tb.sh.peek(64'h4, read_data);
//      $display("read_data: %x", read_data);
      
//      tb.sh.peek(64'h8, read_data);
//      $display("read_data: %x", read_data);
      

      tb.sh.poke(64'h1c, 0);                   // write index
      tb.sh.poke(64'h20, pcim_address[31:0]);  // write address low
      tb.sh.poke(64'h24, pcim_address[63:32]); // write address high
      tb.sh.poke(64'h28, 32'h0000_0000);       // write data
      tb.sh.poke(64'h2c, 32'h0000_0002);       // write 32b

      tb.sh.poke(64'h3c, 0);                   // read index
      tb.sh.poke(64'h40, pcim_address[31:0]);  // read address low
      tb.sh.poke(64'h44, pcim_address[63:32]); // read address high
      tb.sh.poke(64'h48, 32'h0000_0000);       // read data
      tb.sh.poke(64'h4c, 32'h0000_0002);       // read 32b

      tb.sh.poke(64'h08, 32'h0003);  // start read & write

      #1000ns;

      tb.sh.power_down();
      $finish;
   end

endmodule // test_peek_poke
