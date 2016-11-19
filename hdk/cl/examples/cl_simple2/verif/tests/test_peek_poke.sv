// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

module test_peek_poke();

   logic [31:0]        read_data;

   initial begin
      tb.sh.power_up();

      tb.sh.peek(64'h0, read_data);
      $display("read_data: %x", read_data);
      
      tb.sh.peek(64'h4, read_data);
      $display("read_data: %x", read_data);
      
      tb.sh.peek(64'h8, read_data);
      $display("read_data: %x", read_data);
      
      tb.sh.poke(64'h10, 32'h11223344);
      
      #500ns;
      
      tb.sh.power_down();
      $finish;
   end

endmodule // test_peek_poke
