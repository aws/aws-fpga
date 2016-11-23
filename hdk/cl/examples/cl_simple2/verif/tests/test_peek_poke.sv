// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

module test_peek_poke();

   logic [31:0]       write_data_b[16];
   logic [31:0]       read_data_b[16];
   
   logic [31:0]        read_data;

   initial begin
      tb.sh.power_up();

      tb.sh.peek(64'h0, 6'h0, read_data);
      $display("read_data: %x", read_data);
      
      tb.sh.peek(64'h4, 6'h0, read_data);
      $display("read_data: %x", read_data);
      
      tb.sh.peek(64'h8, 6'h0, read_data);
      $display("read_data: %x", read_data);
      
      tb.sh.poke(64'h10, 32'h11223344, 6'h0);

      tb.sh.peek(64'h10, 6'h0, read_data);
      $display("read_data: %x", read_data);
/*
      write_data_b[0] = 32'h44332211;
      write_data_b[1] = 32'h55667788;
      write_data_b[2] = 32'h99AABBCC;
      write_data_b[3] = 32'hDDEEFF11;
      for (int i=4; i<16; i++) begin
         write_data_b[i] = 'h0;
      end
      
      tb.sh.poke_burst(64'h4, 4, write_data_b);
      
      tb.sh.peek_burst(64'h4, 4, read_data_b);
      for (int n= 0; n<$size(read_data_b);n++) begin
         $display("read_data: %x", read_data_b[n]);
      end     
      #500ns;
*/

      #5000ns;

      tb.sh.power_down();
      $finish;
   end

endmodule // test_peek_poke
