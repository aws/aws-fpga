// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

module test_null();

   initial begin
      int exit_code;
      
      tb.sh.power_up();

      tb.test_main(exit_code);
      
      #50ns;

      tb.sh.power_down();
      
      $finish;
   end

endmodule // test_null
