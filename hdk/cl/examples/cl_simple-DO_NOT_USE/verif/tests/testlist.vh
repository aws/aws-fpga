// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

task verilog_run_test;
   begin
      if (testname=="pcie_test")
        pcie_test;
      else if (testname=="ddr_test")
        ddr_test;
      else
        begin
           $display("*** FATAL *** Specified unknown value for testname : %0s", testname);
           $finish;
        end
   end
endtask
