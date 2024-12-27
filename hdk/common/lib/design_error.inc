// ============================================================================
// Amazon FPGA Hardware Development Kit
//
// Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
// ============================================================================


//------------------------------------------------------------
// These are routines to report design errors uniformly
//------------------------------------------------------------

//import uvm_pkg::*;

task design_error (input string err_str);
begin
   `ifdef UVM_ENABLED
      `uvm_error("DESIGN", $psprintf("%m: %s", err_str));
   `else
      $display($time,,,"%m: ***DESIGN ERROR*** %s", err_str);
   `endif

   `ifndef DISABLE_DESIGN_ERROR_FINISH
      $display("Design Error killing sim...");
      repeat(5)
         @(posedge clk);
      $finish;
   `endif
end
endtask
