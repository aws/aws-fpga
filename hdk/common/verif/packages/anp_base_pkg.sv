//------------------------------------------------------------------------------
// Amazon FPGA Hardware Development Kit
//
// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
//------------------------------------------------------------------------------

package anp_base_pkg;

   static int errors_quit_count = get_quit_count();
   static int infos;
   static int warnings;
   static int errors;
   static int fatals;
   static bit eot_called = 0;
   static bit msg_show_file_info = ($test$plusargs("ANP_MSG_SHOW_FILE_INFO")) ? 1: 0;
   static bit msg_no_info = ($test$plusargs("ANP_MSG_NO_INFO")) ? 1: 0;
   static bit msg_debug = ($test$plusargs("ANP_DEBUG")) ? 1: 0;
   static bit msg_no_fatal_exit = ($test$plusargs("ANP_NO_FATAL_EXIT")) ? 1: 0;

   function int get_quit_count();
      int value;
      if (!$value$plusargs("ANP_MAX_QUIT_COUNT=%d", value)) begin
         value = 9999;
      end
      return value;
   endfunction : get_quit_count

   function void end_of_test();
      string s;
      int fp;
      if (eot_called == 1) return;
      s = "--- ANP Report Summary ---\n";
      s = {s, $sformatf("Quit count : %0d of %0d\n", errors, errors_quit_count)};
      s = {s, "** Report counts by severity\n"};
      s = {s, $sformatf("INFO    : %0d\n", infos)};
      s = {s, $sformatf("WARNING : %0d\n", warnings)};
      s = {s, $sformatf("ERROR   : %0d\n", errors)};
      s = {s, $sformatf("FATAL   : %0d\n", fatals)};
      s = {s, "** Test's status\n"};
      if ((fatals + errors) > 0) begin
         fp = $fopen("failed", "w");
         s = {s, "TEST FAILED\n"};
      end
      else begin
         fp = $fopen("passed", "w");
         s = {s, "TEST PASSED\n"};
      end
      $fwrite(fp, ".empty_file");
      $fclose(fp);
      $display(s);
      eot_called = 1;
      $finish(2);
   endfunction : end_of_test

endpackage : anp_base_pkg


