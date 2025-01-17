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


// This test initiates dma and pcim traffic in parallel.

module test_peek_poke();

   import tb_type_defines_pkg::*;

   `include "base_test_utils.svh"

   initial begin

	  tb.power_up();
	  initialize_ddr();

      $display("[%t] : Programming cl_tst registers for PCIM", $realtime);
  	  program_cl_tst(.base_addr(64'h0000), .test_addr(64'h1234_0000), .enable_write(1'b1), .enable_read(1'b1),
          			 .axi_len(8'h07), .iter_mode(1'b0), .num_iter(0), .num_inst(16'h000f));

      #500ns;
      tb.power_down();

	  report_pass_fail_status();

      $finish;
   end // initial begin

endmodule // test_peek_poke
