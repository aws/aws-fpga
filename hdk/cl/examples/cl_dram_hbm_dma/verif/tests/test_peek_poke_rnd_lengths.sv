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


// PCIM test with random lengths for each transfer

module test_peek_poke_rnd_lengths();

   import tb_type_defines_pkg::*;

   `include "base_test_utils.svh"

   logic [7:0] len;

   initial begin

	  tb.power_up();
	  initialize_ddr();

      len = 0 ;

      for(int addr =0; addr <=1023; addr = addr+64) begin
         $display("[%t] : Programming cl_tst registers for PCIM", $realtime);
         len = $urandom_range(16, 1);
         $display("[%t] : Number of AXI data phases %d \n", $realtime, len);

      	 program_cl_tst(.base_addr(64'h0000), .test_addr(64'h1234_0000 + addr), .enable_write(1'b1), .enable_read(1'b1),
              			 .axi_len(len), .iter_mode(1'b0), .num_iter(0), .num_inst(16'h0001));
      end // for (int addr =0; addr <=63; addr++)

      tb.power_down();

      report_pass_fail_status();

      $finish;
   end

endmodule // test_peek_poke_rnd_lengths
