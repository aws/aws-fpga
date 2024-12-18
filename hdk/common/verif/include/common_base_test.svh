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


`define DDR_CHANNEL 0
`define HBM_CHANNEL 1

`define _8_GB 64'h0002_0000_0000
`define _16_GB 64'h0004_0000_0000
`define _24_GB 64'h0006_0000_0000
`define _32_GB 64'h0008_0000_0000
`define _48_GB 64'h000C_0000_0000
`define _64_GB 64'h0010_0000_0000


`ifdef USE_32GB_DDR_DIMM
    `define AWS_SIM_32GB_DDR
`elsif USE_AP_32GB_DDR_DIMM
    `define AWS_SIM_32GB_DDR
`elsif USE_64GB_DDR_DIMM
    `define AWS_SIM_64GB_DDR
`elsif USE_AP_64GB_DDR_DIMM
    `define AWS_SIM_64GB_DDR
`endif


int error_count = 0;


function void print_result;
    input bit success;
    if (success == 1'b1)
        $display("*** TEST PASSED ***");
    else
        $display("*** TEST FAILED ***");
endfunction


task report_pass_fail_status(bit additional_case = 1'b1);
   $display("[%t] : Detected %3d errors", $realtime, error_count);
   print_result(error_count == 0 && (!tb.chk_prot_err_stat()) && additional_case);
endtask


task compare_data(logic [511:0] act_data, exp_data, logic [63:0] addr);
   if(act_data !== exp_data) begin
      $error("[%t] ***ERROR*** : Data Mismatch Addr: %0h. Actual Data:%0h <==> Expected Data: %0h", $realtime, addr, act_data, exp_data);
      error_count ++;
   end
   else begin
      $display("[%t]: Data Matched Addr: %0h. Actual Data:%0h <==> Expected Data: %0h", $realtime, addr, act_data, exp_data);
   end
endtask
