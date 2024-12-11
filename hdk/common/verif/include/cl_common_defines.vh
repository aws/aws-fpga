// Amazon FPGA Hardware Development Kit
//
// Copyright 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
