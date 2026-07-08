// ============================================================================
// Amazon FPGA Hardware Development Kit
//
// Copyright 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

// Test Null - minimal test to verify cl_clk_gen design loads

module test_null();

`include "test_base.inc"

initial begin
    $display("\n");
    $display("================================================================================");
    $display(" TEST: test_null (cl_clk_gen)");
    $display("================================================================================");

    // Power up with Clock Recipe A2 to set clk_extra_a2 = 125 MHz
    tb.power_up(.clk_recipe_a(ClockRecipe::A2));

    $display("[%t] Design powered up with Clock Recipe A2", $time);

    #500ns;

    // De-assert resets from aws_clk_gen
    aws_clkgen_dsrt_rst();

    $display("[%t] aws_clk_gen resets de-asserted", $time);

    #1000ns;

    tb.power_down();

    $display("\n[%t] Test completed", $time);
    report_pass_fail_status();

    $finish;
end

endmodule // test_null
