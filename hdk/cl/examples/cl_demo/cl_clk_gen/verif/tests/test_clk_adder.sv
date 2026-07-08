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

// Test CLK Adder
//
// Demonstrates:
// 1. Power up with Clock Recipe A2 (clk_extra_a2 = 125 MHz)
// 2. Configure aws_clk_gen via SDA interface (de-assert resets)
// 3. Adder operations across clock domain crossing
//    (OCL @ clk_main_a0 250 MHz -> adder @ clk_extra_a1 15.625 MHz)

module test_clk_adder();

`include "test_base.inc"

initial begin
    $display("\n");
    $display("================================================================================");
    $display(" TEST: test_clk_adder (cl_clk_gen)");
    $display(" Demonstrates aws_clk_gen + clock domain crossing with AXI-Lite");
    $display("================================================================================");

    // Power up with Clock Recipe A2: clk_extra_a2 = 125 MHz
    $display("\n[%t] Power up with Clock Recipe A2", $time);
    tb.power_up(.clk_recipe_a(ClockRecipe::A2));
    #500ns;

    // De-assert aws_clk_gen resets via SDA interface
    $display("\n[%t] De-assert aws_clk_gen resets via SDA", $time);
    aws_clkgen_dsrt_rst();
    #500ns;

    // Adder operations across clock domains
    $display("\n[%t] Adder operations across clock domains", $time);

    perform_and_check_addition(
        .a(32'h0000_0100),
        .b(32'h0000_0200),
        .expected_sum(32'h0000_0300),
        .expected_carry(32'h0000_0000),
        .test_name("Basic addition: 0x100 + 0x200")
    );
    #200ns;

    perform_and_check_addition(
        .a(32'hFFFF_FFFF),
        .b(32'h0000_0001),
        .expected_sum(32'h0000_0000),
        .expected_carry(32'h0000_0001),
        .test_name("Addition with carry: 0xFFFFFFFF + 0x1")
    );
    #200ns;

    perform_and_check_addition(
        .a(32'hFFFF_FFFF),
        .b(32'hFFFF_FFFF),
        .expected_sum(32'hFFFF_FFFE),
        .expected_carry(32'h0000_0001),
        .test_name("Max+Max: 0xFFFFFFFF + 0xFFFFFFFF")
    );
    #200ns;

    perform_and_check_addition(
        .a(32'h0000_0000),
        .b(32'h0000_0000),
        .expected_sum(32'h0000_0000),
        .expected_carry(32'h0000_0000),
        .test_name("Zero addition: 0x0 + 0x0")
    );

    #1000ns;
    tb.power_down();

    $display("\n[%t] Test completed", $time);
    report_pass_fail_status();

    $finish;
end

endmodule // test_clk_adder
