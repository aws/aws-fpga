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


`include "common_base_test.svh"
`include "cl_clk_gen_defines.vh"
`include "aws_clk_gen_utils.svh"

`ifndef CL_CLK_GEN_TEST_BASE
`define CL_CLK_GEN_TEST_BASE
import tb_type_defines_pkg::*;

//==============================================================================
// Helper Tasks - Register Access via OCL
//==============================================================================

task write_operand_a(input logic[31:0] data);
    tb.poke_ocl(.addr(`ADDR_OPERAND_A), .data(data));
endtask

task write_operand_b(input logic[31:0] data);
    tb.poke_ocl(.addr(`ADDR_OPERAND_B), .data(data));
endtask

task read_sum(output logic[31:0] data);
    logic[63:0] rdata;
    tb.peek_ocl(.addr(`ADDR_SUM), .data(rdata));
    data = rdata[31:0];
endtask

task read_carry(output logic[31:0] data);
    logic[63:0] rdata;
    tb.peek_ocl(.addr(`ADDR_CARRY), .data(rdata));
    data = rdata[31:0];
endtask

task trigger_addition();
    tb.poke_ocl(.addr(`ADDR_CONTROL_STATUS), .data(32'h00000001));
endtask

task perform_addition(
    input logic[31:0] a,
    input logic[31:0] b,
    output logic[31:0] sum,
    output logic[31:0] carry
);
    logic[63:0] rdata;
    logic[31:0] status;
    int poll_count;

    write_operand_a(a);
    write_operand_b(b);
    trigger_addition();

    // Poll ready flag (mirrors the software cl_add() polling loop)
    status = 32'h0;
    poll_count = 0;
    while (!status[1] && poll_count < 100) begin
        tb.peek_ocl(.addr(`ADDR_CONTROL_STATUS), .data(rdata));
        status = rdata[31:0];
        poll_count++;
    end

    if (!status[1]) begin
        $error("[%t] Timeout waiting for ready flag in perform_addition", $time);
        error_count++;
    end

    read_sum(sum);
    read_carry(carry);
endtask

task perform_and_check_addition(
    input logic[31:0] a,
    input logic[31:0] b,
    input logic[31:0] expected_sum,
    input logic[31:0] expected_carry,
    input string test_name
);
    logic[31:0] actual_sum, actual_carry;

    $display("[%t] TEST: %s", $time, test_name);
    $display("        Operands: 0x%08x + 0x%08x", a, b);

    perform_addition(a, b, actual_sum, actual_carry);

    $display("        Expected: sum=0x%08x, carry=0x%08x", expected_sum, expected_carry);
    $display("        Actual:   sum=0x%08x, carry=0x%08x", actual_sum, actual_carry);

    if (actual_sum !== expected_sum) begin
        $error("[%t] ERROR: %s - sum mismatch", $time, test_name);
        error_count++;
    end
    if (actual_carry !== expected_carry) begin
        $error("[%t] ERROR: %s - carry mismatch", $time, test_name);
        error_count++;
    end
    if (actual_sum === expected_sum && actual_carry === expected_carry)
        $display("        PASS: %s", test_name);
endtask

`endif // CL_CLK_GEN_TEST_BASE
