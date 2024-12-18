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

module test_hbm_perf32();

  import tb_type_defines_pkg::*;

  `include "base_test_utils.svh";

  initial begin

    automatic logic [31:0] selected_channels = 32'hFFFF_FFFF;
    automatic logic [3:0]  axlen = 4'hF;

    tb.power_up(.clk_recipe_a(ClockRecipe::A1),
                .clk_recipe_b(ClockRecipe::B0),
                .clk_recipe_c(ClockRecipe::C0));

    aws_clkgen_dsrt_rst();

    initialize_hbm();

    deselect_cl_tst_hw();

    program_cl_hbm_perf_kernel(.axlen(axlen));

    run_cl_hbm_perf_kernel_writes(.selected_channels(selected_channels));
    run_cl_hbm_perf_kernel_reads(.selected_channels(selected_channels));

    check_for_cl_hbm_perf_kernel_response_errors();
    print_cl_hbm_perf_kernel_latencies();

    print_cl_hbm_perf_kernel_bandwidth_performance(.selected_channels(selected_channels), .axlen(axlen));

    #500ns;
    tb.power_down();

    report_pass_fail_status();

    $finish;

   end
endmodule // test_hbm_perf32
