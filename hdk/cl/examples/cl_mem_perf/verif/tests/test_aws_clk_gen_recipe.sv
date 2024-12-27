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


module test_aws_clk_gen_recipe();

  import tb_type_defines_pkg::*;

  `include "base_test_utils.svh";

  initial begin

    static int freq_a   = 87;
    static int freq_b   = 125;
    static int freq_c   = 318;
    static int freq_hbm = 437;

    // Please refer to `$AWS_FPGA_REPO_DIR/sdk/userspace/include/fpga_clkgen.h` for more information
    // Default configuration is A1, B2, C0, H2
    clk default_clock_frequencies [10:0] = '{
        '{"clk_hbm_ref",  100, `FREQ_CTR_9},
        '{"clk_hbm_axi",  450, `FREQ_CTR_8},
        '{"clk_extra_c1", 400, `FREQ_CTR_7},
        '{"clk_extra_c0", 300, `FREQ_CTR_6},
        '{"clk_extra_b1", 225, `FREQ_CTR_5},
        '{"clk_extra_b0", 450, `FREQ_CTR_4},
        '{"clk_extra_a3", 500, `FREQ_CTR_3},
        '{"clk_extra_a2", 375, `FREQ_CTR_2},
        '{"clk_extra_a1", 125, `FREQ_CTR_1},
        '{"clk_main_a0",  250, `FREQ_CTR_0},
        '{"reference",    100, `REF_FREQ_CTR}
    }; // Reverse order so that the ref_clk is at 0 and clk_hbm_ref is at 9

    clk modified_clock_frequencies [10:0] = '{
        '{"clk_hbm_ref",  100, `FREQ_CTR_9},
        '{"clk_hbm_axi",  freq_hbm, `FREQ_CTR_8},
        '{"clk_extra_c1", 105, `FREQ_CTR_7},
        '{"clk_extra_c0", freq_c, `FREQ_CTR_6},
        '{"clk_extra_b1", 83, `FREQ_CTR_5},
        '{"clk_extra_b0", freq_b, `FREQ_CTR_4},
        '{"clk_extra_a3", 58, `FREQ_CTR_3},
        '{"clk_extra_a2", 58, `FREQ_CTR_2},
        '{"clk_extra_a1", freq_a, `FREQ_CTR_1},
        '{"clk_main_a0",  250, `FREQ_CTR_0},
        '{"reference",    100, `REF_FREQ_CTR}
    }; // Reverse order so that the ref_clk is at 0 and clk_hbm_ref is at 9

    tb.power_up(.clk_recipe_a(ClockRecipe::A1),
                .clk_recipe_b(ClockRecipe::B0),
                .clk_recipe_c(ClockRecipe::C0));

    #500ns;

    aws_clkgen_dsrt_rst();

    // Toggle reset per smartconnect IP requirement
    aws_clkgen_asrt_rst();
    #500ns;
    aws_clkgen_dsrt_rst();

    compare_cl_clk_freq(default_clock_frequencies);

    // Please refer to `$AWS_FPGA_REPO_DIR/sdk/userspace/include/fpga_clkgen.*` for system clock frequencies
    // Please refer to `$AWS_FPGA_REPO_DIR/hdk/common/verif/include/aws_clk_gen_utils.svh` for TB clock frequencies
    aws_clkgen_dynamic_freq(.freq_clk_a(freq_a), .freq_clk_b(freq_b), .freq_clk_c(freq_c), .freq_clk_hbm(freq_hbm), .reset(0));
    compare_cl_clk_freq(modified_clock_frequencies);

    aws_clkgen_dynamic_freq(.freq_clk_a(0), .freq_clk_b(0), .freq_clk_c(0), .freq_clk_hbm(0), .reset(1));
    compare_cl_clk_freq(default_clock_frequencies);

    #500ns;
    tb.power_down();

    report_pass_fail_status();

    $finish;

  end // initial begin

endmodule // test_aws_clk_gen_recipe
