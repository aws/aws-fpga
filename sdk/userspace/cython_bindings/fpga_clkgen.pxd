# Cython Header File for FPGA Clkgen Functions

from libc.stdint cimport uint32_t

# fpga_clkgen.pxd
cdef extern from "fpga_clkgen.h":

    struct fpga_clkgen_group:
        double[3] clocks

    struct fpga_clkgen_info:
        fpga_clkgen_group clock_group_a
        fpga_clkgen_group clock_group_b
        fpga_clkgen_group clock_group_c
        fpga_clkgen_group clock_group_hbm

    int aws_clkgen_get_dynamic(int slot_id, fpga_clkgen_info* info)
    int aws_clkgen_set_recipe(int slot_id, uint32_t clk_a_recipe, uint32_t clk_b_recipe, uint32_t clk_c_recipe, uint32_t clk_hbm_recipe, uint32_t reset);
    int aws_clkgen_set_dynamic(int slot_id, uint32_t clk_a_freq, uint32_t clk_b_freq, uint32_t clk_c_freq, uint32_t clk_hbm_freq, uint32_t reset);
