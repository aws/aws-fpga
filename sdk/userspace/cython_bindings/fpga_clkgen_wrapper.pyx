# Cython Code File for FPGA ClkGen library

from fpga_clkgen cimport *
from fpga_mgmt cimport *
from fpga_utils import check_return_code
from typing import Dict, Any


class FpgaClkgen:
    def get_dynamic(self, slot_id: int) -> Dict[str, Any]:
        cdef fpga_clkgen_info info
        ret = aws_clkgen_get_dynamic(slot_id, &info)
        check_return_code(ret, "get dynamic", slot_id)
        return info

    def set_recipe(self, slot_id: int, clk_a_recipe: uint32_t, clk_b_recipe: uint32_t, clk_c_recipe: uint32_t, clk_hbm_recipe: uint32_t, reset: uint32_t) -> None:
        ret = aws_clkgen_set_recipe(slot_id, clk_a_recipe, clk_b_recipe, clk_c_recipe, clk_hbm_recipe, reset)
        check_return_code(ret, "set recipe", slot_id)

    def set_dynamic(self, slot_id: int, clk_a_freq: uint32_t, clk_b_freq: uint32_t, clk_c_freq: uint32_t, clk_hbm_freq: uint32_t, reset: uint32_t) -> None:
        ret = aws_clkgen_set_dynamic(slot_id, clk_a_freq, clk_b_freq, clk_c_freq, clk_hbm_freq, reset)
        check_return_code(ret, "set dynamic", slot_id)
