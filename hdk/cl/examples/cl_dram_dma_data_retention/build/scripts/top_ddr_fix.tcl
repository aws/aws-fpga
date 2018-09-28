# Amazon FPGA Hardware Development Kit
#
# Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Amazon Software License (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#    http://aws.amazon.com/asl/
#
# or in the "license" file accompanying this file. This file is distributed on
# an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.

set_property STARTUP_WAIT TRUE [get_cells WRAPPER_INST/CL/SH_DDR/ddr_cores.DDR4_*/inst/u_ddr4_infrastructure/gen_mmcme4.u_mmcme_adv_inst]
set_property STARTUP_WAIT TRUE [get_cells {WRAPPER_INST/CL/SH_DDR/ddr_cores.DDR4_*/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/u_ddr4_phy_pll/plle_loop[*].gen_plle4.PLLE4_BASE_INST_OTHER}]

set_property BITSTREAM.STARTUP.LCK_CYCLE 2 [current_design]
set_property BITSTREAM.STARTUP.MATCH_CYCLE 1 [current_design]

set_property INIT 1'b0 [get_cells {WRAPPER_INST/CL/SH_DDR/ddr_cores.DDR4_0/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[6].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_BITSLICE_LOWER[4].GEN_RXTX_BITSLICE_EN.u_xiphy_bitslice_lower/xiphy_rxtx_bitslice}]
set_property INIT 1'b0 [get_cells {WRAPPER_INST/CL/SH_DDR/ddr_cores.DDR4_0/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[6].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_BITSLICE_LOWER[5].GEN_RXTX_BITSLICE_EN.u_xiphy_bitslice_lower/xiphy_rxtx_bitslice}]
set_property INIT 1'b0 [get_cells {WRAPPER_INST/CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[6].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_BITSLICE_UPPER[0].GEN_RXTX_BITSLICE_EN.u_xiphy_bitslice_upper/xiphy_rxtx_bitslice}]
set_property INIT 1'b0 [get_cells {WRAPPER_INST/CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[6].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_BITSLICE_UPPER[1].GEN_RXTX_BITSLICE_EN.u_xiphy_bitslice_upper/xiphy_rxtx_bitslice}]
set_property INIT 1'b0 [get_cells {WRAPPER_INST/CL/SH_DDR/ddr_cores.DDR4_2/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[5].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_BITSLICE_UPPER[4].GEN_RXTX_BITSLICE_EN.u_xiphy_bitslice_upper/xiphy_rxtx_bitslice}]
set_property INIT 1'b0 [get_cells {WRAPPER_INST/CL/SH_DDR/ddr_cores.DDR4_2/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[5].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_BITSLICE_UPPER[5].GEN_RXTX_BITSLICE_EN.u_xiphy_bitslice_upper/xiphy_rxtx_bitslice}]
#set_property INIT 1'b0 [get_cells {WRAPPER_INST/SH/SH/CL_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[8].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_BITSLICE_UPPER[0].GEN_RXTX_BITSLICE_EN.u_xiphy_bitslice_upper/xiphy_rxtx_bitslice}]
#set_property INIT 1'b0 [get_cells {WRAPPER_INST/SH/SH/CL_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[8].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_BITSLICE_UPPER[1].GEN_RXTX_BITSLICE_EN.u_xiphy_bitslice_upper/xiphy_rxtx_bitslice}]
set_property INIT 1'b0 [get_cells {WRAPPER_INST/CL/SH_DDR/ddr_cores.DDR4_0/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[6].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_BITSLICE_LOWER[4].GEN_RXTX_BITSLICE_EN.u_xiphy_bitslice_lower/xiphy_rxtx_bitslice}]
set_property INIT 1'b0 [get_cells {WRAPPER_INST/CL/SH_DDR/ddr_cores.DDR4_0/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[6].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_BITSLICE_LOWER[5].GEN_RXTX_BITSLICE_EN.u_xiphy_bitslice_lower/xiphy_rxtx_bitslice}]
set_property INIT 1'b0 [get_cells {WRAPPER_INST/CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[6].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_BITSLICE_UPPER[0].GEN_RXTX_BITSLICE_EN.u_xiphy_bitslice_upper/xiphy_rxtx_bitslice}]
set_property INIT 1'b0 [get_cells {WRAPPER_INST/CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[6].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_BITSLICE_UPPER[1].GEN_RXTX_BITSLICE_EN.u_xiphy_bitslice_upper/xiphy_rxtx_bitslice}]
set_property INIT 1'b0 [get_cells {WRAPPER_INST/CL/SH_DDR/ddr_cores.DDR4_2/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[5].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_BITSLICE_UPPER[4].GEN_RXTX_BITSLICE_EN.u_xiphy_bitslice_upper/xiphy_rxtx_bitslice}]
set_property INIT 1'b0 [get_cells {WRAPPER_INST/CL/SH_DDR/ddr_cores.DDR4_2/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[5].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_BITSLICE_UPPER[5].GEN_RXTX_BITSLICE_EN.u_xiphy_bitslice_upper/xiphy_rxtx_bitslice}]
#set_property INIT 1'b0 [get_cells {WRAPPER_INST/SH/SH/CL_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[8].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_BITSLICE_UPPER[0].GEN_RXTX_BITSLICE_EN.u_xiphy_bitslice_upper/xiphy_rxtx_bitslice}]
#set_property INIT 1'b0 [get_cells {WRAPPER_INST/SH/SH/CL_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy/inst/generate_block1.u_ddr_xiphy/byte_num[8].xiphy_byte_wrapper.u_xiphy_byte_wrapper/I_BITSLICE_UPPER[1].GEN_RXTX_BITSLICE_EN.u_xiphy_bitslice_upper/xiphy_rxtx_bitslice}]

