# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
# =============================================================================


-define CL_NAME=cl_firesim
// -define NO_SDE_DEBUG_ILA
-define DISABLE_VJTAG_DEBUG

-include $CL_DIR/verif/tests
-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f
${TEST_NAME}

// -include ${CL_DIR}/../common/design
// -include ${CL_DIR}/../common/design/cl_common_defines.vh

-include $CL_DIR/design
${CL_DIR}/design/cl_firesim_defines.vh
${CL_DIR}/design/cl_firesim.sv
${CL_DIR}/design/cl_id_defines.vh
${CL_DIR}/design/FireSim-generated.defines.vh
${CL_DIR}/design/FireSim-generated.sv
// ${CL_DIR}/design/FireSim-generated.implementation.xdc
// ${CL_DIR}/design/FireSim-generated.synthesis.xdc

-include $CL_DIR/ip
${CL_DIR}/ip/axi_clock_converter_512_pcim/axi_clock_converter_512_pcim_sim_netlist.v
${CL_DIR}/ip/axi_clock_converter_512_wide/axi_clock_converter_512_wide_sim_netlist.v
${CL_DIR}/ip/axi_clock_converter_dramslim/axi_clock_converter_dramslim_sim_netlist.v
${CL_DIR}/ip/axi_clock_converter_oclnew/axi_clock_converter_oclnew_sim_netlist.v
${CL_DIR}/ip/axi_dwidth_converter_0/axi_dwidth_converter_0_sim_netlist.v
${CL_DIR}/ip/clk_wiz_0_firesim/clk_wiz_0_firesim_sim_netlist.v

-include $CL_DIR/../../examples/cl_dram_hbm_dma
${CL_DIR}/../../examples/cl_dram_hbm_dma/design/axil_slave.sv
${CL_DIR}/../../examples/cl_dram_hbm_dma/design/cl_tst_scrb.sv
${CL_DIR}/../../examples/cl_dram_hbm_dma/design/cl_tst.sv
${CL_DIR}/../../examples/cl_dram_hbm_dma/design/cl_int_tst.sv
${CL_DIR}/../../examples/cl_dram_hbm_dma/design/cl_dram_dma_pkg.sv
${CL_DIR}/../../examples/cl_dram_hbm_dma/design/cl_pcim_mstr.sv
${CL_DIR}/../../examples/cl_dram_hbm_dma/design/cl_ila.sv
${CL_DIR}/../../examples/cl_dram_hbm_dma/design/cl_vio.sv
${CL_DIR}/../../examples/cl_dram_hbm_dma/design/cl_int_slv.sv
${CL_DIR}/../../examples/cl_dram_hbm_dma/design/cl_sda_slv.sv
${CL_DIR}/../../examples/cl_dram_hbm_dma/design/cl_dram_dma_axi_mstr.sv
${CL_DIR}/../../examples/cl_dram_hbm_dma/design/mem_scrb.sv