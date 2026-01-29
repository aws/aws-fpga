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

+define+VCS_SIM
+define+CARD_1=card
+define+RANDOMIZE_MEM_INIT
+define+RANDOMIZE_REG_INIT
+define+RANDOMIZE_GARBAGE_ASSIGN
+define+RANDOMIZE_INVALID_ASSIGN
+define+PRINTF_COND=1'b1
+define+STOP_COND=1'b1
+libext+.v
+libext+.sv
+libext+.svh

-y ${CL_ROOT}/../common/design
-y ${CL_ROOT}/design
-y ${CL_ROOT}/design/ila_files
-y ${CL_ROOT}/verif/sv
-y ${SH_LIB_DIR}
-y ${SH_INF_DIR}
-y ${SH_SH_DIR}
-y ${HDK_SHELL_DESIGN_DIR}/ip/cl_debug_bridge/bd_0/hdl
-y ${HDK_SHELL_DESIGN_DIR}/ip/cl_debug_bridge/sim
-y ${HDK_SHELL_DESIGN_DIR}/sh_ddr/sim

+incdir+${CL_ROOT}/../common/design
+incdir+${CL_ROOT}/design
+incdir+${CL_ROOT}/design/ila_files
+incdir+${CL_ROOT}/verif/sv
+incdir+${SH_LIB_DIR}
+incdir+${SH_INF_DIR}
+incdir+${SH_SH_DIR}
+incdir+${HDK_COMMON_DIR}/verif/include
+incdir+${HDK_SHELL_DESIGN_DIR}/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog
+incdir+${HDK_SHELL_DESIGN_DIR}/ip/axi_register_slice_light/hdl
+incdir+${HDK_SHELL_DESIGN_DIR}/ip/cl_axi_interconnect/ipshared/7e3a/hdl
+incdir+${HDK_SHELL_DESIGN_DIR}/sh_ddr/sim

${CL_ROOT}/../common/design/cl_common_defines.vh
${CL_ROOT}/design/cl_firesim_defines.vh
${HDK_SHELL_DESIGN_DIR}/ip/ila_vio_counter/sim/ila_vio_counter.v
${HDK_SHELL_DESIGN_DIR}/ip/ila_0/sim/ila_0.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_debug_bridge/bd_0/sim/bd_a493.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_debug_bridge/bd_0/ip/ip_0/sim/bd_a493_xsdbm_0.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/xsdbm_v3_0_vl_rfs.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/ltlib_v1_0_vl_rfs.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_debug_bridge/bd_0/ip/ip_1/sim/bd_a493_lut_buffer_0.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_debug_bridge/bd_0/ip/ip_1/hdl/lut_buffer_v2_0_vl_rfs.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_debug_bridge/bd_0/hdl/bd_a493_wrapper.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_debug_bridge/sim/cl_debug_bridge.v
${HDK_SHELL_DESIGN_DIR}/ip/vio_0/sim/vio_0.v
${HDK_SHELL_DESIGN_DIR}/ip/axi_register_slice_light/sim/axi_register_slice_light.v
${HDK_SHELL_DESIGN_DIR}/ip/axi_register_slice/sim/axi_register_slice.v
${HDK_SHELL_DESIGN_DIR}/ip/axi_clock_converter_0/hdl/fifo_generator_v13_2_rfs.v
${HDK_SHELL_DESIGN_DIR}/ip/axi_register_slice_light/hdl/axi_register_slice_v2_1_vl_rfs.v
${HDK_SHELL_DESIGN_DIR}/ip/axi_register_slice_light/hdl/axi_infrastructure_v1_1_vl_rfs.v
${HDK_SHELL_DESIGN_DIR}/ip/axi_clock_converter_0/hdl/axi_clock_converter_v2_1_vl_rfs.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_axi_interconnect/sim/cl_axi_interconnect.v
${SH_LIB_DIR}/../ip/axi_clock_converter_0/sim/axi_clock_converter_0.v
${CL_ROOT}/ip/axi_clock_converter_dramslim/sim/axi_clock_converter_dramslim.v
${CL_ROOT}/ip/axi_clock_converter_oclnew/sim/axi_clock_converter_oclnew.v
${CL_ROOT}/ip/axi_clock_converter_oclnew/hdl/axi_clock_converter_v2_1_vl_rfs.v
${CL_ROOT}/ip/axi_clock_converter_512_wide/sim/axi_clock_converter_512_wide.v
${CL_ROOT}/ip/axi_clock_converter_512_pcim/sim/axi_clock_converter_512_pcim.v
${CL_ROOT}/ip/clk_wiz_0_firesim/clk_wiz_0_firesim_sim_netlist.v
${CL_ROOT}/ip/axi_dwidth_converter_0/sim/axi_dwidth_converter_0.v
${CL_ROOT}/ip/axi_dwidth_converter_0/hdl/axi_dwidth_converter_v2_1_vl_rfs.v
${CL_ROOT}/ip/axi_dwidth_converter_0/hdl/axi_register_slice_v2_1_vl_rfs.v
${CL_ROOT}/design/FireSim-generated.sv
${CL_ROOT}/design/FireSim-generated.defines.vh
${CL_ROOT}/design/cl_firesim.sv

-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f

${TEST_NAME}
