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

+define+QUESTA_SIM

+libext+.v
+libext+.sv
+libext+.svh

-y ${CL_ROOT}/../common/design
-y ${CL_ROOT}/design
-y ${SH_LIB_DIR}
-y ${SH_INF_DIR}
-y ${SH_SH_DIR}
-y ${HDK_SHELL_DESIGN_DIR}/ip/cl_debug_bridge/bd_0/hdl
-y ${HDK_SHELL_DESIGN_DIR}/ip/cl_debug_bridge/sim

+incdir+${CL_ROOT}/../common/design
+incdir+${CL_ROOT}/verif/sv
+incdir+${SH_LIB_DIR}
+incdir+${SH_INF_DIR}
+incdir+${SH_SH_DIR}
+incdir+${HDK_COMMON_DIR}/verif/include
+incdir+${HDK_SHELL_DESIGN_DIR}/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog
+incdir+${HDK_SHELL_DESIGN_DIR}/ip/axi_register_slice_light/hdl

${CL_ROOT}/../common/design/cl_common_defines.vh

${CL_ROOT}/design/cl_hello_world_defines.vh

+define+DISABLE_CHIPSCOPE_DEBUG

${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_xbar_0/sim/cl_axi_interconnect_xbar_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_s00_regslice_0/sim/cl_axi_interconnect_s00_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_m00_regslice_0/sim/cl_axi_interconnect_m00_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_m01_regslice_0/sim/cl_axi_interconnect_m01_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_m02_regslice_0/sim/cl_axi_interconnect_m02_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_m03_regslice_0/sim/cl_axi_interconnect_m03_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/hdl/cl_axi_interconnect.v
${SH_LIB_DIR}/../ip/axi_clock_converter_0/sim/axi_clock_converter_0.v
${SH_LIB_DIR}/../ip/dest_register_slice/sim/dest_register_slice.v
${SH_LIB_DIR}/../ip/src_register_slice/sim/src_register_slice.v
${SH_LIB_DIR}/../ip/axi_register_slice/sim/axi_register_slice.v
${SH_LIB_DIR}/../ip/axi_register_slice_light/sim/axi_register_slice_light.v



${CL_ROOT}/design/hello_world.sv
${CL_ROOT}/design/cl_hello_world_pkg.sv
${CL_ROOT}/design/cl_hello_world.sv

-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f

${TEST_NAME}
