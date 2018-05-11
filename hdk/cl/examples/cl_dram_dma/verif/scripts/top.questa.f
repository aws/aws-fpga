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

-y ${CL_ROOT}/design
-y ${SH_LIB_DIR}
-y ${SH_INF_DIR}
-y ${HDK_SHELL_DESIGN_DIR}/sh_ddr/sim

+incdir+${CL_ROOT}/../common/design
+incdir+${CL_ROOT}/design
+incdir+${CL_ROOT}/verif/sv
+incdir+${SH_LIB_DIR}
+incdir+${SH_INF_DIR}
+incdir+${HDK_COMMON_DIR}/verif/include
+incdir+${CL_ROOT}/design/axi_crossbar_0
+incdir+${SH_LIB_DIR}/../ip/cl_axi_interconnect/ipshared/7e3a/hdl
+incdir+${HDK_SHELL_DESIGN_DIR}/sh_ddr/sim

-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f
${TEST_NAME}

${SH_LIB_DIR}/../ip/cl_axi_interconnect/ipshared/5235/hdl/axi_data_fifo_v2_1_vl_rfs.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ipshared/78eb/hdl/axi_crossbar_v2_1_vl_rfs.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_xbar_0/sim/cl_axi_interconnect_xbar_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_s00_regslice_0/sim/cl_axi_interconnect_s00_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_s01_regslice_0/sim/cl_axi_interconnect_s01_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_m00_regslice_0/sim/cl_axi_interconnect_m00_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_m01_regslice_0/sim/cl_axi_interconnect_m01_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_m02_regslice_0/sim/cl_axi_interconnect_m02_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_m03_regslice_0/sim/cl_axi_interconnect_m03_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/hdl/cl_axi_interconnect.v
${SH_LIB_DIR}/../ip/axi_clock_converter_0/hdl/axi_clock_converter_v2_1_vl_rfs.v
${SH_LIB_DIR}/../ip/axi_clock_converter_0/sim/axi_clock_converter_0.v
${SH_LIB_DIR}/../ip/dest_register_slice/sim/dest_register_slice.v
${SH_LIB_DIR}/../ip/src_register_slice/sim/src_register_slice.v
${SH_LIB_DIR}/../ip/axi_register_slice/hdl/axi_register_slice_v2_1_vl_rfs.v
${SH_LIB_DIR}/../ip/axi_register_slice/sim/axi_register_slice.v
${SH_LIB_DIR}/../ip/axi_register_slice_light/sim/axi_register_slice_light.v

${SH_LIB_DIR}/bram_2rw.sv
${SH_LIB_DIR}/flop_fifo.sv

+define+DISABLE_VJTAG_DEBUG
${CL_ROOT}/design/axil_slave.sv
${CL_ROOT}/design/cl_dram_dma_defines.vh
${CL_ROOT}/design/cl_tst_scrb.sv


${CL_ROOT}/design/cl_tst.sv

${CL_ROOT}/design/cl_int_tst.sv
${CL_ROOT}/design/cl_dram_dma_pkg.sv
${CL_ROOT}/design/cl_dma_pcis_slv.sv
${CL_ROOT}/design/cl_pcim_mstr.sv
${CL_ROOT}/design/cl_ila.sv
${CL_ROOT}/design/cl_vio.sv
${CL_ROOT}/design/cl_int_slv.sv
${CL_ROOT}/design/cl_ocl_slv.sv
${CL_ROOT}/design/cl_sda_slv.sv
${CL_ROOT}/design/cl_dram_dma_axi_mstr.sv
${CL_ROOT}/design/cl_dram_dma.sv

