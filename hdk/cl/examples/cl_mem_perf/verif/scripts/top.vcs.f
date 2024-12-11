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

+define+CL_NAME=cl_mem_perf
+define+DISABLE_VJTAG_DEBUG

+incdir+$CL_DIR/verif/tests
-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f
${TEST_NAME}

+incdir+${CL_DIR}/design
${CL_DIR}/design/cl_mem_perf_defines.vh
${CL_DIR}/design/cl_axi_ctl.sv
${CL_DIR}/design/cl_kernel_ctl.sv
${CL_DIR}/design/cl_kernel_regs.sv
${CL_DIR}/design/cl_kernel_req.sv
${CL_DIR}/design/cl_clk_freq.sv
${CL_DIR}/design/cl_hbm_perf_kernel.sv
${CL_DIR}/design/cl_mem_hbm_axi4.sv
${CL_DIR}/design/cl_mem_hbm_wrapper.sv
${CL_DIR}/design/cl_mem_ocl_dec.sv
${CL_DIR}/design/cl_mem_pcis_dec.sv
${CL_DIR}/design/cl_mem_perf.sv

#
# RTL source from CL_DRAM_HBM_DMA
#
+incdir+$CL_DIR/../cl_dram_hbm_dma
${CL_DIR}/../cl_dram_hbm_dma/design/axil_slave.sv
${CL_DIR}/../cl_dram_hbm_dma/design/cl_tst_scrb.sv
${CL_DIR}/../cl_dram_hbm_dma/design/cl_tst.sv
${CL_DIR}/../cl_dram_hbm_dma/design/cl_int_tst.sv
${CL_DIR}/../cl_dram_hbm_dma/design/cl_dram_dma_pkg.sv
${CL_DIR}/../cl_dram_hbm_dma/design/cl_pcim_mstr.sv
${CL_DIR}/../cl_dram_hbm_dma/design/cl_ila.sv
${CL_DIR}/../cl_dram_hbm_dma/design/cl_vio.sv
${CL_DIR}/../cl_dram_hbm_dma/design/cl_int_slv.sv
${CL_DIR}/../cl_dram_hbm_dma/design/cl_sda_slv.sv
${CL_DIR}/../cl_dram_hbm_dma/design/cl_dram_dma_axi_mstr.sv
${CL_DIR}/../cl_dram_hbm_dma/design/mem_scrb.sv
