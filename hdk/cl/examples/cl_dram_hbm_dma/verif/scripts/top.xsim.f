# Amazon FPGA Hardware Development Kit
#
# Copyright 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

-define CL_NAME=cl_dram_hbm_dma
-define DISABLE_VJTAG_DEBUG

-include $CL_DIR/verif/tests
-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f
${TEST_NAME}

-include ${CL_DIR}/design
${CL_DIR}/design/cl_dram_dma_defines.vh
${CL_DIR}/design/axil_slave.sv
${CL_DIR}/design/mem_scrb.sv
${CL_DIR}/design/cl_tst_scrb.sv
${CL_DIR}/design/cl_tst.sv
${CL_DIR}/design/cl_int_tst.sv
${CL_DIR}/design/cl_dram_dma_pkg.sv
${CL_DIR}/design/cl_dma_pcis_slv.sv
${CL_DIR}/design/cl_pcim_mstr.sv
${CL_DIR}/design/cl_ila.sv
${CL_DIR}/design/cl_vio.sv
${CL_DIR}/design/cl_int_slv.sv
${CL_DIR}/design/cl_ocl_slv.sv
${CL_DIR}/design/cl_sda_slv.sv
${CL_DIR}/design/cl_hbm_axi4.sv
${CL_DIR}/design/cl_hbm_wrapper.sv
${CL_DIR}/design/cl_dram_dma_axi_mstr.sv
${CL_DIR}/design/cl_dram_hbm_dma.sv
