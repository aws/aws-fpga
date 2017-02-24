## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

-define VIVADO_SIM

-sourcelibext .v
-sourcelibext .sv
-sourcelibext .svh

-sourcelibdir ${CL_ROOT}/design
-sourcelibdir ${SH_LIB_DIR}
-sourcelibdir ${SH_INF_DIR}

-include ${CL_ROOT}/verif/sv
-include ${SH_LIB_DIR}
-include ${SH_INF_DIR}
-include ${HDK_COMMON_DIR}/verif/include
-include ${CL_ROOT}/design/axi_crossbar_0
-include ${CL_ROOT}/design/src_register_slice
-include ${CL_ROOT}/design/dest_register_slice


${CL_ROOT}/design/axi_crossbar_0/axi_crossbar_0.v
${CL_ROOT}/design/axi_crossbar_0/axi_crossbar_v2_1_vl_rfs.v
${CL_ROOT}/design/axi_crossbar_0/axi_data_fifo_v2_1_vl_rfs.v
${CL_ROOT}/design/axi_crossbar_0/axi_infrastructure_v1_1_vl_rfs.v
${CL_ROOT}/design/axi_crossbar_0/axi_register_slice_v2_1_vl_rfs.v
${CL_ROOT}/design/axi_crossbar_0/generic_baseblocks_v2_1_vl_rfs.v
${CL_ROOT}/design/axi_crossbar_0/fifo_generator_v13_1_rfs.v

${CL_ROOT}/design/axil_slave.sv
${CL_ROOT}/design/cl_xdma_defines.vh
${CL_ROOT}/design/cl_tst_scrb.sv
${CL_ROOT}/design/cl_tst.sv
${CL_ROOT}/design/cl_int_tst.sv
${CL_ROOT}/design/cl_xdma.sv

${CL_ROOT}/design/src_register_slice/src_register_slice.v
${CL_ROOT}/design/dest_register_slice/dest_register_slice.v

-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f

${TEST_NAME}
