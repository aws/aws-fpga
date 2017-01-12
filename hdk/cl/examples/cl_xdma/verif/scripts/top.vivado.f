## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

-define VIVADO_SIM

-sourcelibext .v
-sourcelibext .sv

-sourcelibdir ${CL_ROOT}/design
-sourcelibdir ${CL_ROOT}/design/axi_crossbar_1/hdl  
-sourcelibdir ${SH_LIB_DIR}
-sourcelibdir ${SH_INF_DIR}

-include ${CL_ROOT}/verif/sv
-include ${SH_LIB_DIR}
-include ${SH_INF_DIR}

${CL_ROOT}/design/axi_crossbar_1/synth/axi_crossbar_1.v
${CL_ROOT}/design/axi_crossbar_1/hdl/axi_crossbar_v2_1_vl_rfs.v
${CL_ROOT}/design/axi_crossbar_1/hdl/axi_data_fifo_v2_1_vl_rfs.v
${CL_ROOT}/design/axi_crossbar_1/hdl/axi_infrastructure_v1_1_vl_rfs.v
${CL_ROOT}/design/axi_crossbar_1/hdl/axi_register_slice_v2_1_vl_rfs.v
${CL_ROOT}/design/axi_crossbar_1/hdl/generic_baseblocks_v2_1_vl_rfs.v
${CL_ROOT}/design/axi_crossbar_1/hdl/fifo_generator_v13_1_rfs.v

${CL_ROOT}/design/cl_xdma_defines.vh
${CL_ROOT}/design/cl_tst_scrb.sv
${CL_ROOT}/design/cl_tst.sv
${CL_ROOT}/design/cl_int_tst.sv
${CL_ROOT}/design/cl_xdma.sv

-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f

${TEST_NAME}
