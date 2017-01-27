## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

+define+VCS_SIM

+libext+.v
+libext+.sv
+libext+.svh

-y ${CL_ROOT}/design
-y ${SH_LIB_DIR}
-y ${SH_INF_DIR}

+incdir+${CL_ROOT}/verif/sv
+incdir+${SH_LIB_DIR}
+incdir+${SH_INF_DIR}
+incdir+${HDK_COMMON_DIR}/verif/include
+incdir+${CL_ROOT}/design/axi_crossbar_1/hdl  

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
