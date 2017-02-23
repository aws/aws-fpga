## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

+define+QUESTA_SIM

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
+incdir+${CL_ROOT}/design/axi_crossbar_0  
+incdir+${CL_ROOT}/design/src_register_slice  
+incdir+${CL_ROOT}/design/dest_register_slice

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
