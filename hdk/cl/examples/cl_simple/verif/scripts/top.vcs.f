## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

+define+VCS_SIM
+define+CL_NAME=cl_simple
+define+FPGA_LESS_RST
+define+NO_XDMA

+libext+.v
+libext+.sv

-y ${CL_ROOT}/design
-y ${HDK_DIR}/common/shell_latest/design/mgt
-y ${SH_LIB_DIR}
-y ${SH_INF_DIR}

+incdir+${CL_ROOT}/verif/sv
+incdir+${SH_LIB_DIR}
+incdir+${SH_INF_DIR}

${CL_ROOT}/design/cl_tst_scrb.sv
${CL_ROOT}/design/cl_tst.sv
${CL_ROOT}/design/cl_int_tst.sv
${CL_ROOT}/design/cl_simple.sv

-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f

${TEST_NAME}