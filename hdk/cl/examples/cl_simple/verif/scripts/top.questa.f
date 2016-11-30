## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

+define+QUESTA_SIM

+define+NO_XDMA

+libext+.v
+libext+.sv

+incdir+${CL_ROOT}/design
+incdir+${CL_ROOT}/verif/sv
+incdir+${SH_LIB_DIR}
+incdir+${SH_INF_DIR}

-y ${CL_ROOT}/design
-y ${HDK_DIR}/common/shell_latest/design/mgt
-y ${HDK_DIR}/top/vu9p/design/sh
-y ${SH_LIB_DIR}

-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f

${HDK_DIR}/top/vu9p/design/sh/sh_ddr.sv

${CL_ROOT}/design/cl_tst_scrb.sv
${CL_ROOT}/design/cl_tst.sv
${CL_ROOT}/design/cl_int_tst.sv
${CL_ROOT}/design/cl_simple.sv

${TEST_NAME}
