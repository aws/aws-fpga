## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

-define NO_XDMA

-sourcelibext .v
-sourcelibext .sv

-sourcelibdir ${CL_ROOT}/design
-sourcelibdir ${HDK_DIR}/common/shell_latest/design/mgt
-sourcelibdir ${SH_LIB_DIR}
-sourcelibdir ${SH_INF_DIR}

-include ${CL_ROOT}/verif/sv
-include ${SH_INF_DIR}

-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f

${CL_ROOT}/design/cl_tst_scrb.sv
${CL_ROOT}/design/cl_tst.sv
${CL_ROOT}/design/cl_int_tst.sv
${CL_ROOT}/design/cl_simple.sv

${TEST_NAME}

