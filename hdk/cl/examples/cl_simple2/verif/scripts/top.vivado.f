## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

-define NO_XDMA

-sourcelibext .v
-sourcelibext .sv

-sourcelibdir ${CL_ROOT}/design
-sourcelibdir ${HDK_DIR}/top/vu9p/design/mgt
-sourcelibdir ${HDK_DIR}/top/vu9p/design/sh
-sourcelibdir ${SH_LIB_DIR}

-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f

${HDK_DIR}/top/vu9p/design/sh/sh_ddr.sv

${CL_ROOT}/design/cl_tst_scrb.sv
${CL_ROOT}/design/cl_tst.sv
${CL_ROOT}/design/cl_int_tst.sv
${CL_ROOT}/design/cl_simple.sv
${CL_ROOT}/verif/tests/test_peek_poke.sv
