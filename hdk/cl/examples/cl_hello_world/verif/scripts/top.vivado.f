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

-include ${HDK_SHELL_DIR}/design/interfaces
-include ${CL_ROOT}/verif/sv

${CL_ROOT}/design/cl_hello_world_defines.vh

-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f

${CL_ROOT}/design/cl_hello_world.sv

${TEST_NAME}
