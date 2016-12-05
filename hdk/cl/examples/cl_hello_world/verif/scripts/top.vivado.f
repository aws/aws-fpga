## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

-define VIVADO_SIM

-sourcelibext .v
-sourcelibext .sv

-sourcelibdir ${CL_ROOT}/design
-sourcelibdir ${HDK_DIR}/common/shell_latest/design/mgt
-sourcelibdir ${SH_LIB_DIR}
-sourcelibdir ${SH_INF_DIR}

-include ${CL_ROOT}/verif/sv
-include ${SH_LIB_DIR}
-include ${SH_INF_DIR}

${CL_ROOT}/design/cl_hello_world_defines.vh
${CL_ROOT}/design/cl_hello_world.sv

-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f

${TEST_NAME}
