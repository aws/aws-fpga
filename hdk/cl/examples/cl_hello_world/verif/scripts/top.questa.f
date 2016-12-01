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
+incdir+${HDK_SHELL_DIR}/design/interfaces

-y ${CL_ROOT}/design
-y ${HDK_DIR}/common/shell_latest/design/mgt
-y ${HDK_SHELL_DIR}/design/interfaces
-y ${SH_LIB_DIR}
-y ${SH_INF_DIR}

${CL_ROOT}/design/cl_hello_world_defines.vh

-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f

${CL_ROOT}/design/cl_hello_world.sv

${TEST_NAME}
