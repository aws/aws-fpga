## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

+define+QUESTA_SIM
+define+CL_NAME=cl_hello_world
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

${CL_ROOT}/design/cl_hello_world.sv

-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f

${TEST_NAME}
