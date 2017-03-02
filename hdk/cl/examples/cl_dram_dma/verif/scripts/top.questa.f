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

${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_xbar_0/sim/cl_axi_interconnect_xbar_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_s00_regslice_0/sim/cl_axi_interconnect_s00_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_m00_regslice_0/sim/cl_axi_interconnect_m00_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_m01_regslice_0/sim/cl_axi_interconnect_m01_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_m02_regslice_0/sim/cl_axi_interconnect_m02_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_m03_regslice_0/sim/cl_axi_interconnect_m03_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/hdl/cl_axi_interconnect.v


${CL_ROOT}/design/axil_slave.sv
${CL_ROOT}/design/cl_dram_dma_defines.vh
${CL_ROOT}/design/cl_tst_scrb.sv
${CL_ROOT}/design/cl_tst.sv
${CL_ROOT}/design/cl_int_tst.sv
${CL_ROOT}/design/cl_dram_dma_pkg.sv
${CL_ROOT}/design/cl_dma_pcis_slv.sv
${CL_ROOT}/design/cl_pcim_mstr.sv
${CL_ROOT}/design/cl_ila.sv
${CL_ROOT}/design/cl_vio.sv
${CL_ROOT}/design/cl_int_slv.sv
${CL_ROOT}/design/cl_ocl_slv.sv
${CL_ROOT}/design/cl_sda_slv.sv
${CL_ROOT}/design/cl_dram_dma.sv

${CL_ROOT}/design/src_register_slice/src_register_slice.v
${CL_ROOT}/design/dest_register_slice/dest_register_slice.v

-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f

${TEST_NAME}
