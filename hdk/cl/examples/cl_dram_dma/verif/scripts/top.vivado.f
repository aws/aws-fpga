## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

--define VIVADO_SIM

--sourcelibext .v
--sourcelibext .sv
--sourcelibext .svh

--sourcelibdir ${CL_ROOT}/design
--sourcelibdir ${SH_LIB_DIR}
--sourcelibdir ${SH_INF_DIR}

--include ${CL_ROOT}/verif/sv
--include ${SH_LIB_DIR}
--include ${SH_INF_DIR}
--include ${HDK_COMMON_DIR}/verif/include
--include ${CL_ROOT}/design/axi_crossbar_0
--include ${CL_ROOT}/design/src_register_slice
--include ${CL_ROOT}/design/dest_register_slice
--include ${SH_LIB_DIR}/../ip/cl_axi_interconnect/ipshared/7e3a/hdl


${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_xbar_0/sim/cl_axi_interconnect_xbar_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_s00_regslice_0/sim/cl_axi_interconnect_s00_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_m00_regslice_0/sim/cl_axi_interconnect_m00_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_m01_regslice_0/sim/cl_axi_interconnect_m01_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_m02_regslice_0/sim/cl_axi_interconnect_m02_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/ip/cl_axi_interconnect_m03_regslice_0/sim/cl_axi_interconnect_m03_regslice_0.v
${SH_LIB_DIR}/../ip/cl_axi_interconnect/hdl/cl_axi_interconnect.v
${SH_LIB_DIR}/../ip/axi_clock_converter_0/sim/axi_clock_converter_0.v

+define_DISABLE_CHIPSCOPE_DEBUG
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
