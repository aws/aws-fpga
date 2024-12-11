# Amazon FPGA Hardware Development Kit
#
# Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Amazon Software License (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#    http://aws.amazon.com/asl/
#
# or in the "license" file accompanying this file. This file is distributed on
# an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.

--define VIVADO_SIM

--sourcelibext .v
--sourcelibext .sv
--sourcelibext .svh

--sourcelibdir ${CL_ROOT}/design
--sourcelibdir ${SH_LIB_DIR}
--sourcelibdir ${SH_INF_DIR}
--sourcelibdir ${HDK_SHELL_DESIGN_DIR}/sh_ddr/sim

--include ${CL_ROOT}/../common/design
--include ${CL_ROOT}/design
--include ${CL_ROOT}/verif/sv

--include ${SH_LIB_DIR}
--include ${SH_INF_DIR}
--include ${HDK_COMMON_DIR}/verif/include
--include ${HDK_COMMON_DIR}/lib
--include ${HDK_SHELL_DESIGN_DIR}/ip/cl_debug_bridge/bd_0/ip/ip_0/sim
--include ${HDK_SHELL_DESIGN_DIR}/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog
--include ${HDK_SHELL_DESIGN_DIR}/ip/axi_register_slice/hdl
--include ${HDK_SHELL_DESIGN_DIR}/ip/axi_register_slice_light/hdl
--include ${CL_ROOT}/design/axi_crossbar_0
--include ${HDK_SHELL_DESIGN_DIR}/ip/cl_axi_interconnect/ipshared/7e3a/hdl
--include ${HDK_SHELL_DESIGN_DIR}/sh_ddr/sim

--include ${HDK_CL_IP_SOURCES}/ip/src_register_slice/hdl
--include ${HDK_CL_IP_SOURCES}/ip/dest_register_slice/hdl
--include $HDK_COMMON_DIR/verif/tb/sv

$HDK_COMMON_DIR/lib/macros.svh
$HDK_COMMON_DIR/lib/interfaces.sv
$HDK_COMMON_DIR/lib/lib_pipe.sv
$HDK_COMMON_DIR/lib/bram_1w1r.sv
$HDK_COMMON_DIR/lib/bram_2rw.sv
$HDK_COMMON_DIR/lib/sync.v
$HDK_COMMON_DIR/lib/flop_fifo.sv
$HDK_COMMON_DIR/lib/flop_ccf.sv
$HDK_COMMON_DIR/lib/cdc_async_fifo.sv
$HDK_COMMON_DIR/lib/xpm_fifo.sv
$HDK_COMMON_DIR/lib/mgt_acc_axl.sv
$HDK_COMMON_DIR/lib/mgt_gen_axl.sv
$HDK_COMMON_DIR/lib/ccf_ctl.v
$HDK_COMMON_DIR/verif/models/xilinx_axi_pc/axi_protocol_checker_v1_1_vl_rfs.v
$HDK_COMMON_DIR/verif/packages/anp_base_pkg.sv
$HDK_COMMON_DIR/verif/tb/sv/tb_type_defines_pkg.sv
$HDK_COMMON_DIR/verif/models/sh_bfm/axil_bfm.sv
$HDK_COMMON_DIR/verif/models/sh_bfm/axis_bfm_pkg.sv
$HDK_COMMON_DIR/verif/models/sh_bfm/axis_bfm.sv
$HDK_COMMON_DIR/verif/models/sh_bfm/sh_bfm.sv
$HDK_COMMON_DIR/verif/models/fpga/fpga.sv
$HDK_COMMON_DIR/verif/models/fpga/card.sv
$HDK_COMMON_DIR/verif/tb/sv/tb.sv

-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f
${TEST_NAME}

${HDK_CL_IP_SOURCES}/ip/cl_axi_interconnect/hdl/axi_data_fifo_v2_1_vl_rfs.v
${HDK_CL_IP_SOURCES}/ip/cl_axi_interconnect/sim/cl_axi_interconnect.v
${HDK_CL_IP_SOURCES}/ip/dest_register_slice/hdl/axi_register_slice_v2_1_vl_rfs.v
${HDK_CL_IP_SOURCES}/ip/axi_clock_converter_0/hdl/axi_clock_converter_v2_1_vl_rfs.v
${HDK_CL_IP_SOURCES}/ip/axi_clock_converter_0/hdl/fifo_generator_v13_2_rfs.v
${HDK_CL_IP_SOURCES}/ip/axi_clock_converter_0/sim/axi_clock_converter_0.v
${HDK_CL_IP_SOURCES}/ip/dest_register_slice/sim/dest_register_slice.v
${HDK_CL_IP_SOURCES}/ip/src_register_slice/sim/src_register_slice.v
${HDK_CL_IP_SOURCES}/ip/axi_register_slice/sim/axi_register_slice.v
${HDK_CL_IP_SOURCES}/ip/axi_register_slice_light/sim/axi_register_slice_light.v
${HDK_CL_IP_SOURCES}/ip/cl_axi_interconnect/hdl/axi_crossbar_v2_1_vl_rfs.v
${HDK_CL_IP_SOURCES}/ip/cl_axi_interconnect/hdl/axi_infrastructure_v1_1_vl_rfs.v
${HDK_CL_IP_SOURCES}/ip/cl_axi_clock_converter/sim/cl_axi_clock_converter.v
${HDK_CL_IP_SOURCES}/ip/cl_axi_clock_converter_light/sim/cl_axi_clock_converter_light.v


${HDK_COMMON_DIR}/verif/models/ddr4_rdimm_wrapper/ddr4_bi_delay.sv
${HDK_COMMON_DIR}/verif/models/ddr4_rdimm_wrapper/ddr4_db_delay_model.sv
${HDK_COMMON_DIR}/verif/models/ddr4_rdimm_wrapper/ddr4_db_dly_dir.sv
${HDK_COMMON_DIR}/verif/models/ddr4_rdimm_wrapper/ddr4_dir_detect.sv
${HDK_COMMON_DIR}/verif/models/ddr4_rdimm_wrapper/ddr4_rcd_model.sv
${HDK_COMMON_DIR}/verif/models/ddr4_rdimm_wrapper/ddr4_rank.sv
${HDK_COMMON_DIR}/verif/models/ddr4_rdimm_wrapper/ddr4_dimm.sv
${HDK_COMMON_DIR}/verif/models/ddr4_rdimm_wrapper/ddr4_rdimm_wrapper.sv

$HDK_CL_IP_SOURCES/ip/cl_axi_clock_converter_256b/sim/cl_axi_clock_converter_256b.v
$HDK_CL_IP_SOURCES/ip/cl_axi_width_cnv_512_to_256/sim/cl_axi_width_cnv_512_to_256.v
$HDK_CL_IP_SOURCES/../../cl_ip.gen/sources_1/ip/cl_axi4_to_axi3_conv/sim/cl_axi4_to_axi3_conv.v
$HDK_CL_IP_SOURCES/../../cl_ip.gen/sources_1/ip/cl_axi_register_slice_256/sim/cl_axi_register_slice_256.v
$HDK_CL_IP_SOURCES/ip/cl_axi_width_cnv_512_to_256/simulation/blk_mem_gen_v8_4.v


--define DISABLE_VJTAG_DEBUG
${CL_ROOT}/design/cl_dram_dma_defines.vh
${CL_ROOT}/design/axil_slave.sv
${CL_ROOT}/design/mem_scrb.sv
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
${CL_ROOT}/design/cl_dram_dma_axi_mstr.sv
${CL_ROOT}/design/cl_dram_hbm_dma.sv
