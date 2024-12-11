# Amazon FPGA Hardware Development Kit
#
# Copyright 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

+define+VCS_SIM
+define+CARD_1=card
+define+SIMULATION


$XILINX_VIVADO/data/verilog/src/glbl.v

#------------------------------------------------------------------------------
# Design Files
#------------------------------------------------------------------------------
+incdir+$HDK_COMMON_DIR/lib
$HDK_COMMON_DIR/lib/aws_clk_gen.sv
$HDK_COMMON_DIR/lib/aws_clk_regs.sv
$HDK_COMMON_DIR/lib/axil_to_cfg_cnv.sv
$HDK_COMMON_DIR/lib/axi_clock_conv.sv
$HDK_COMMON_DIR/lib/bram_1w1r.sv
$HDK_COMMON_DIR/lib/cdc_sync.sv
$HDK_COMMON_DIR/lib/flop_fifo.sv
$HDK_COMMON_DIR/lib/ft_fifo.v
$HDK_COMMON_DIR/lib/hbm_wrapper.sv
$HDK_COMMON_DIR/lib/lib_pipe.sv
$HDK_COMMON_DIR/lib/ram_fifo_ft.sv
$HDK_COMMON_DIR/lib/srl_fifo.sv
$HDK_COMMON_DIR/lib/xpm_fifo.sv
$HDK_COMMON_DIR/lib/axis_flop_fifo.sv
$HDK_COMMON_DIR/lib/bram_2rw.sv
$HDK_COMMON_DIR/lib/cdc_async_fifo.sv
$HDK_COMMON_DIR/lib/flop_fifo_in.sv
$HDK_COMMON_DIR/lib/ft_fifo_p.v
$HDK_COMMON_DIR/lib/interfaces.sv
$HDK_COMMON_DIR/lib/rr_arb.sv

+incdir+$HDK_SHELL_DESIGN_DIR/ip/cl_axi_interconnect/ipshared/7e3a/hdl
+incdir+$HDK_SHELL_DESIGN_DIR/interfaces

+incdir+$HDK_SHELL_DESIGN_DIR/sh_ddr/sim
$HDK_SHELL_DESIGN_DIR/sh_ddr/sim/sync.v
$HDK_SHELL_DESIGN_DIR/sh_ddr/sim/mgt_acc_axl.sv
$HDK_SHELL_DESIGN_DIR/sh_ddr/sim/mgt_gen_axl.sv
$HDK_SHELL_DESIGN_DIR/sh_ddr/sim/ccf_ctl.v
$HDK_SHELL_DESIGN_DIR/sh_ddr/sim/flop_ccf.sv
$HDK_SHELL_DESIGN_DIR/sh_ddr/sim/sh_ddr.sv
$HDK_SHELL_DESIGN_DIR/sh_ddr/sim/axi4_slave_bfm.sv

#------------------------------------------------------------------------------
# Verification Files
#------------------------------------------------------------------------------

+incdir+$HDK_COMMON_DIR/verif/include
$HDK_COMMON_DIR/verif/models/xilinx_axi_pc/axi_protocol_checker_v1_1_vl_rfs.v

+incdir+$HDK_COMMON_DIR/verif/models/ddr4_model
$HDK_COMMON_DIR/verif/models/ddr4_model/ddr4_sdram_model_wrapper.sv

+incdir+$HDK_COMMON_DIR/verif/models/ddr4_rdimm_wrapper
$HDK_COMMON_DIR/verif/models/ddr4_rdimm_wrapper/ddr4_rcd_model.sv
$HDK_COMMON_DIR/verif/models/ddr4_rdimm_wrapper/ddr4_rdimm_wrapper.sv
$HDK_COMMON_DIR/verif/models/ddr4_rdimm_wrapper/ddr4_dimm.sv
$HDK_COMMON_DIR/verif/models/ddr4_rdimm_wrapper/ddr4_bi_delay.sv
$HDK_COMMON_DIR/verif/models/ddr4_rdimm_wrapper/ddr4_db_delay_model.sv
$HDK_COMMON_DIR/verif/models/ddr4_rdimm_wrapper/ddr4_dir_detect.sv
$HDK_COMMON_DIR/verif/models/ddr4_rdimm_wrapper/ddr4_db_dly_dir.sv
$HDK_COMMON_DIR/verif/models/ddr4_rdimm_wrapper/ddr4_rank.sv

+incdir+$HDK_COMMON_DIR/verif/packages
$HDK_COMMON_DIR/verif/packages/anp_base_pkg.sv

+incdir+$HDK_COMMON_DIR/verif/models/fpga
$HDK_COMMON_DIR/verif/models/fpga/fpga.sv
$HDK_COMMON_DIR/verif/models/fpga/card.sv

+incdir+$HDK_COMMON_DIR/verif/tb/sv
$HDK_COMMON_DIR/verif/tb/sv/tb_type_defines_pkg.sv
$HDK_COMMON_DIR/verif/tb/sv/tb.sv

+incdir+$HDK_COMMON_DIR/verif/models/sh_bfm
$HDK_COMMON_DIR/verif/models/sh_bfm/axil_bfm.sv
$HDK_COMMON_DIR/verif/models/sh_bfm/axis_bfm_pkg.sv
$HDK_COMMON_DIR/verif/models/sh_bfm/axis_bfm.sv
$HDK_COMMON_DIR/verif/models/sh_bfm/sh_bfm.sv

+incdir+$HDK_COMMON_DIR/ip/cl_ip/cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/hdl
$HDK_COMMON_DIR/ip/cl_ip/cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/hdl/cl_axi_sc_1x1_wrapper.v
+incdir+$HDK_COMMON_DIR/ip/cl_ip/cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/hdl
$HDK_COMMON_DIR/ip/cl_ip/cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/hdl/cl_axi_sc_2x2_wrapper.v

#------------------------------------------------------------------------------
# SDE Specific Files
#------------------------------------------------------------------------------
$HDK_COMMON_DIR/verif/models/base/gen_buf_t.sv
$HDK_COMMON_DIR/verif/models/stream_bfm/stream_bfm.sv
$HDK_COMMON_DIR/verif/tb/sv/dma_classes.sv
