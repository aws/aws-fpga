# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
# =============================================================================


# Common CL Synthesis Tcl Script Header


###############################################################################
print "Creating in-memory synthesis project"
###############################################################################
# Param needed to avoid clock name collisions
# NOTE: reset in synth_cl_footer.tcl
set_param sta.enableAutoGenClkNamePersistence 0

create_project -in_memory -part $DEVICE_TYPE -force

# Parse in XPM libraries
set_property XPM_LIBRARIES {XPM_CDC XPM_MEMORY XPM_FIFO} [current_project]

###############################################################################
print "Reading common AWS components"
###############################################################################
read_verilog -sv [ list \
  ${HDK_SHELL_DESIGN_DIR}/../../lib/interfaces.sv \
  ${HDK_SHELL_DESIGN_DIR}/../../lib/aws_clk_gen.sv \
  ${HDK_SHELL_DESIGN_DIR}/../../lib/aws_clk_regs.sv \
  ${HDK_SHELL_DESIGN_DIR}/../../lib/axil_to_cfg_cnv.sv \
  ${HDK_SHELL_DESIGN_DIR}/../../lib/axis_flop_fifo.sv \
  ${HDK_SHELL_DESIGN_DIR}/../../lib/lib_pipe.sv \
  ${HDK_SHELL_DESIGN_DIR}/../../lib/bram_1w1r.sv \
  ${HDK_SHELL_DESIGN_DIR}/../../lib/bram_2rw.sv \
  ${HDK_SHELL_DESIGN_DIR}/../../lib/xpm_fifo.sv \
  ${HDK_SHELL_DESIGN_DIR}/../../lib/flop_fifo.sv \
  ${HDK_SHELL_DESIGN_DIR}/../../lib/flop_fifo_in.sv \
  ${HDK_SHELL_DESIGN_DIR}/../../lib/cdc_async_fifo.sv \
  ${HDK_SHELL_DESIGN_DIR}/../../lib/cdc_sync.sv \
  ${HDK_SHELL_DESIGN_DIR}/../../lib/ft_fifo_p.v \
  ${HDK_SHELL_DESIGN_DIR}/../../lib/ft_fifo.v \
  ${HDK_SHELL_DESIGN_DIR}/../../lib/ram_fifo_ft.sv \
  ${HDK_SHELL_DESIGN_DIR}/../../lib/rr_arb.sv \
  ${HDK_SHELL_DESIGN_DIR}/sh_ddr/synth/sync.v \
  ${HDK_SHELL_DESIGN_DIR}/sh_ddr/synth/flop_ccf.sv \
  ${HDK_SHELL_DESIGN_DIR}/sh_ddr/synth/ccf_ctl.v \
  ${HDK_SHELL_DESIGN_DIR}/sh_ddr/synth/mgt_acc_axl.sv \
  ${HDK_SHELL_DESIGN_DIR}/sh_ddr/synth/mgt_gen_axl.sv \
  ${HDK_SHELL_DESIGN_DIR}/sh_ddr/synth/sh_ddr.sv \
  ${HDK_SHELL_DESIGN_DIR}/interfaces/cl_ports.vh
]

###############################################################################
print "Reading AWS Constraints"
###############################################################################
# cl_pins.xdc                  - AWS provided DDR/C2C IO pin constraints.
# generated_cl_clocks_aws.xdc  - AWS auto-generated clock constraint from `aws_gen_clk_constraints.tcl`
# cl_ddr_timing_aws.xdc        - AWS timing constraints for SH_DDR.
read_xdc ${HDK_SHELL_DIR}/build/constraints/cl_pins.xdc
read_xdc ${CL_DIR}/build/constraints/generated_cl_clocks_aws.xdc
read_xdc -ref ${CL} ${HDK_SHELL_DIR}/build/constraints/cl_ddr_timing_aws.xdc

# Do not propagate local clock constraints for clocks generated in the SH
set_property USED_IN {synthesis implementation OUT_OF_CONTEXT} [get_files generated_cl_clocks_aws.xdc]
set_property PROCESSING_ORDER EARLY [get_files generated_cl_clocks_aws.xdc]


set_property USED_IN {synthesis implementation} [get_files cl_ddr_timing_aws.xdc]
set_property PROCESSING_ORDER LATE   [get_files cl_ddr_timing_aws.xdc]
