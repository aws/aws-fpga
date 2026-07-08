# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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


# Common header
source ${HDK_SHELL_DIR}/build/scripts/synth_cl_header.tcl


###############################################################################
print "Reading encrypted user source files"
###############################################################################

read_verilog -sv [glob ${src_post_enc_dir}/*.{s,}v]

###############################################################################
print "Reading CL IP blocks"
###############################################################################

# aws_clk_gen clocking IPs
read_ip [ list \
  $HDK_SHELL_DESIGN_DIR/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/clk_mmcm_a/clk_mmcm_a.xci \
  $HDK_SHELL_DESIGN_DIR/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/cl_clk_axil_xbar/cl_clk_axil_xbar.xci
]

# AXI register slice and clock converter IPs
read_ip [ list \
  ${HDK_IP_SRC_DIR}/axi_register_slice_light/axi_register_slice_light.xci \
  ${HDK_IP_SRC_DIR}/cl_axi_register_slice_light/cl_axi_register_slice_light.xci \
  ${HDK_IP_SRC_DIR}/cl_axi_clock_converter_light/cl_axi_clock_converter_light.xci
]

# Debug
read_ip ${HDK_IP_SRC_DIR}/cl_debug_bridge/cl_debug_bridge.xci

###############################################################################
print "Reading user constraints"
###############################################################################

read_xdc [ list \
  ${constraints_dir}/cl_synth_user.xdc \
  ${constraints_dir}/cl_timing_user.xdc
]

set_property PROCESSING_ORDER LATE [get_files cl_synth_user.xdc]
set_property PROCESSING_ORDER LATE [get_files cl_timing_user.xdc]

###############################################################################
print "Starting synthesis of customer's design ${CL}"
###############################################################################
update_compile_order -fileset sources_1

synth_design -mode out_of_context \
             -top ${CL} \
             -verilog_define XSDB_SLV_DIS \
             -part ${DEVICE_TYPE} \
             -keep_equivalent_registers


# Common footer
source ${HDK_SHELL_DIR}/build/scripts/synth_cl_footer.tcl
