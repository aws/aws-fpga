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


# Common header
source ${HDK_SHELL_DIR}/build/scripts/synth_cl_header.tcl


###############################################################################
print "Reading encrypted user source codes"
###############################################################################

#---- User would replace this section -----

# Reading the .sv and .v files, as proper designs would not require reading
# .vh, nor .inc files
read_verilog -sv [glob ${src_post_enc_dir}/*.?v]

#---- End of section replaced by User ----

###############################################################################
print "Reading CL IP blocks"
###############################################################################

#---- User would uncomment and/or list IPs required in their design ----

## DDR IP
# read_ip ${HDK_IP_SRC_DIR}/cl_ddr4_32g/cl_ddr4_32g.xci

## HBM IP's
# read_ip ${HDK_IP_SRC_DIR}/cl_hbm_mmcm/cl_hbm_mmcm.xci
# read_ip ${HDK_IP_SRC_DIR}/cl_hbm/cl_hbm.xci

## Clocking IP's
# read_ip ${HDK_SHELL_DESIGN_DIR}/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/clk_mmcm_a/clk_mmcm_a.xci
# read_ip ${HDK_SHELL_DESIGN_DIR}/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/clk_mmcm_b/clk_mmcm_b.xci
# read_ip ${HDK_SHELL_DESIGN_DIR}/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/clk_mmcm_c/clk_mmcm_c.xci
# read_ip ${HDK_SHELL_DESIGN_DIR}/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/clk_mmcm_hbm/clk_mmcm_hbm.xci
# read_ip ${HDK_SHELL_DESIGN_DIR}/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/cl_clk_axil_xbar/cl_clk_axil_xbar.xci
# read_ip ${HDK_SHELL_DESIGN_DIR}/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/cl_sda_axil_xbar/cl_sda_axil_xbar.xci

## AXI Register Slice IP's
# read_ip ${HDK_IP_SRC_DIR}/cl_axi_register_slice/cl_axi_register_slice.xci
# read_ip ${HDK_IP_SRC_DIR}/cl_axi_register_slice_light/cl_axi_register_slice_light.xci
# read_ip ${HDK_IP_SRC_DIR}/src_register_slice/src_register_slice.xci
# read_ip ${HDK_IP_SRC_DIR}/dest_register_slice/dest_register_slice.xci
# read_ip ${HDK_IP_SRC_DIR}/axi_register_slice/axi_register_slice.xci
# read_ip ${HDK_IP_SRC_DIR}/axi_register_slice_light/axi_register_slice_light.xci
# read_ip ${HDK_IP_SRC_DIR}/cl_axi_register_slice_256/cl_axi_register_slice_256.xci

## AXI Conversion IP's
# read_ip ${HDK_IP_SRC_DIR}/cl_axi_clock_converter/cl_axi_clock_converter.xci
# read_ip ${HDK_IP_SRC_DIR}/cl_axi_clock_converter_light/cl_axi_clock_converter_light.xci
# read_ip ${HDK_IP_SRC_DIR}/cl_axi4_to_axi3_conv/cl_axi4_to_axi3_conv.xci
# read_ip ${HDK_IP_SRC_DIR}/cl_axi_clock_converter_256b/cl_axi_clock_converter_256b.xci
# read_ip ${HDK_IP_SRC_DIR}/cl_axi_width_cnv_512_to_256/cl_axi_width_cnv_512_to_256.xci
# read_ip ${HDK_IP_SRC_DIR}/axi_clock_converter_0/axi_clock_converter_0.xci

## AXI Utility IP's
# read_ip ${HDK_IP_SRC_DIR}/cl_axi_interconnect/cl_axi_interconnect.xci
# read_ip ${HDK_IP_SRC_DIR}/cl_axi_interconnect_64G_ddr/cl_axi_interconnect_64G_ddr.xci

## Read IP for virtual jtag / ILA/VIO
# read_ip ${HDK_IP_SRC_DIR}/cl_debug_bridge/cl_debug_bridge.xci
# read_ip ${HDK_IP_SRC_DIR}/ila_1/ila_1.xci
# read_ip ${HDK_IP_SRC_DIR}/ila_vio_counter/ila_vio_counter.xci
# read_ip ${HDK_IP_SRC_DIR}/vio_0/vio_0.xci

#---- End of section uncommented by the User ----

###############################################################################
print "Reading user constraints"
###############################################################################

#---- User would replace this section -----

read_xdc [ list \
  ${constraints_dir}/cl_synth_user.xdc \
  ${constraints_dir}/cl_timing_user.xdc
]

set_property PROCESSING_ORDER LATE [get_files cl_synth_user.xdc]
set_property PROCESSING_ORDER LATE [get_files cl_timing_user.xdc]

#---- End of section replaced by User ----


###############################################################################
print "Starting synthesizing customer design ${CL}"
###############################################################################
update_compile_order -fileset sources_1

synth_design -mode out_of_context \
             -top ${CL} \
             -verilog_define XSDB_SLV_DIS \
             -part ${DEVICE_TYPE} \
             -keep_equivalent_registers

###############################################################################
print "Connecting debug network"
###############################################################################

#---- User would replace this section -----

# set cl_ila_cells [get_cells -hier *ILA*]
# if {$cl_ila_cells != ""} {
#   connect_debug_cores -master [get_cells [get_debug_cores -filter {NAME=~*CL_DEBUG_BRIDGE*}]] \
#                       -slaves $cl_ila_cells
# }

#---- End of section replaced by User ----


# Common footer
source ${HDK_SHELL_DIR}/build/scripts/synth_cl_footer.tcl
