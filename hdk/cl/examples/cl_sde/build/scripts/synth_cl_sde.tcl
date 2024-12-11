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


# Common header
source ${HDK_SHELL_DIR}/build/scripts/synth_cl_header.tcl



###############################################################################
print "Reading encrypted user source codes"
###############################################################################

#---- User would replace this section -----

# Reading the .sv and .v files, as proper designs would not require reading
# .vh, nor .inc files
read_verilog -sv [glob ${src_post_enc_dir}/cl_sde_defines.vh]
set_property file_type {Verilog Header} [get_files ${src_post_enc_dir}/cl_sde_defines.vh]
set_property is_global_include true     [get_files ${src_post_enc_dir}/cl_sde_defines.vh]

read_verilog -sv [glob ${src_post_enc_dir}/*.?v]

#---- End of section replaced by User ----

###############################################################################
print "Reading CL IP blocks"
###############################################################################

#---- User would uncomment the IP's required in their design ----

#Read DDR IP
read_ip [ list \
  ${HDK_IP_SRC_DIR}/cl_ddr4_32g/cl_ddr4_32g.xci
]

#Read IP for axi register slices
read_ip [ list \
  ${HDK_IP_SRC_DIR}/cl_axi_interconnect/cl_axi_interconnect.xci \
  ${HDK_IP_SRC_DIR}/cl_axi_clock_converter/cl_axi_clock_converter.xci \
  ${HDK_IP_SRC_DIR}/cl_axi_clock_converter_light/cl_axi_clock_converter_light.xci \
  ${HDK_IP_SRC_DIR}/src_register_slice/src_register_slice.xci \
  ${HDK_IP_SRC_DIR}/dest_register_slice/dest_register_slice.xci \
  ${HDK_IP_SRC_DIR}/axi_clock_converter_0/axi_clock_converter_0.xci \
  ${HDK_IP_SRC_DIR}/axi_register_slice/axi_register_slice.xci \
  ${HDK_IP_SRC_DIR}/axi_register_slice_light/axi_register_slice_light.xci \
  ${HDK_IP_SRC_DIR}/cl_axi_clock_converter_256b/cl_axi_clock_converter_256b.xci \
  ${HDK_IP_SRC_DIR}/cl_hbm/cl_hbm.xci \
  ${HDK_IP_SRC_DIR}/cl_axi_width_cnv_512_to_256/cl_axi_width_cnv_512_to_256.xci \
  ${HDK_IP_SRC_DIR}/cl_hbm_mmcm/cl_hbm_mmcm.xci \
  ${HDK_IP_SRC_DIR}/cl_axi4_to_axi3_conv/cl_axi4_to_axi3_conv.xci
]

#Read IP for virtual jtag / ILA/VIO
read_ip [ list \
  ${HDK_IP_SRC_DIR}/cl_debug_bridge/cl_debug_bridge.xci \
  ${HDK_IP_SRC_DIR}/ila_1/ila_1.xci
]

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

set cl_ila_cells [get_cells [list CL_ILA/CL_DMA_ILA_0 CL_ILA/ddr_A_hookup.CL_DDRA_ILA_0]]
if {$cl_ila_cells != ""} {
  connect_debug_cores -master [get_cells [get_debug_cores -filter {NAME=~*CL_DEBUG_BRIDGE*}]] -slaves $cl_ila_cells
}

#---- End of section replaced by User ----



# Common footer
source ${HDK_SHELL_DIR}/build/scripts/synth_cl_footer.tcl
