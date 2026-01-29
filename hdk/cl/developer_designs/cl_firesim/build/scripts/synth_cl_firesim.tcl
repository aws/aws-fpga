#Param needed to avoid clock name collisions
# CL_MODULE: Set default if not already defined (used for clock name prefixing)
if {![info exists CL_MODULE]} {
    set CL_MODULE "cl_firesim"
}
# set VDEFINES $VDEFINES
set VDEFINES ""

# Common header
source ${HDK_SHELL_DIR}/build/scripts/synth_cl_header.tcl


###############################################################################
print "Reading encrypted user source codes"
###############################################################################

# Generate IP instantated in Golden-Gate generated RTL
file mkdir $CL_DIR/design/ipgen
set ipgen_scripts [glob -nocomplain $CL_DIR/design/FireSim-generated.*.ipgen.tcl]
foreach script $ipgen_scripts {
    source $script
}

# Generate targets for all IPs contained within the generated module hierarchy.
# With the exception of the PLL, these are the only IP instances that don't have
# their output artifacts checked in.
generate_target all [get_ips]

synth_ip [get_ips]

########################################
## Generate clocks based on Recipe 
########################################

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Calling aws_gen_clk_constraints.tcl to generate clock constraints from developer's specified recipe.";

source $HDK_SHELL_DIR/build/scripts/aws_gen_clk_constraints.tcl

#############################
## Read design files
#############################

#Convenience to set the root of the RTL directory
set ENC_SRC_DIR $CL_DIR/build/src_post_encryption

# Set include directories for Verilog `include directives
# This is needed to find cl_common_defines.vh in the common/design directory
set_property include_dirs [list \
    ${CL_DIR}/design \
    ${CL_DIR}/../common/design \
] [current_fileset]

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Reading developer's Custom Logic files post encryption.";

#---- User would replace this section -----

# Reading the .sv and .v files, as proper designs would not require reading
# .vh, nor .inc files
# read_verilog -sv [glob ${src_post_enc_dir}/*.{s,}v]
read_verilog -sv [glob ${CL_DIR}/design/*.{s,}v]

#---- End of section replaced by User ----

puts "AWS FPGA: Reading AWS Shell design";

# DONE IN synth_cl_header.tcl
#Read AWS Design files
# read_verilog -sv [ list \
#   $HDK_SHELL_DESIGN_DIR/../../lib/lib_pipe.sv \
#   $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/sync.v \
#   $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/flop_ccf.sv \
#   $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/ccf_ctl.v \
#   $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/sh_ddr.sv \
#   $HDK_SHELL_DESIGN_DIR/../../lib/lib_pipe.sv \
#   $HDK_SHELL_DESIGN_DIR/../../lib/bram_2rw.sv \
#   $HDK_SHELL_DESIGN_DIR/../../lib/flop_fifo.sv \
#   $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/mgt_acc_axl.sv  \
#   $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/mgt_gen_axl.sv  \
#   $HDK_SHELL_DESIGN_DIR/interfaces/cl_ports.vh
# ]

###############################################################################
print "Reading CL IP blocks"
###############################################################################

## DDR IP
# read_ip ${HDK_IP_SRC_DIR}/cl_ddr4_32g/cl_ddr4_32g.xci

## HBM IP's
# read_ip ${HDK_IP_SRC_DIR}/cl_hbm_mmcm/cl_hbm_mmcm.xci
# read_ip ${HDK_IP_SRC_DIR}/cl_hbm/cl_hbm.xci

# Clocking IP's
read_ip ${HDK_SHELL_DESIGN_DIR}/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/clk_mmcm_a/clk_mmcm_a.xci
read_ip ${HDK_SHELL_DESIGN_DIR}/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/clk_mmcm_b/clk_mmcm_b.xci
read_ip ${HDK_SHELL_DESIGN_DIR}/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/clk_mmcm_c/clk_mmcm_c.xci
read_ip ${HDK_SHELL_DESIGN_DIR}/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/clk_mmcm_hbm/clk_mmcm_hbm.xci
read_ip ${HDK_SHELL_DESIGN_DIR}/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/cl_clk_axil_xbar/cl_clk_axil_xbar.xci
read_ip ${HDK_SHELL_DESIGN_DIR}/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/cl_sda_axil_xbar/cl_sda_axil_xbar.xci

# AXI Register Slice IP's
read_ip ${HDK_IP_SRC_DIR}/cl_axi_register_slice/cl_axi_register_slice.xci
read_ip ${HDK_IP_SRC_DIR}/cl_axi_register_slice_light/cl_axi_register_slice_light.xci
read_ip ${HDK_IP_SRC_DIR}/src_register_slice/src_register_slice.xci
read_ip ${HDK_IP_SRC_DIR}/dest_register_slice/dest_register_slice.xci
read_ip ${HDK_IP_SRC_DIR}/axi_register_slice/axi_register_slice.xci
read_ip ${HDK_IP_SRC_DIR}/axi_register_slice_light/axi_register_slice_light.xci
read_ip ${HDK_IP_SRC_DIR}/cl_axi_register_slice_256/cl_axi_register_slice_256.xci
read_ip ${HDK_IP_SRC_DIR}/cl_axi3_256b_reg_slice/cl_axi3_256b_reg_slice.xci

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

# Read IP for virtual jtag / ILA/VIO
read_ip ${HDK_IP_SRC_DIR}/cl_debug_bridge/cl_debug_bridge.xci
read_ip ${HDK_IP_SRC_DIR}/ila_1/ila_1.xci
read_ip ${HDK_IP_SRC_DIR}/ila_vio_counter/ila_vio_counter.xci
read_ip ${HDK_IP_SRC_DIR}/vio_0/vio_0.xci

#Read IP for virtual jtag / ILA/VIO
read_ip [ list \
  ${HDK_IP_SRC_DIR}/axi_clock_converter_0/axi_clock_converter_0.xci \
  $CL_DIR/ip/axi_clock_converter_dramslim/axi_clock_converter_dramslim.xci \
  $CL_DIR/ip/axi_clock_converter_oclnew/axi_clock_converter_oclnew.xci \
  $CL_DIR/ip/axi_clock_converter_512_wide/axi_clock_converter_512_wide.xci \
  $CL_DIR/ip/axi_clock_converter_512_pcim/axi_clock_converter_512_pcim.xci \
  $CL_DIR/ip/axi_dwidth_converter_0/axi_dwidth_converter_0.xci
]

## AXI Conversion IP's
read_ip [ list \
  ${HDK_IP_SRC_DIR}/cl_axi_clock_converter/cl_axi_clock_converter.xci \
  ${HDK_IP_SRC_DIR}/cl_axi_clock_converter_light/cl_axi_clock_converter_light.xci
]

# Additional IP's that might be needed if using the DDR
read_ip [ list \
  ${HDK_IP_SRC_DIR}/cl_ddr4_32g/cl_ddr4_32g.xci \
  ${HDK_IP_SRC_DIR}/cl_ddr4_32g_ap/cl_ddr4_32g_ap.xci \
  ${HDK_IP_SRC_DIR}/cl_ddr4/cl_ddr4.xci \
  ${HDK_IP_SRC_DIR}/cl_ddr4_64g_ap/cl_ddr4_64g_ap.xci
]
read_ip [ list \
 ${HDK_IP_SRC_DIR}/cl_axi_interconnect/cl_axi_interconnect.xci \
 ${HDK_IP_SRC_DIR}/cl_axi_interconnect_64G_ddr/cl_axi_interconnect_64G_ddr.xci
]

###############################################################################
print "Reading user constraints"
###############################################################################

read_xdc [ list \
  ${constraints_dir}/cl_synth_user.xdc \
  ${constraints_dir}/cl_timing_user.xdc
]

set_property PROCESSING_ORDER LATE [get_files cl_synth_user.xdc]
set_property PROCESSING_ORDER LATE [get_files cl_timing_user.xdc]


# FireSim custom clocking
source $CL_DIR/build/scripts/synth_firesim_clk_wiz.tcl

#===============================================================================
# ALL IPs below were originally configured for F1 (xcvu9p) and must be
# regenerated for F2. reset_target clears stale OOC synthesis outputs.
#===============================================================================

# Reconfigure PCIS clock converter for F2 16-bit IDs (vs F1's 6-bit)
upgrade_ip [get_ips axi_clock_converter_512_wide]
reset_target {all} [get_ips axi_clock_converter_512_wide]
set_property CONFIG.ID_WIDTH 16 [get_ips axi_clock_converter_512_wide]
generate_target {all} [get_ips axi_clock_converter_512_wide]
synth_ip [get_ips axi_clock_converter_512_wide]

# Regenerate axi_dwidth_converter_0 for F2 (64-bit to 512-bit width conversion)
# CRITICAL: Disable FIFO_MODE to prevent MDRV-1 (Multiple Driver Nets) DRC errors
# on xcvu47p. The packet FIFO mode creates BRAM instances that drive constant nets
# with multiple drivers, which fails DRC on F2's device architecture.
upgrade_ip [get_ips axi_dwidth_converter_0]
reset_target {all} [get_ips axi_dwidth_converter_0]
set_property CONFIG.FIFO_MODE {0} [get_ips axi_dwidth_converter_0]
generate_target {all} [get_ips axi_dwidth_converter_0]
synth_ip [get_ips axi_dwidth_converter_0]

# Regenerate axi_clock_converter_dramslim for F2
upgrade_ip [get_ips axi_clock_converter_dramslim]
reset_target {all} [get_ips axi_clock_converter_dramslim]
generate_target {all} [get_ips axi_clock_converter_dramslim]
synth_ip [get_ips axi_clock_converter_dramslim]

# Regenerate axi_clock_converter_oclnew for F2
upgrade_ip [get_ips axi_clock_converter_oclnew]
reset_target {all} [get_ips axi_clock_converter_oclnew]
generate_target {all} [get_ips axi_clock_converter_oclnew]
synth_ip [get_ips axi_clock_converter_oclnew]

# Regenerate axi_clock_converter_512_pcim for F2
upgrade_ip [get_ips axi_clock_converter_512_pcim]
reset_target {all} [get_ips axi_clock_converter_512_pcim]
generate_target {all} [get_ips axi_clock_converter_512_pcim]
synth_ip [get_ips axi_clock_converter_512_pcim]

#===============================================================================

#Do not propagate local clock constraints for clocks generated in the SH
set_property USED_IN {synthesis implementation OUT_OF_CONTEXT} [get_files generated_cl_clocks_aws.xdc]
set_property PROCESSING_ORDER EARLY  [get_files generated_cl_clocks_aws.xdc]

########################
# CL Synthesis
########################

###############################################################################
print "Starting synthesizing customer design ${CL}"
###############################################################################
update_compile_order -fileset sources_1

# synth_design -mode out_of_context \
#              -top ${CL} \
#              -verilog_define XSDB_SLV_DIS \
#              -part ${DEVICE_TYPE} \
#              -keep_equivalent_registers

synth_design -mode out_of_context \
             -top cl_firesim \
             -verilog_define XSDB_SLV_DIS \
             -part ${DEVICE_TYPE} \
             -keep_equivalent_registers

# update_compile_order -fileset sources_1
# puts "\nRunning synth_design for $CL_MODULE $CL_DIR/build/scripts \[[clock format [clock seconds] -format {%a %b %d %H:%M:%S %Y}]\]"
# eval [concat synth_design -top $CL_MODULE -verilog_define XSDB_SLV_DIS $VDEFINES -part [DEVICE_TYPE] -mode out_of_context $synth_options -directive $synth_directive]

set failval [catch {exec grep "FAIL" failfast.csv}]
if { $failval==0 } {
	puts "AWS FPGA: FATAL ERROR--Resource utilization error; check failfast.csv for details"
	exit 1
}

set timestamp [clock format [clock seconds] -format "%y_%m_%d-%H%M%S"]
puts "AWS FPGA: ([clock format [clock seconds] -format %T]) writing post synth checkpoint.";
write_checkpoint -force $CL_DIR/build/checkpoints/${timestamp}.CL.post_synth.dcp

report_utilization -hierarchical -hierarchical_percentages -file $CL_DIR/build/reports/${timestamp}.post_synth_utilization.rpt
report_control_sets -verbose -file $CL_DIR/build/reports/${timestamp}.post_synth_control_sets.rpt

# close_project
#Set param back to default value
# set_param sta.enableAutoGenClkNamePersistence 1

# Common footer
source ${HDK_SHELL_DIR}/build/scripts/synth_cl_footer.tcl
