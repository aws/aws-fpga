#Param needed to avoid clock name collisions
# set_param sta.enableAutoGenClkNamePersistence 0
set CL_MODULE cl_firesim
# set VDEFINES $VDEFINES
set VDEFINES ""

# Common header
source ${HDK_SHELL_DIR}/build/scripts/synth_cl_header.tcl
# set DEVICE_TYPE "xcvu47p-fsvh2892-2-e"


###############################################################################
print "Reading encrypted user source codes"
###############################################################################

# create_project -in_memory -part [$DEVICE_TYPE] -force

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

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Reading developer's Custom Logic files post encryption.";

#---- User would replace this section -----

# Reading the .sv and .v files, as proper designs would not require
# reading .v, .vh, nor .inc files

# read_verilog -sv [glob ${src_post_enc_dir}/*.{s,}v] 
# getting ERROR: [Synth 8-9263] cannot open include file 'cl_common_defines.vh' 
read_verilog -sv [glob ${CL_DIR}/design/*.{s,}v]

#---- End of section replaced by User ----

puts "AWS FPGA: Reading AWS Shell design";

#Read AWS Design files
# read_verilog -sv [ list \
#   $HDK_SHELL_DESIGN_DIR/lib/lib_pipe.sv \
#   $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/sync.v \
#   $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/flop_ccf.sv \
#   $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/ccf_ctl.v \
#   $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/sh_ddr.sv \
#   $HDK_SHELL_DESIGN_DIR/lib/lib_pipe.sv \
#   $HDK_SHELL_DESIGN_DIR/lib/bram_2rw.sv \
#   $HDK_SHELL_DESIGN_DIR/lib/flop_fifo.sv \
#   $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/mgt_acc_axl.sv  \
#   $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/mgt_gen_axl.sv  \
#   $HDK_SHELL_DESIGN_DIR/interfaces/cl_ports.vh
# ]

read_verilog -sv [ list \
  $HDK_SHELL_DESIGN_DIR/../../lib/lib_pipe.sv \
  $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/sync.v \
  $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/flop_ccf.sv \
  $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/ccf_ctl.v \
  $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/sh_ddr.sv \
  $HDK_SHELL_DESIGN_DIR/../../lib/lib_pipe.sv \
  $HDK_SHELL_DESIGN_DIR/../../lib/bram_2rw.sv \
  $HDK_SHELL_DESIGN_DIR/../../lib/flop_fifo.sv \
  $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/mgt_acc_axl.sv  \
  $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/mgt_gen_axl.sv  \
  $HDK_SHELL_DESIGN_DIR/interfaces/cl_ports.vh
]

puts "AWS FPGA: Reading IP blocks";

## Clocking IP's
read_ip [ list \
  $HDK_SHELL_DESIGN_DIR/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/clk_mmcm_a/clk_mmcm_a.xci \
  $HDK_SHELL_DESIGN_DIR/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/clk_mmcm_b/clk_mmcm_b.xci \
  $HDK_SHELL_DESIGN_DIR/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/clk_mmcm_c/clk_mmcm_c.xci \
  $HDK_SHELL_DESIGN_DIR/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/clk_mmcm_hbm/clk_mmcm_hbm.xci \
  $HDK_SHELL_DESIGN_DIR/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/cl_clk_axil_xbar/cl_clk_axil_xbar.xci \
  $HDK_SHELL_DESIGN_DIR/../../ip/cl_ip/cl_ip.srcs/sources_1/ip/cl_sda_axil_xbar/cl_sda_axil_xbar.xci
]

#Read IP for axi register slices
# read_ip [ list \
#   $HDK_SHELL_DESIGN_DIR/ip/src_register_slice/src_register_slice.xci \
#   $HDK_SHELL_DESIGN_DIR/ip/dest_register_slice/dest_register_slice.xci \
#   $HDK_SHELL_DESIGN_DIR/ip/axi_register_slice/axi_register_slice.xci \
#   $HDK_SHELL_DESIGN_DIR/ip/axi_register_slice_light/axi_register_slice_light.xci
# ]

## AXI Register Slice IP's
read_ip [ list \
  ${HDK_IP_SRC_DIR}/axi_register_slice/axi_register_slice.xci \
  ${HDK_IP_SRC_DIR}/axi_register_slice_light/axi_register_slice_light.xci \
  ${HDK_IP_SRC_DIR}/cl_axi_register_slice_light/cl_axi_register_slice_light.xci \
  ${HDK_IP_SRC_DIR}/cl_axi3_256b_reg_slice/cl_axi3_256b_reg_slice.xci
]

read_ip [ list \
  ${HDK_IP_SRC_DIR}/src_register_slice/src_register_slice.xci \
  ${HDK_IP_SRC_DIR}/dest_register_slice/dest_register_slice.xci \
  ${HDK_IP_SRC_DIR}/axi_register_slice/axi_register_slice.xci \
  ${HDK_IP_SRC_DIR}/axi_register_slice_light/axi_register_slice_light.xci
]

#Read IP for virtual jtag / ILA/VIO
# read_ip [ list \
#   $HDK_SHELL_DESIGN_DIR/ip/ila_0/ila_0.xci \
#   $HDK_SHELL_DESIGN_DIR/ip/cl_debug_bridge/cl_debug_bridge.xci \
#   $HDK_SHELL_DESIGN_DIR/ip/ila_vio_counter/ila_vio_counter.xci \
#   $HDK_SHELL_DESIGN_DIR/ip/vio_0/vio_0.xci \
#   $HDK_SHELL_DESIGN_DIR/ip/axi_clock_converter_0/axi_clock_converter_0.xci \
#   $CL_DIR/ip/axi_clock_converter_dramslim/axi_clock_converter_dramslim.xci \
#   $CL_DIR/ip/axi_clock_converter_oclnew/axi_clock_converter_oclnew.xci \
#   $CL_DIR/ip/axi_clock_converter_512_wide/axi_clock_converter_512_wide.xci \
#   $CL_DIR/ip/axi_clock_converter_512_pcim/axi_clock_converter_512_pcim.xci \
#   $CL_DIR/ip/axi_dwidth_converter_0/axi_dwidth_converter_0.xci
# ]
read_ip [ list \
  ${HDK_IP_SRC_DIR}/cl_debug_bridge/cl_debug_bridge.xci \
  ${HDK_IP_SRC_DIR}/ila_1/ila_1.xci \
  ${HDK_IP_SRC_DIR}/ila_vio_counter/ila_vio_counter.xci \
  ${HDK_IP_SRC_DIR}/vio_0/vio_0.xci \
  ${HDK_IP_SRC_DIR}/axi_clock_converter_0/axi_clock_converter_0.xci \
  $CL_DIR/ip/axi_clock_converter_dramslim/axi_clock_converter_dramslim.xci \
  $CL_DIR/ip/axi_clock_converter_oclnew/axi_clock_converter_oclnew.xci \
  $CL_DIR/ip/axi_clock_converter_512_wide/axi_clock_converter_512_wide.xci \
  $CL_DIR/ip/axi_clock_converter_512_pcim/axi_clock_converter_512_pcim.xci \
  $CL_DIR/ip/axi_dwidth_converter_0/axi_dwidth_converter_0.xci
]
#   $CL_DIR/ip/axi_dwidth_converter_0/axi_dwidth_converter_0.xci \
#   $CL_DIR/ip/clk_wiz_0_firesim/clk_wiz_0_firesim.xci
# ]

## AXI Conversion IP's
read_ip [ list \
  ${HDK_IP_SRC_DIR}/cl_axi_clock_converter/cl_axi_clock_converter.xci \
  ${HDK_IP_SRC_DIR}/cl_axi_clock_converter_light/cl_axi_clock_converter_light.xci
]

# Additional IP's that might be needed if using the DDR
# read_ip [ list \
#  $HDK_SHELL_DESIGN_DIR/ip/ddr4_core/ddr4_core.xci
# ]
read_ip [ list \
  ${HDK_IP_SRC_DIR}/cl_ddr4_32g/cl_ddr4_32g.xci \
  ${HDK_IP_SRC_DIR}/cl_ddr4_32g_ap/cl_ddr4_32g_ap.xci \
  ${HDK_IP_SRC_DIR}/cl_ddr4/cl_ddr4.xci \
  ${HDK_IP_SRC_DIR}/cl_ddr4_64g_ap/cl_ddr4_64g_ap.xci
]
# read_bd [ list \
#  $HDK_SHELL_DESIGN_DIR/ip/cl_axi_interconnect/cl_axi_interconnect.bd
# ]
read_ip [ list \
 ${HDK_IP_SRC_DIR}/cl_axi_interconnect/cl_axi_interconnect.xci \
 ${HDK_IP_SRC_DIR}/cl_axi_interconnect_64G_ddr/cl_axi_interconnect_64G_ddr.xci
]

puts "AWS FPGA: Reading AWS constraints";

#Read all the constraints
#
#  cl_clocks_aws.xdc  - AWS auto-generated clock constraint.   ***DO NOT MODIFY***
#  cl_ddr.xdc         - AWS provided DDR pin constraints.      ***DO NOT MODIFY***
#  cl_synth_user.xdc  - Developer synthesis constraints.
read_xdc [ list \
   $CL_DIR/build/constraints/generated_cl_clocks_aws.xdc \
   $HDK_SHELL_DIR/build/constraints/cl_ddr_timing_aws.xdc \
   $CL_DIR/build/constraints/cl_synth_user.xdc \
   $CL_DIR/design/FireSim-generated.synthesis.xdc \
]
#    $HDK_SHELL_DIR/build/constraints/cl_synth_aws.xdc \

# FireSim custom clocking
# source $CL_DIR/build/scripts/synth_firesim_clk_wiz.tcl

#Do not propagate local clock constraints for clocks generated in the SH
set_property USED_IN {synthesis implementation OUT_OF_CONTEXT} [get_files generated_cl_clocks_aws.xdc]
set_property PROCESSING_ORDER EARLY  [get_files generated_cl_clocks_aws.xdc]

###############################################################################
print "Reading user constraints"
###############################################################################

read_xdc [ list \
  ${constraints_dir}/cl_synth_user.xdc \
  ${constraints_dir}/cl_timing_user.xdc
]

set_property PROCESSING_ORDER LATE [get_files cl_synth_user.xdc]
set_property PROCESSING_ORDER LATE [get_files cl_timing_user.xdc]

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


# puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Start design synthesis.";

# update_compile_order -fileset sources_1
# puts "\nRunning synth_design for $CL_MODULE $CL_DIR/build/scripts \[[clock format [clock seconds] -format {%a %b %d %H:%M:%S %Y}]\]"
# # eval [concat synth_design -top $CL_MODULE -verilog_define XSDB_SLV_DIS $VDEFINES -part [xcvu47p-fsvh2892-2-e] -mode out_of_context $synth_options -directive $synth_directive]
# eval [concat synth_design -top $CL_MODULE -verilog_define XSDB_SLV_DIS $VDEFINES -mode out_of_context]

set failval [catch {exec grep "FAIL" failfast.csv}]
if { $failval==0 } {
	puts "AWS FPGA: FATAL ERROR--Resource utilization error; check failfast.csv for details"
	exit 1
}

# set timestamp [{date +"%y_%m_%d-%H%M%S"}]
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