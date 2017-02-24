## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## create_cl.tcl: Build to generate CL design checkpoint based on
## 		developer code
## =============================================================================

package require tar

#################################################
## Generate CL_routed.dcp (Done by User)
#################################################
puts "AWS FPGA Scripts";
puts "Creating Design Checkpoint from Custom Logic source code";
puts "Shell Version: VenomCL_unc - 0x11241611";

#checking if CL_DIR env variable exists
if { [info exists ::env(CL_DIR)] } {
        set CL_DIR $::env(CL_DIR)
        puts "Using CL directory $CL_DIR";
} else {
        puts "Error: CL_DIR environment variable not defined ! ";
        puts "Use export CL_DIR=Your_Design_Root_Directory"
        exit 2
}

#checking if HDK_SHELL_DIR env variable exists
if { [info exists ::env(HDK_SHELL_DIR)] } {
        set HDK_SHELL_DIR $::env(HDK_SHELL_DIR)
        puts "Using Shell directory $HDK_SHELL_DIR";
} else {
        puts "Error: HDK_SHELL_DIR environment variable not defined ! ";
        puts "Run the hdk_setup.sh script from the root directory of aws-fpga";
        exit 2
}

#Convenience to set the root of the RTL directory
set systemtime [clock seconds]
set timestamp [clock format $systemtime -gmt 1 -format {%y_%m_%d-%H%M}]

puts "All reports and intermediate results will be time stamped with $timestamp";

set_msg_config -severity INFO -suppress
set_msg_config -severity STATUS -suppress
set_msg_config -severity WARNING -suppress
set_msg_config -id {Chipscope 16-3} -suppress
set_msg_config -string {AXI_QUAD_SPI} -suppress

puts "AWS FPGA: Calling the encrypt.tcl";

source encrypt.tcl

#This sets the Device Type
source $HDK_SHELL_DIR/build/scripts/device_type.tcl

create_project -in_memory -part [DEVICE_TYPE] -force

#set_param chipscope.enablePRFlow true

#############################
## Read design files
#############################

#---- User would replace this section -----

#Global defines (this is specific to the CL design).  This file is encrypted by encrypt.tcl
read_verilog [ list \
   $CL_DIR/build/src_post_encryption/cl_dram_dma_defines.vh
]
set_property file_type {Verilog Header} [get_files $CL_DIR/build/src_post_encryption/cl_dram_dma_defines.vh ]
set_property is_global_include true [get_files $CL_DIR/build/src_post_encryption/cl_dram_dma_defines.vh ]

puts "AWS FPGA: Reading developer's Custom Logic files post encryption";

#User design files (these are the files that were encrypted by encrypt.tcl)
read_verilog [ list \
$CL_DIR/build/src_post_encryption/cl_dram_dma.sv \
$CL_DIR/build/src_post_encryption/cl_tst.sv \
$CL_DIR/build/src_post_encryption/cl_int_tst.sv \
$CL_DIR/build/src_post_encryption/mem_scrb.sv \
$CL_DIR/build/src_post_encryption/cl_tst_scrb.sv \
$CL_DIR/build/src_post_encryption/axil_slave.sv \
$CL_DIR/build/src_post_encryption/src_register_slice.v \
$CL_DIR/build/src_post_encryption/dest_register_slice.v \
$CL_DIR/build/src_post_encryption/axi_crossbar_0.v \
$CL_DIR/build/src_post_encryption/axi_register_slice_v2_1_vl_rfs.v \
$CL_DIR/build/src_post_encryption/axi_crossbar_v2_1_vl_rfs.v \
$CL_DIR/build/src_post_encryption/axi_data_fifo_v2_1_vl_rfs.v \
$CL_DIR/build/src_post_encryption/axi_infrastructure_v1_1_0.vh \
$CL_DIR/build/src_post_encryption/axi_infrastructure_v1_1_vl_rfs.v \
$CL_DIR/build/src_post_encryption/generic_baseblocks_v2_1_vl_rfs.v \
$CL_DIR/build/src_post_encryption/fifo_generator_v13_1_rfs.v
]

#---- End of section replaced by User ----
puts "AWS FPGA: Reading AWS Shell design";

#Read AWS Design files
read_verilog [ list \
$HDK_SHELL_DIR/design/lib/flop_fifo.sv \
$HDK_SHELL_DIR/design/lib/flop_fifo_in.sv \
$HDK_SHELL_DIR/design/lib/bram_2rw.sv \
$HDK_SHELL_DIR/design/lib/flop_ccf.sv \
$HDK_SHELL_DIR/design/lib/ccf_ctl.v \
$HDK_SHELL_DIR/design/lib/sync.v \
$HDK_SHELL_DIR/design/lib/axi4_ccf.sv \
$HDK_SHELL_DIR/design/lib/axi4_flop_fifo.sv \
$HDK_SHELL_DIR/design/lib/lib_pipe.sv \
$HDK_SHELL_DIR/design/lib/mgt_acc_axl.sv  \
$HDK_SHELL_DIR/design/lib/mgt_gen_axl.sv  \
$HDK_SHELL_DIR/design/interfaces/sh_ddr.sv \
$HDK_SHELL_DIR/design/interfaces/cl_ports.vh 
]

puts "AWS FPGA: Reading IP blocks";
#Read DDR IP
read_ip [ list \
$HDK_SHELL_DIR/design/ip/ddr4_core/ddr4_core.xci
]

puts "AWS FPGA: Reading AWS constraints";


#Read all the constraints
#
#  cl_synth_aws.xdc  - AWS provided constraints.          ***DO NOT MODIFY***
#  cl_clocks_aws.xdc - AWS provided clock constraint.     ***DO NOT MODIFY***
#  cl_ddr.xdc        - AWS provided DDR pin constraints.  ***DO NOT MODIFY***
read_xdc [ list \
   $HDK_SHELL_DIR/build/constraints/cl_synth_aws.xdc \
   $HDK_SHELL_DIR/build/constraints/cl_clocks_aws.xdc \
   $HDK_SHELL_DIR/build/constraints/cl_ddr.xdc \
   $CL_DIR/build/constraints/cl_synth_user.xdc
]

#Do not propagate local clock constraints for clocks generated in the SH
set_property USED_IN {synthesis OUT_OF_CONTEXT} [get_files cl_clocks_aws.xdc]

update_compile_order -fileset sources_1
set_property verilog_define XSDB_SLV_DIS [current_fileset]

########################
# CL Synthesis
########################
puts "AWS FPGA: Start design synthesis";

synth_design -top cl_dram_dma -verilog_define XSDB_SLV_DIS -part [DEVICE_TYPE] -mode out_of_context  -keep_equivalent_registers -flatten_hierarchy rebuilt

# Prohibit the top two URAM sites of each URAM quad.
# These two sites cannot be used within PR designs.
set uramSites [get_sites -filter { SITE_TYPE == "URAM288" } ]
foreach uramSite $uramSites {
  # Get the URAM location within a quad
  set quadLoc [expr  [string range $uramSite [expr [string first Y $uramSite] + 1] end] % 4]
  # The top-two sites have usage restrictions
  if {$quadLoc == 2 || $quadLoc == 3} {
    # Prohibit the appropriate site
    set_property PROHIBIT true $uramSite
    puts "Setting Placement Prohibit on $uramSite"
  }
}

set failval [catch {exec grep "FAIL" failfast.csv}]
if { $failval==0 } {
	puts "AWS FPGA: FATAL ERROR--Resource utilization error; check failfast.csv for details"
	exit 1
}

puts "AWS FPGA: Optimizing design";
opt_design -directive Explore

check_timing -file $CL_DIR/build/reports/${timestamp}.cl.synth.check_timing_report.txt
report_timing_summary -file $CL_DIR/build/reports/${timestamp}.cl.synth.timing_summary.rpt
write_checkpoint -force $CL_DIR/build/checkpoints/${timestamp}.CL.post_synth_opt.dcp
close_design

#######################
# Implementation
#######################
#Read in the Shell checkpoint and do the CL implementation
puts "AWS FPGA: Implementation step -Combining Shell and CL design checkpoints";

open_checkpoint $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
read_checkpoint -strict -cell CL $CL_DIR/build/checkpoints/${timestamp}.CL.post_synth_opt.dcp

#Read the constraints, note *DO NOT* read cl_clocks_aws (clocks originating from AWS shell)
read_xdc [ list \
$HDK_SHELL_DIR/build/constraints/cl_pnr_aws.xdc \
$CL_DIR/build/constraints/cl_pnr_user.xdc \
$HDK_SHELL_DIR/build/constraints/cl_ddr.xdc
]

# Prohibit the top two URAM sites of each URAM quad.
# These two sites cannot be used within PR designs.
set uramSites [get_sites -filter { SITE_TYPE == "URAM288" } ]
foreach uramSite $uramSites {
  # Get the URAM location within a quad
  set quadLoc [expr  [string range $uramSite [expr [string first Y $uramSite] + 1] end] % 4]
  # The top-two sites have usage restrictions
  if {$quadLoc == 2 || $quadLoc == 3} {
    # Prohibit the appropriate site
    set_property PROHIBIT true $uramSite
    puts "Setting Placement Prohibit on $uramSite"
  }
}

puts "AWS FPGA: Optimize design during implementation";

opt_design -directive Explore
check_timing -file $CL_DIR/build/reports/${timestamp}.SH_CL.check_timing_report.txt

puts "AWS FPGA: Place design stage";
#place_design -verbose -directive Explore
place_design -directive WLDrivenBlockPlacement
write_checkpoint -force $CL_DIR/build/checkpoints/${timestamp}.SH_CL.post_place.dcp

puts "AWS FPGA: Physical optimization stage";

phys_opt_design -directive Explore
report_timing_summary -file $CL_DIR/build/reports/${timestamp}.cl.post_place_opt.timing_summary.rpt
write_checkpoint -force $CL_DIR/build/checkpoints/${timestamp}.SH_CL.post_place_opt.dcp

puts "AWS FPGA: Route design stage";

#route_design  -verbose -directive Explore
route_design  -directive MoreGlobalIterations

puts "AWS FPGA: Post-route Physical optimization stage ";

phys_opt_design  -directive Explore

puts "AWS FPGA: Locking design ";

lock_design -level routing

report_timing_summary -file $CL_DIR/build/reports/${timestamp}.SH_CL.post_route_opt.timing_summary.rpt

#This is what will deliver to AWS
write_checkpoint -force $CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp

puts "AWS FPGA: Verify compatibility of generated checkpoint with SH checkpoint"

#Verify PR build
pr_verify -full_check $CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp -file $CL_DIR/build/checkpoints/to_aws/${timestamp}.pr_verify.log

### --------------------------------------------
### Emulate what AWS will do
### --------------------------------------------

# Make temp dir for bitstream
file mkdir $CL_DIR/build/aws_verify_temp_dir

# Verify the Developer DCP is compatible with SH_BB. 
pr_verify -full_check $CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
open_checkpoint $CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp
report_timing_summary -file $CL_DIR/build/reports/${timestamp}.SH_CL_final_timing_summary.rpt
report_io -file $CL_DIR/build/reports/${timestamp}.SH_CL_final_report_io.rpt

# Write out the CL DCP to integrate with SH_BB
write_checkpoint -force -cell CL $CL_DIR/build/checkpoints/${timestamp}.CL_routed.dcp
close_design

# Integreate Developer CL with SH BB
open_checkpoint $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
read_checkpoint -strict -cell CL $CL_DIR/build/checkpoints/${timestamp}.CL_routed.dcp
report_drc -file $CL_DIR/build/reports/${timestamp}.SH_CL_final_DRC.rpt
write_checkpoint -force $CL_DIR/build/checkpoints/${timestamp}.SH_CL_final.route.dcp
pr_verify -full_check $CL_DIR/build/checkpoints/${timestamp}.SH_CL_final.route.dcp $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp 
set_param bitstream.enablePR 4123
write_bitstream -force -bin_file $CL_DIR/build/aws_verify_temp_dir/${timestamp}.SH_CL_final.bit

# Clean-up temp dir for bitstream
file delete -force $CL_DIR/build/aws_verify_temp_dir

### --------------------------------------------

# Create a zipped tar file, that would be used for createFpgaImage EC2 API
puts "Compress files for sending back to AWS"

# clean up vivado.log file
exec perl $HDK_SHELL_DIR/build/scripts/clean_log.pl

cd $CL_DIR/build/checkpoints
tar::create to_aws/${timestamp}.Developer_CL.tar [glob  to_aws/${timestamp}*]

close_design

