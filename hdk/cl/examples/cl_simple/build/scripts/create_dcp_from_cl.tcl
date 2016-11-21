## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## create_cl.tcl: Build to generate CL design checkpoint based on
## 		developer code
## =============================================================================


#################################################
## Generate CL_routed.dcp (Done by User)
#################################################
puts "AWS FPGA Scripts";
puts "Creating Design Checkpoint from Custom Logic source code";

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
        puts "Using CL directory $HDK_SHELL_DIR";
} else {
        puts "Error: HDK_SHELL_DIR environment variable not defined ! ";
        puts "Run the hdk_setup.sh script from the root directory of aws-fpga";
        exit 2
}

#Convenience to set the root of the RTL directory
set systemtime [clock seconds]
set timestamp [clock format $systemtime -gmt 1 -format {%y_%m_%d-%H%M}]

puts "All reports and intermediate results will be time stamped with $timestamp";

file mkdir ../src_post_encryption

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
#read_verilog {
#   $CL_DIR/src_post_encryption/cl_simple_defines.vh
#}
#set_property file_type {Verilog Header} [get_files ../src/cl_simple_defines.vh ]
#set_property is_global_include true [get_files ../src/cl_simple_defines.vh ]

#User design files (these are the files that were encrypted by encrypt.tcl)
read_verilog [ list \
$CL_DIR/src_post_encryption/cl_simple.sv \
$CL_DIR/src_post_encryption/cl_tst.sv \
$CL_DIR/src_post_encryption/cl_int_tst.sv \
$CL_DIR/src_post_encryption/mem_scrb.sv \
$CL_DIR/src_post_encryption/cl_tst_scrb.sv
]

#---- End of section replaced by User ----

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
$HDK_SHELL_DIR/design/cl/cl_ports.vh \
$HDK_SHELL_DIR/design/sh/sh_ddr.sv
]

#Read DDR IP
read_ip {
$HDL_SHELL_DIR/design/ip/ddr4_core/ddr4_core.xci
}

#Note Developer can add IP 

#Read all the constraints
#
#  cl_synth_aws.xdc - AWS provided constraints.  ***DO NOT MODIFY***
#  cl_clocks_aws.xdc - AWS provided clock constraint.  ***DO NOT MODIFY***
#  ddr.xdc - AWS provided DDR pin constraints.  ***DO NOT MODIFY***
#  cl_synt_user.xdc - User constraints.  User can add constraints to this file (or include more constraints as needed)
read_xdc {
   $HDK_SHELL_DIR/build/constraints/cl_synth_aws.xdc
   $HDK_SHELL_DIR/build/constraints/cl_clocks_aws.xdc
   $HDK_SHELL_DIR/build/constraints/ddr.xdc
   $HDK_SHELL_DIR/build/constraints/cl_synth_user.xdc
}

#Do not propagate local clock constraints for clocks generated in the SH
set_property USED_IN {synthesis OUT_OF_CONTEXT} [get_files cl_clocks_aws.xdc]

update_compile_order -fileset sources_1
set_property verilog_define XSDB_SLV_DIS [current_fileset]

########################
# CL Synthesis
########################
synth_design -top cl_simple -verilog_define XSDB_SLV_DIS -verilog_define CL_SECOND -part [DEVICE_TYPE] -mode out_of_context  -keep_equivalent_registers -flatten_hierarchy rebuilt
opt_design -verbose -directive Explore
check_timing -file $CL_DIR/build/reports/${timestamp}.cl.synth.check_timing_report.txt
report_timing_summary -file $CL_DIR/build/reports/${timestamp}.cl.synth.timing_summary.rpt
write_checkpoint -force $CL_DIR/build/checkpoints/${timestamp}.CL.post_synth_opt.dcp
close_design

#######################
# Implementation
#######################
#Read in the Shell checkpoint and do the CL implementation
open_checkpoint $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
read_checkpoint -strict -cell CL $CL_DIR/build/checkpoints/${timestamp}.CL.post_synth_opt.dcp

#Read the constraints, note *DO NOT* read cl_clocks_aws (clocks originating from AWS shell)
read_xdc {
$CL_DIR/build/constraints/cl_pnr_aws.xdc
$CL_DIR/build/constraints/cl_pnr_user.xdc
$CL_DIR/build/constraints/ddr.xdc
}

opt_design -verbose -directive Explore
check_timing -file $CL_DIR/build/reports/${timestamp}.SH_CL.check_timing_report.txt

#place_design -verbose -directive Explore
place_design -verbose -directive WLDrivenBlockPlacement
write_checkpoint -force $CL_DIR/build/checkpoints/${timestamp}.SH_CL.post_place.dcp

phys_opt_design -verbose -directive Explore
report_timing_summary -file $CL_DIR/build/reports/${timestamp}.cl.post_place_opt.timing_summary.rpt
write_checkpoint -force $CL_DIR/build/checkpoints/${timestamp}.SH_CL.post_place_opt.dcp

#route_design  -verbose -directive Explore
route_design  -verbose -directive MoreGlobalIterations

phys_opt_design -verbose -directive Explore

lock_design -level routing

report_timing_summary -file $CL_DIR/build/reports/${timestamp}.SH_CL.post_route_opt.timing_summary.rpt

#This is what will deliver to AWS
write_checkpoint -force $CL_DIR/build/to_aws/${timestamp}.SH_CL_routed.dcp

#Verify PR build
pr_verify -full_check $CL_DIR/build/to_aws/${timestamp}.SH_CL_routed.dcp $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp -o $CL_DIR/build/to_aws/${timestamp}.pr_verify.log

close_design

# created a zipped tar file, that would be used for createFpgaImage EC2 API
exec tar cvfz ${timestamp}.Developer_CL.tar.gz $CL_DIR/build/to_aws/*

