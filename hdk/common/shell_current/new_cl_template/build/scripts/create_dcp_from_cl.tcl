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

#TODO:
#check if CL_DIR and HDK_COMMON_DIR defined

set systemtime [clock seconds]
set timestamp [clock format $systemtime -gmt 1 -format {%y_%m_%d-%H%M}]

# The next script will encryption and copy the files to the /build/src_port_encryption
# Developer should make sure the tcl script referenced below include all the design files
source encrypt.tcl

#This sets the Device Type, should not change
source $HDK_COMMON_DIR/build/scripts/device_type.tcl

create_project -in_memory -part [DEVICE_TYPE] -force

#set_param chipscope.enablePRFlow true

#############################
## Read design files
#############################

#---- User would replace this section -----

#Global defines (this is specific to the CL design).  This file is encrypted by encrypt.tcl
read_verilog {
   $CL_DIR/build/src_port_encryptin/PUT_YOUR_DESIGN_FILE_NAMES_HERE
}

#if some of your files include a header file, call these two functions
set_property file_type {Verilog Header} [get_files .$CL_DIR/build/src_port_encryptin/cl_simple_defines.vh ]
set_property is_global_include true [get_files $CL_DIR/build/src_port_encryptin/cl_simple_defines.vh ]

#User design files (these are the files that were encrypted by encrypt.tcl)
read_verilog {
$CL_DIR/build/src_port_encryption/cl_simple.sv
# add the other files
}

#---- End of section replaced by User ----

#Read AWS Design files
read_verilog [ list \
$HDK_COMMON_DIR/design/lib/flop_fifo.sv \
$HDK_COMMON_DIR/design/lib/flop_fifo_in.sv \
$HDK_COMMON_DIR/design/lib/bram_2rw.sv \
$HDK_COMMON_DIR/design/lib/flop_ccf.sv \
$HDK_COMMON_DIR/design/lib/ccf_ctl.v \
$HDK_COMMON_DIR/design/lib/sync.v \
$RHDK_COMMON_DIR/design/lib/axi4_ccf.sv \
$HDK_COMMON_DIR/design/lib/axi4_flop_fifo.sv \
$HDK_COMMON_DIR/design/lib/lib_pipe.sv \
$HDK_COMMON_DIR/design/mgt/mgt_acc_ccf.sv \
$HDK_COMMON_DIR/design/mgt/mgt_acc_axl.sv  \
$HDK_COMMON_DIR/design/mgt/mgt_gen_axl.sv  \
$HDK_COMMON_DIR/design/cl/cl_ports.vh \
$HDK_COMMON_DIR/design/sh/sh_ddr.sv
]

#Read DDR IP
read_ip {
../ip/ddr4_core/ddr4_core.xci
}

#Note Developer can add IP 

#Read all the constraints
#
#  cl_synth_aws.xdc - AWS provided constraints.  ***DO NOT MODIFY***
#  cl_clocks_aws.xdc - AWS provided clock constraint.  ***DO NOT MODIFY***
#  ddr.xdc - AWS provided DDR pin constraints.  ***DO NOT MODIFY***
#  cl_synt_user.xdc - User constraints.  User can add constraints to this file (or include more constraints as needed)
read_xdc {
   $HDK_COMMON_DIR/build/constraints/cl_synth_aws.xdc
   $HDK_COMMON_DIR/build/constraints/cl_clocks_aws.xdc
   $HDK_COMMON_DIR/build/constraints/ddr.xdc
   $HDK_COMMON_DIR/build/constraints/cl_synth_user.xdc
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
check_timing -file $CL_DIR/build/reports/cl.synth.check_timing_report.${timestamp}.txt
report_timing_summary -file $CL_DIR/build/reports/cl.synth.timing_summary.${timestamp}.rpt
write_checkpoint -force $CL_DIR/build/checkpoints/CL.post_synth_opt.${timestamp}.dcp
close_design

#######################
# Implementation
#######################
#Read in the Shell checkpoint and do the CL implementation
open_checkpoint $HDK_COMMON_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
read_checkpoint -strict -cell CL $CL_DIR/build/checkpoints/CL.post_synth_opt.dcp

#Read the constraints, note *DO NOT* read cl_clocks_aws (clocks originating from SH)
read_xdc {
$CL_DIR/build/constraints/cl_pnr_aws.xdc
$CL_DIR/build/constraints/cl_pnr_user.xdc
$CL_DIR/build/constraints/ddr.xdc
}

opt_design -verbose -directive Explore
check_timing -file $CL_DIR/build/reports/SH_CL.check_timing_report.txt

#place_design -verbose -directive Explore
place_design -verbose -directive WLDrivenBlockPlacement
write_checkpoint -force $CL_DIR/build/checkpoints/SH_CL.post_place.${timestamp}.dcp

phys_opt_design -verbose -directive Explore
report_timing_summary -file $CL_DIR/build/reports/cl.post_place_opt.timing_summary.${timestamp}.rpt
write_checkpoint -force $CL_DIR/build/SH_CL.post_place_opt.${timestamp}.dcp

#route_design  -verbose -directive Explore
route_design  -verbose -directive MoreGlobalIterations

phys_opt_design -verbose -directive Explore

lock_design -level routing

report_timing_summary -file $CL_DIR/build/reports/SH_CL.post_route_opt.timing_summary.${timestamp}.rpt

#This is what will deliver to AWS
write_checkpoint -force to_aws/SH_CL_routed.dcp
file copy -force $CL_DIR/build/to_aws/SH_CL_routed.dcp ../to_aws/${timestamp}.SH_CL_routed.dcp

#Verify PR build
pr_verify -full_check $CL_DIR/build/to_aws/SH_CL_routed.${timestamp}.dcp $HDK_COMMON_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp -o $CL_DIR/build/to_aws/${timestamp}.pr_verify.log

close_design

exec tar cvfz ${timestamp}.Developer_CL.tar.gz $CL_DIR/build/to_aws/*
