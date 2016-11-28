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

#Convenience to set the root of the RTL directory
set RTL_ORIGIN ../../../rtl
set systemtime [clock seconds]
set timestamp [clock format $systemtime -gmt 1 -format {%y_%m_%d-%H%M}]

source encrypt.tcl

#This sets the Device Type
source ./device_type.tcl

create_project -in_memory -part [DEVICE_TYPE] -force

#set_param chipscope.enablePRFlow true

#############################
## Read design files
#############################

#---- User would replace this section -----

#Global defines (this is specific to the CL design).  This file is encrypted by encrypt.tcl
read_verilog {
   ../src/cl_simple_defines.vh
}
set_property file_type {Verilog Header} [get_files ../src/cl_simple_defines.vh ]
set_property is_global_include true [get_files ../src/cl_simple_defines.vh ]

#User design files (these are the files that were encrypted by encrypt.tcl)
read_verilog {
../src/cl_simple.sv
../src/cl_tst.sv
../src/cl_int_tst.sv
../src/mem_scrb.sv
../src/cl_tst_scrb.sv
}

#---- End of section replaced by User ----

#Read AWS Design files
read_verilog [ list \
$RTL_ORIGIN/lib/flop_fifo.sv \
$RTL_ORIGIN/lib/flop_fifo_in.sv \
$RTL_ORIGIN/lib/bram_2rw.sv \
$RTL_ORIGIN/lib/flop_ccf.sv \
$RTL_ORIGIN/lib/ccf_ctl.v \
$RTL_ORIGIN/lib/sync.v \
$RTL_ORIGIN/lib/axi4_ccf.sv \
$RTL_ORIGIN/lib/axi4_flop_fifo.sv \
$RTL_ORIGIN/lib/lib_pipe.sv \
$RTL_ORIGIN/mgt/mgt_acc_ccf.sv \
$RTL_ORIGIN/mgt/mgt_acc_axl.sv  \
$RTL_ORIGIN/mgt/mgt_gen_axl.sv  \
$RTL_ORIGIN/cl/cl_ports.vh \
$RTL_ORIGIN/sh/sh_ddr.sv
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
   ../constraints/cl_synth_aws.xdc
   ../constraints/cl_clocks_aws.xdc
   ../constraints/ddr.xdc
   ../constraints/cl_synth_user.xdc
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
check_timing -file ../reports/cl.synth.check_timing_report.txt
report_timing_summary -file ../reports/cl.synth.timing_summary.rpt
write_checkpoint -force ../checkpoints/CL.post_synth_opt.dcp
close_design

#######################
# Implementation
#######################
#Read in the Shell checkpoint and do the CL implementation
open_checkpoint ../checkpoints/from_aws/SH_CL_BB_routed.dcp
read_checkpoint -strict -cell CL ../checkpoints/CL.post_synth_opt.dcp

#Read the constraints, note *DO NOT* read cl_clocks_aws (clocks originating from SH)
read_xdc {
../constraints/cl_pnr_aws.xdc
../constraints/cl_pnr_user.xdc
../constraints/ddr.xdc
}

opt_design -verbose -directive Explore
check_timing -file ../reports/SH_CL.check_timing_report.txt

#place_design -verbose -directive Explore
place_design -verbose -directive WLDrivenBlockPlacement
write_checkpoint -force ../checkpoints/SH_CL.post_place.dcp

phys_opt_design -verbose -directive Explore
report_timing_summary -file ../reports/cl.post_place_opt.timing_summary.rpt
write_checkpoint -force ../checkpoints/SH_CL.post_place_opt.dcp

#route_design  -verbose -directive Explore
route_design  -verbose -directive MoreGlobalIterations

phys_opt_design -verbose -directive Explore

lock_design -level routing

report_timing_summary -file ../reports/SH_CL.post_route_opt.timing_summary.rpt

#This is what will deliver to AWS
write_checkpoint -force ../to_aws/SH_CL_routed.dcp
file copy -force ../to_aws/SH_CL_routed.dcp ../to_aws/${timestamp}.SH_CL_routed.dcp

#Verify PR build
pr_verify -full_check ../to_aws/SH_CL_routed.dcp ../checkpoints/from_aws/SH_CL_BB_routed.dcp -o ../to_aws/${timestamp}.pr_verify.log

close_design

exec tar cvfz ${timestamp}.Developer_CL.tar.gz ../to_aws/*

