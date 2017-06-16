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

package require tar

set top top_sp
set TOP cl_dram_dma
 
#################################################
## Command-line Arguments
#################################################
set timestamp           [lindex $argv  0]
set strategy            [lindex $argv  1]
set hdk_version         [lindex $argv  2]
set shell_version       [lindex $argv  3]
set device_id           [lindex $argv  4]
set vendor_id           [lindex $argv  5]
set subsystem_id        [lindex $argv  6]
set subsystem_vendor_id [lindex $argv  7]
set clock_recipe_a      [lindex $argv  8]
set clock_recipe_b      [lindex $argv  9]
set clock_recipe_c      [lindex $argv 10]
set notify_via_sns      [lindex $argv 11]

##################################################
### Implementation step options 
##################################################
#Set psip to 1 to enable Physical Synthesis in Placer (2017.1+ only)
set psip 1

set opt 1
set opt_options    "-verbose"
set opt_directive  "ExploreWithRemap"
set opt_preHookTcl ""

set place 1
set place_options    ""
set place_directive  "Explore"
#Prohbit sites to avoid congestion if utilization is low enough

set place_preHookTcl ""

set phys_opt 1
set phys_options    ""
set phys_directive  "Explore"
set phys_preHookTcl ""

set route 1
set route_options    ""
set route_directive  "Explore"
set route_preHookTcl ""

set route_phys_opt 1
set post_phys_options    ""
set post_phys_directive  "Explore"
set post_phys_preHookTcl ""


#################################################
## Generate CL_routed.dcp (Done by User)
#################################################
puts "AWS FPGA Scripts";
puts "Creating Design Checkpoint from Custom Logic source code";
puts "HDK Version:            $hdk_version";
puts "Shell Version:          $shell_version";
puts "Vivado Script Name:     $argv0";
puts "Strategy:               $strategy";
puts "PCI Device ID           $device_id";
puts "PCI Vendor ID           $vendor_id";
puts "PCI Subsystem ID        $subsystem_id";
puts "PCI Subsystem Vendor ID $subsystem_vendor_id";
puts "Clock Recipe A:         $clock_recipe_a";
puts "Clock Recipe B:         $clock_recipe_b";
puts "Clock Recipe C:         $clock_recipe_c";
puts "Notify when done:       $notify_via_sns";

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

#checking if HDK_SHELL_DESIGN_DIR env variable exists
if { [info exists ::env(HDK_SHELL_DESIGN_DIR)] } {
        set HDK_SHELL_DESIGN_DIR $::env(HDK_SHELL_DESIGN_DIR)
        puts "Using Shell design directory $HDK_SHELL_DESIGN_DIR";
} else {
        puts "Error: HDK_SHELL_DESIGN_DIR environment variable not defined ! ";
        puts "Run the hdk_setup.sh script from the root directory of aws-fpga";
        exit 2
}

puts "All reports and intermediate results will be time stamped with $timestamp";

set_msg_config -severity INFO -suppress
set_msg_config -severity STATUS -suppress
set_msg_config -id {Chipscope 16-3} -suppress
set_msg_config -string {AXI_QUAD_SPI} -suppress

# Suppress Warnings
# These are to avoid warning messages that may not be real issues. A developer
# may comment them out if they wish to see more information from warning
# messages.
set_msg_config -id {Common 17-55}         -suppress
set_msg_config -id {Constraints 18-4434}  -suppress
set_msg_config -id {Constraints 18-550}   -suppress
set_msg_config -id {Constraints 18-619}   -suppress
set_msg_config -id {Coretcl 2-64}         -suppress
set_msg_config -id {Designutils 20-1567}  -suppress
set_msg_config -id {DRC 23-20}            -suppress
set_msg_config -id {Opt 31-155}           -suppress
set_msg_config -id {Physopt 32-742}       -suppress
set_msg_config -id {Place 46-14}          -suppress
set_msg_config -id {Route 35-39}          -suppress
set_msg_config -id {Synth 8-115}          -suppress
set_msg_config -id {Synth 8-152}          -suppress
set_msg_config -id {Synth 8-3295}         -suppress
set_msg_config -id {Synth 8-3321}         -suppress
set_msg_config -id {Synth 8-3331}         -suppress
set_msg_config -id {Synth 8-3332}         -suppress
set_msg_config -id {Synth 8-350}          -suppress
set_msg_config -id {Synth 8-3848}         -suppress
set_msg_config -id {Synth 8-3917}         -suppress
set_msg_config -id {Synth 8-3936}         -suppress
set_msg_config -id {Timing 38-436}        -suppress
set_msg_config -id {Vivado 12-1008}       -suppress

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Calling the encrypt.tcl.";

# Check that an email address has been set, else unset notify_via_sns

if {[string compare $notify_via_sns "1"] == 0} {
  if {![info exists env(EMAIL)]} {
    puts "AWS FPGA: ([clock format [clock seconds] -format %T]) EMAIL variable empty!  Completition notification will *not* be sent!";
    set notify_via_sns 0;
  } else {
    puts "AWS FPGA: ([clock format [clock seconds] -format %T]) EMAIL address for completion notification set to $env(EMAIL).";
  }
}

source encrypt.tcl
#This sets the Device Type
source $HDK_SHELL_DIR/build/scripts/device_type.tcl
source $HDK_SHELL_DIR/build/scripts/step.tcl -notrace

##################################################
### Tcl Procs and Params 
##################################################
if {[string match "2017.1*" [version -short]]} {
   ####Turn off power opt in opt_design for improved QoR
   set_param logicopt.enablePowerLopt false

   ####Forcing global router ON for improved QoR 
   set_param route.gr.minGRCongLevel 0
   set_param route.gr.minNumNets     1

   ####Disable timing relaxation in router for improved QoR
   set_param route.ignTgtRelaxFactor true
   set_param route.dlyCostCoef 1.141

   ####Enable support of clocking from one RP to another (SH-->CL)
   set_param hd.supportClockNetCrossDiffReconfigurablePartitions 1 
}

##################################################
### Source and Output Directories 
##################################################
set synthDir  "../synthesis_user_sda"
set implDir   "../implement_user_sda"
set rptDir    "../reports_user_sda"

##################################################
### Create output Directories 
##################################################
if {![file exists $synthDir]} {
   file mkdir $synthDir
}

if {![file exists $implDir]} {
   file mkdir $implDir
}

if {![file exists $rptDir]} {
   file mkdir $rptDir
}

create_project -in_memory -part [DEVICE_TYPE] -force

#set_param chipscope.enablePRFlow true
#Param needed to avoid clock name collisions
set_param sta.enableAutoGenClkNamePersistence 0

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

read_verilog -sv [ glob $ENC_SRC_DIR/*.{v,sv} ]

#---- End of section replaced by User ----

puts "AWS FPGA: Reading AWS Shell design";

#Read AWS Design files
read_verilog [ list \
  $HDK_SHELL_DESIGN_DIR/lib/lib_pipe.sv \
  $HDK_SHELL_DESIGN_DIR/lib/bram_2rw.sv \
  $HDK_SHELL_DESIGN_DIR/lib/flop_fifo.sv \
  $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/sync.v \
  $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/flop_ccf.sv \
  $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/ccf_ctl.v \
  $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/mgt_acc_axl.sv  \
  $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/mgt_gen_axl.sv  \
  $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/sh_ddr.sv \
  $HDK_SHELL_DESIGN_DIR/interfaces/cl_ports.vh 
]

puts "AWS FPGA: Reading IP blocks";
#Read DDR IP
read_ip [ list \
  $HDK_SHELL_DESIGN_DIR/ip/ddr4_core/ddr4_core.xci 
]

#Read IP for axi register slices
read_ip [ list \
  $HDK_SHELL_DESIGN_DIR/ip/src_register_slice/src_register_slice.xci \
  $HDK_SHELL_DESIGN_DIR/ip/axi_clock_converter_0/axi_clock_converter_0.xci \
  $HDK_SHELL_DESIGN_DIR/ip/dest_register_slice/dest_register_slice.xci \
  $HDK_SHELL_DESIGN_DIR/ip/axi_register_slice/axi_register_slice.xci \
  $HDK_SHELL_DESIGN_DIR/ip/axi_register_slice_light/axi_register_slice_light.xci
]

#Read IP for virtual jtag / ILA/VIO
read_ip [ list \
  $HDK_SHELL_DESIGN_DIR/ip/cl_debug_bridge/cl_debug_bridge.xci \
  $HDK_SHELL_DESIGN_DIR/ip/ila_1/ila_1.xci \
  $HDK_SHELL_DESIGN_DIR/ip/ila_vio_counter/ila_vio_counter.xci \
  $HDK_SHELL_DESIGN_DIR/ip/vio_0/vio_0.xci
]
read_bd [ list \
  $HDK_SHELL_DESIGN_DIR/ip/cl_axi_interconnect/cl_axi_interconnect.bd
]

puts "AWS FPGA: Reading AWS constraints";

#Read all the constraints
#
#  cl_clocks_aws.xdc  - AWS auto-generated provided clock constraint.   ***DO NOT MODIFY***
#  cl_ddr.xdc         - AWS provided DDR pin constraints.               ***DO NOT MODIFY***
#  cl_synth_user.xdc  - Developer synthesis constraints.
read_xdc [ list \
   $CL_DIR/build/constraints/cl_clocks_aws.xdc \
   $HDK_SHELL_DIR/build/constraints/cl_synth_aws.xdc \
   $HDK_SHELL_DIR/build/constraints/cl_ddr.xdc \
   $CL_DIR/build/constraints/cl_synth_user.xdc
]

#Do not propagate local clock constraints for clocks generated in the SH
#set_property USED_IN {synthesis OUT_OF_CONTEXT} [get_files cl_clocks_aws.xdc]
set_property USED_IN {synthesis implementation OUT_OF_CONTEXT} [get_files cl_clocks_aws.xdc]
set_property USED_IN {synthesis implementation} [get_files cl_synth_aws.xdc]
set_property PROCESSING_ORDER EARLY  [get_files cl_clocks_aws.xdc]
set_property PROCESSING_ORDER LATE   [get_files cl_synth_aws.xdc]

########################
# CL Synthesis
########################
puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Start design synthesis.";

update_compile_order -fileset sources_1

switch $strategy {
    "BASIC" {
        puts "BASIC strategy."
        synth_design -top $TOP -verilog_define XSDB_SLV_DIS -part [DEVICE_TYPE] -mode out_of_context  -keep_equivalent_registers -flatten_hierarchy rebuilt > $synthDir/${TOP}_synth.log
    }
    "EXPLORE" {
        puts "EXPLORE strategy."
        synth_design -top $TOP -verilog_define XSDB_SLV_DIS -part [DEVICE_TYPE] -mode out_of_context  -keep_equivalent_registers -flatten_hierarchy rebuilt > $synthDir/${TOP}_synth.log 
    }
    "TIMING" {
        puts "TIMING strategy."
        synth_design -top $TOP -verilog_define XSDB_SLV_DIS -part [DEVICE_TYPE] -mode out_of_context -no_lc -shreg_min_size 5 -fsm_extraction one_hot -resource_sharing off > $synthDir/${TOP}_synth.log 
    }
    "CONGESTION" {
        puts "CONGESTION strategy."
        synth_design -top $TOP -verilog_define XSDB_SLV_DIS -part [DEVICE_TYPE] -mode out_of_context -directive AlternateRoutability -no_lc -shreg_min_size 10 -control_set_opt_threshold 16 > $synthDir/${TOP}_synth.log 
    }
    "DEFAULT" {
        puts "DEFAULT strategy."
        synth_design -top $TOP -verilog_define XSDB_SLV_DIS -part [DEVICE_TYPE] -mode out_of_context  -keep_equivalent_registers > $synthDir/${TOP}_synth.log
    }
    default {
        puts "$strategy is NOT a valid strategy."
    }
}

set failval [catch {exec grep "FAIL" failfast.csv}]
if { $failval==0 } {
	puts "AWS FPGA: FATAL ERROR--Resource utilization error; check failfast.csv for details"
	exit 1
}

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) writing post synth checkpoint.";

write_checkpoint -force $CL_DIR/build/checkpoints/${timestamp}.CL.post_synth.dcp
close_project

#Set param back to default value
set_param sta.enableAutoGenClkNamePersistence 1

########################
# CL Optimize
########################

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Optimizing design.";

# Implementation
#Read in the Shell checkpoint and do the CL implementation

puts "AWS FPGA: Implementation step -Combining Shell and CL design checkpoints";

#open_checkpoint $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
#read_checkpoint -strict -cell CL $CL_DIR/build/checkpoints/${timestamp}.CL.post_synth.dcp
add_files $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
add_files $CL_DIR/build/checkpoints/${timestamp}.CL.post_synth.dcp
set_property SCOPED_TO_CELLS {CL} [get_files $CL_DIR/build/checkpoints/${timestamp}.CL.post_synth.dcp]

#Read the constraints, note *DO NOT* read cl_clocks_aws (clocks originating from AWS shell)
read_xdc [ list \
   $HDK_SHELL_DIR/build/constraints/cl_pnr_aws.xdc \
   $CL_DIR/build/constraints/cl_pnr_user.xdc \
   $HDK_SHELL_DIR/build/constraints/cl_ddr.xdc
]
set_property PROCESSING_ORDER late [get_files cl_pnr_user.xdc]

link_design -top $top -part [DEVICE_TYPE] -reconfig_partitions {SH CL}

puts "Writing post-link_design checkpoint $implDir/$top.post_link.dcp"
write_checkpoint -force $implDir/$top.post_link_design.dcp > $implDir/checkpoint.log

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Sourcing aws_clock_properties.tcl to apply properties to clocks. ";

# Apply properties to clocks
source $HDK_SHELL_DIR/build/scripts/aws_clock_properties.tcl

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Optimize design during implementation. ";

switch $strategy {
    "BASIC" {
        puts "BASIC strategy."
        opt_design
    }
    "EXPLORE" {
        puts "EXPLORE strategy."
        opt_design -directive Explore
    }
    "TIMING" {
        puts "TIMING strategy."
        opt_design -directive Explore
    }
    "CONGESTION" {
        puts "CONGESTION strategy."
        opt_design -bufg_opt -control_set_merge -hier_fanout_limit 512 -muxf_remap -propconst -retarget -sweep
    }
    "DEFAULT" {
        puts "DEFAULT strategy."
        impl_step opt_design $top $opt_options $opt_directive $opt_preHookTcl
        if {$psip} {
           impl_step opt_design $top "-merge_equivalent_drivers -sweep"
        }
    }
    default {
        puts "$strategy is NOT a valid strategy."
    }
}

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

########################
# CL Place
########################
puts "AWS FPGA: Place design stage";

# Constraints for TCK<->Main Clock
set_clock_groups -name tck_clk_main_a0 -asynchronous -group [get_clocks -of_objects [get_pins static_sh/SH_DEBUG_BRIDGE/inst/bsip/inst/USE_SOFTBSCAN.U_TAP_TCKBUFG/O]] -group [get_clocks -of_objects [get_pins SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/mmcme3_adv_inst/CLKOUT0]]
set_clock_groups -name tck_drck -asynchronous -group [get_clocks -of_objects [get_pins static_sh/SH_DEBUG_BRIDGE/inst/bsip/inst/USE_SOFTBSCAN.U_TAP_TCKBUFG/O]] -group [get_clocks drck]
set_clock_groups -name tck_userclk -asynchronous -group [get_clocks -of_objects [get_pins static_sh/SH_DEBUG_BRIDGE/inst/bsip/inst/USE_SOFTBSCAN.U_TAP_TCKBUFG/O]] -group [get_clocks -of_objects [get_pins static_sh/pcie_inst/inst/gt_top_i/diablo_gt.diablo_gt_phy_wrapper/phy_clk_i/bufg_gt_userclk/O]]

switch $strategy {
    "BASIC" {
        puts "BASIC strategy."
        place_design
    }
    "EXPLORE" {
        puts "EXPLORE strategy."
        place_design -directive Explore
    }
    "TIMING" {
        puts "TIMING strategy."
        place_design -directive ExtraNetDelay_high
    }
    "CONGESTION" {
        puts "CONGESTION strategy."
        place_design -directive AltSpreadLogic_medium
    }
    "DEFAULT" {
        puts "DEFAULT strategy."
        if {$psip} {
           append place_options " -fanout_opt"
        }
        impl_step place_design $top $place_options $place_directive $place_preHookTcl
    }
    default {
        puts "$strategy is NOT a valid strategy."
    }
}

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Writing checkpoint post place.";

write_checkpoint -force $CL_DIR/build/checkpoints/${timestamp}.SH_CL.post_place.dcp

###########################
# CL Physical Optimization
###########################

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Physical optimization stage.";

switch $strategy {
    "BASIC" {
        puts "BASIC strategy."
    }
    "EXPLORE" {
        puts "EXPLORE strategy."
        phys_opt_design -directive Explore
    }
    "TIMING" {
        puts "TIMING strategy."
        phys_opt_design -directive Explore
    }
    "CONGESTION" {
        puts "CONGESTION strategy."
        phys_opt_design -directive Explore
    }
    "DEFAULT" {
        puts "DEFAULT strategy."
        impl_step phys_opt_design $top $phys_options $phys_directive $phys_preHookTcl
    }
    default {
        puts "$strategy is NOT a valid strategy."
    }
}

########################
# CL Route
########################

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Physical optimization stage.";

switch $strategy {
    "BASIC" {
        puts "BASIC strategy."
        route_design
    }
    "EXPLORE" {
        puts "EXPLORE strategy."
        route_design -directive Explore
    }
    "TIMING" {
        puts "TIMING strategy."
        route_design -directive Explore -tns_cleanup
    }
    "CONGESTION" {
        puts "CONGESTION strategy."
        route_design -directive Explore
    }
    "DEFAULT" {
        puts "DEFAULT strategy."
        impl_step route_design $top $route_options $route_directive $route_preHookTcl
    }
    default {
        puts "$strategy is NOT a valid strategy."
    }
}

#################################
# CL Final Physical Optimization
#################################

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Post-route Physical optimization stage. ";

switch $strategy {
    "BASIC" {
        puts "BASIC strategy."
    }
    "EXPLORE" {
        #puts "EXPLORE strategy."        
    }
    "TIMING" {
        puts "TIMING strategy."
        phys_opt_design  -directive Explore
    }
    "CONGESTION" {
        puts "CONGESTION strategy."
    }
    "DEFAULT" {
        puts "DEFAULT strategy."
        set SLACK [get_property SLACK [get_timing_paths]]
        if {$route_phys_opt && $SLACK > -0.400 && $SLACK < 0} {
           impl_step route_phys_opt_design $top $post_phys_options $post_phys_directive $post_phys_preHookTcl
        }
    }
    default {
        puts "$strategy is NOT a valid strategy."
    }
}

# Lock the design to preserve the placement and routing
puts "AWS FPGA: Locking design ";
lock_design -level routing

# Report final timing
report_timing_summary -file $CL_DIR/build/reports/${timestamp}.SH_CL_final_timing_summary.rpt

# This is what will deliver to AWS

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) writing final DCP to to_aws directory.";

write_checkpoint -force $CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp

# Generate debug probes file
write_debug_probes -force -no_partial_ltxfile -file $CL_DIR/build/checkpoints/${timestamp}.debug_probes.ltx

close_project

# ################################################
# Create Manifest and Tarball for delivery
# ################################################

# Create a zipped tar file, that would be used for createFpgaImage EC2 API

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Compress files for sending to AWS. "

# Create manifest file
set manifest_file [open "$CL_DIR/build/checkpoints/to_aws/${timestamp}.manifest.txt" w]
set hash [lindex [split [exec sha256sum $CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp] ] 0]

puts $manifest_file "manifest_format_version=1\n"
puts $manifest_file "pci_vendor_id=$vendor_id\n"
puts $manifest_file "pci_device_id=$device_id\n"
puts $manifest_file "pci_subsystem_id=$subsystem_id\n"
puts $manifest_file "pci_subsystem_vendor_id=$subsystem_vendor_id\n"
puts $manifest_file "dcp_hash=$hash\n"
puts $manifest_file "shell_version=$shell_version\n"
puts $manifest_file "dcp_file_name=${timestamp}.SH_CL_routed.dcp\n"
puts $manifest_file "hdk_version=$hdk_version\n"
puts $manifest_file "date=$timestamp\n"
puts $manifest_file "clock_recipe_a=$clock_recipe_a\n"
puts $manifest_file "clock_recipe_b=$clock_recipe_b\n"
puts $manifest_file "clock_recipe_c=$clock_recipe_c\n"

close $manifest_file

# Delete old tar file with same name
if { [file exists $CL_DIR/build/checkpoints/to_aws/${timestamp}.Developer_CL.tar] } {
        puts "Deleting old tar file with same name.";
        file delete -force $CL_DIR/build/checkpoints/to_aws/${timestamp}.Developer_CL.tar
}

# Tar checkpoint to aws
cd $CL_DIR/build/checkpoints
tar::create to_aws/${timestamp}.Developer_CL.tar [glob to_aws/${timestamp}*]

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Finished creating final tar file in to_aws directory.";

if {[string compare $notify_via_sns "1"] == 0} {
  puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Calling notification script to send e-mail to $env(EMAIL)";
  exec $env(HDK_COMMON_DIR)/scripts/notify_via_sns.py
}

