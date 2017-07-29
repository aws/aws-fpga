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
set TOP cl_top

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
set run_aws_emulation   [lindex $argv 11]
set notify_via_sns      [lindex $argv 12]

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
puts "Run AWS Emulation:      $run_aws_emulation";
puts "Notify when done:       $notify_via_sns";

#checking if FAAS_CL_DIR env variable exists
if { [info exists ::env(FAAS_CL_DIR)] } {
        set FAAS_CL_DIR $::env(FAAS_CL_DIR)
        puts "Using CL directory $FAAS_CL_DIR";
} else {
        puts "Error: FAAS_CL_DIR environment variable not defined ! ";
        puts "Use export FAAS_CL_DIR=Your_Design_Root_Directory"
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
#error "break 1"

#set_msg_config -severity INFO -suppress
#set_msg_config -severity STATUS -suppress
set_msg_config -id {Chipscope 16-3} -suppress
set_msg_config -string {AXI_QUAD_SPI} -suppress

# Suppress Warnings
# These are to avoid warning messages that may not be real issues. A developer
# may comment them out if they wish to see more information from warning
# messages.
set_msg_config -id {Constraints 18-550} -suppress
set_msg_config -id {Constraints 18-619} -suppress
set_msg_config -id {DRC 23-20}          -suppress
set_msg_config -id {Physopt 32-742}     -suppress
set_msg_config -id {Place 46-14}        -suppress
set_msg_config -id {Synth 8-3295}       -suppress
set_msg_config -id {Synth 8-3321}       -suppress
set_msg_config -id {Synth 8-3331}       -suppress
set_msg_config -id {Synth 8-3332}       -suppress
set_msg_config -id {Synth 8-350}        -suppress
set_msg_config -id {Synth 8-3848}       -suppress
set_msg_config -id {Synth 8-3917}       -suppress
set_msg_config -id {Timing 38-436}      -suppress
set_msg_config -id {Synth 8-6014}       -suppress
set_msg_config -id {Constraints 18-952} -suppress
set_msg_config -id {DRC CKLD-2}         -suppress
set_msg_config -id {DRC REQP-1853}      -suppress
set_msg_config -id {Route 35-456}       -suppress
set_msg_config -id {Route 35-455}       -suppress
set_msg_config -id {Route 35-459}       -suppress

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

#source encrypt.tcl

##################################################
### Tcl Procs and Params 
##################################################

#if {[string match "2017.1*" [version -short]]} {
   ####Turn off power opt in opt_design for improved QoR
   #set_param logicopt.enablePowerLopt false

   ####Forcing global router ON for improved QoR 
   #set_param route.gr.minGRCongLevel 0
   #set_param route.gr.minNumNets     1

   ####Disable timing relaxation in router for improved QoR
   #set_param route.ignTgtRelaxFactor true
   #set_param route.dlyCostCoef 1.141

   ####Enable support of clocking from one RP to another (SH-->CL)
   set_param hd.supportClockNetCrossDiffReconfigurablePartitions 1

   set_param physynth.ultraRAMOptOutput false


   ####Turn off debug flow DRCs due to false error caused by ECO changes (tck_clk.tcl)
   #set_param chipscope.enablePRFlowDRC 0
#}

#This sets the Device Type
source $HDK_SHELL_DIR/build/scripts/device_type.tcl

#TEMP: copy DCP to the expected place
#BYDEM
#file copy -force /home/jamesl/aws/jeff_ip/616/aws/myproj/project_1.runs/synth_1/cl_top.dcp $FAAS_CL_DIR/build/checkpoints/${timestamp}.CL.post_synth.dcp

########################
# CL Optimize
########################

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Optimizing design.";

# Implementation
#Read in the Shell checkpoint and do the CL implementation

puts "AWS FPGA: Implementation step -Combining Shell and CL design checkpoints";

#open_checkpoint $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
#read_checkpoint -strict -cell CL $FAAS_CL_DIR/build/checkpoints/${timestamp}.CL.post_synth.dcp
add_files $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
#add_files $FAAS_CL_DIR/build/checkpoints/${timestamp}.CL.post_synth.dcp
#set_property SCOPED_TO_CELLS {CL} [get_files $FAAS_CL_DIR/build/checkpoints/${timestamp}.CL.post_synth.dcp]
add_files $FAAS_CL_DIR/build/checkpoints/CL.post_synth.dcp
set_property SCOPED_TO_CELLS {CL} [get_files $FAAS_CL_DIR/build/checkpoints/CL.post_synth.dcp]


#Read the constraints, note *DO NOT* read cl_clocks_aws (clocks originating from AWS shell)
#BYDEM
#read_xdc [ list \
#   $HDK_SHELL_DIR/build/constraints/cl_pnr_aws.xdc \
#   $FAAS_CL_DIR/build/constraints/cl_pnr_user.xdc \
#   $HDK_SHELL_DIR/build/constraints/cl_ddr.xdc
#]
#set_property PROCESSING_ORDER late [get_files cl_pnr_user.xdc]

#BYDEM 062517b4
#read_xdc [ list \
#   $HDK_SHELL_DIR/build/constraints/cl_pnr_aws.xdc \
#   $HDK_SHELL_DIR/build/constraints/cl_ddr.xdc
#]

# not necessary in batch read_xdc ${FAAS_CL_DIR}/build/constraints/aws_gen_clk_constraints.xdc
read_xdc $HDK_SHELL_DIR/build/constraints/cl_ddr.xdc



link_design -top $top -part [DEVICE_TYPE] -reconfig_partitions {SH CL}

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Sourcing aws_clock_properties.tcl to apply properties to clocks. ";

# Apply properties to clocks
source $HDK_SHELL_DIR/build/scripts/aws_clock_properties.tcl

write_checkpoint -force $FAAS_CL_DIR/build/checkpoints/${timestamp}.SH_CL.post_link_design.dcp
puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Optimize design during implementation. ";
source $HDK_SHELL_DIR/build/scripts/check_uram.tcl

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
        opt_design -directive Explore
    }
    default {
        puts "$strategy is NOT a valid strategy."
    }
}

source [file normalize [file join $::env(FAAS_SCRIPT_DIR) subscripts apply_debug_constraints_hlx.tcl]]















########################
# CL Place
########################
puts "AWS FPGA: Place design stage";

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
        place_design -directive ExtraNetDelay_high
    }
    default {
        puts "$strategy is NOT a valid strategy."
    }
}

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Writing checkpoint post place.";

write_checkpoint -force $FAAS_CL_DIR/build/checkpoints/${timestamp}.SH_CL.post_place.dcp

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
        phys_opt_design -directive Explore
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
        route_design -directive Explore
    }
    default {
        puts "$strategy is NOT a valid strategy."
    }
}

#################################
# CL Final Physical Optimization
#################################

   set SLACK [get_property SLACK [get_timing_paths]]
   #Post-route phys_opt will not be run if slack is positive or greater than -200ps.
   if {$SLACK > -0.400 && $SLACK < 0} {
   
puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Post-route Physical optimization stage. ";

switch $strategy {
    "BASIC" {
        puts "BASIC strategy."
    }
    "EXPLORE" {
        puts "EXPLORE strategy."
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
        phys_opt_design  -directive Explore
    }
    default {
        puts "$strategy is NOT a valid strategy."
    }
}
}

# Lock the design to preserve the placement and routing
puts "AWS FPGA: Locking design ";
lock_design -level routing

# Report final timing
#bydem - make the directory
file mkdir $FAAS_CL_DIR/build
file mkdir $FAAS_CL_DIR/build/reports
report_timing_summary -file $FAAS_CL_DIR/build/reports/${timestamp}.SH_CL_final_timing_summary.rpt

# This is what will deliver to AWS

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) writing final DCP to to_aws directory.";

file mkdir $FAAS_CL_DIR/build/checkpoints/to_aws
write_checkpoint -force $FAAS_CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp
close_project

# ################################################
# Emulate AWS Bitstream Generation
# ################################################

# Only run AWS emulation step if explicitly specified.

if {[string compare $run_aws_emulation "1"] == 0} {
  puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Calling aws_dcp_verify.tcl to emulate AWS bitstream generation for checking the DCP.";
  source $HDK_SHELL_DIR/build/scripts/aws_dcp_verify.tcl
}

# ################################################
# Create Manifest and Tarball for delivery
# ################################################

# Create a zipped tar file, that would be used for createFpgaImage EC2 API

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Compress files for sending to AWS. "

# Create manifest file
set manifest_file [open "$FAAS_CL_DIR/build/checkpoints/to_aws/${timestamp}.manifest.txt" w]
#bydem
if {[info exist ::env(OS)] eq 0} {
	put "OS Environment variable not set, assuming Linux"
	set ::env(OS) "linux"
}
if {[string match "*windows*" [string tolower $::env(OS)]]} {
	if {[info exist SCRIPT_DIR] eq 0} {
		set SCRIPT_DIR [file dirname $argv0]
	}
	set sha256sum [file join $SCRIPT_DIR DONOTINCLUDE_INAPP sha256sum.exe]
	if {[file exists $sha256sum] eq 0} {
		puts "Please add sha256sum to your install app tree at $SCRIPT_DIR or hardcode in [file join [file dirname $argv0] $argv0]"
		set hash "MISSING HASH!  HASH NOT RUN, INVALID MANIFEST"
	} else {
		puts "Getting hash"
		set hash [lindex [split [exec $sha256sum $FAAS_CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp] ] 0]
	}
} else {
	set sha256sum sha256sum
	puts "Getting hash"
	set hash [lindex [split [exec $sha256sum $FAAS_CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp] ] 0]
}


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
if { [file exists $FAAS_CL_DIR/build/checkpoints/to_aws/${timestamp}.Developer_CL.tar] } {
        puts "Deleting old tar file with same name.";
        file delete -force $FAAS_CL_DIR/build/checkpoints/to_aws/${timestamp}.Developer_CL.tar
}

# Tar checkpoint to aws
cd $FAAS_CL_DIR/build/checkpoints
tar::create to_aws/${timestamp}.Developer_CL.tar [glob to_aws/${timestamp}*]

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Finished creating final tar file in to_aws directory.";

#if {[string compare $notify_via_sns "1"] == 0} {
#  puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Calling notification script to send e-mail to $env(EMAIL)";
#  exec $env(HDK_COMMON_DIR)/scripts/notify_via_sns.py
#}

