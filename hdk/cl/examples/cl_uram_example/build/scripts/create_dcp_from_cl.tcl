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

## Do not edit $TOP
set TOP top_sp

## Replace with the name of your module
set CL_MODULE cl_uram_example

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
set uram_option         [lindex $argv 11]
set notify_via_sns      [lindex $argv 12]

##################################################
## Flow control variables 
##################################################
set cl.synth   1
set implement  1

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
puts "URAM option:            $uram_option";
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

##################################################
### Output Directories used by step_user.tcl
##################################################
set implDir   $CL_DIR/build/checkpoints
set rptDir    $CL_DIR/build/reports
set cacheDir  $HDK_SHELL_DESIGN_DIR/cache/ddr4_phy

puts "All reports and intermediate results will be time stamped with $timestamp";

set_msg_config -id {Chipscope 16-3} -suppress
set_msg_config -string {AXI_QUAD_SPI} -suppress

# Suppress Warnings
# These are to avoid warning messages that may not be real issues. A developer
# may comment them out if they wish to see more information from warning
# messages.
set_msg_config -id {Common 17-55}        -suppress
set_msg_config -id {Vivado 12-4739}      -suppress
set_msg_config -id {Constraints 18-4866} -suppress
set_msg_config -id {IP_Flow 19-2162}     -suppress
set_msg_config -id {Route 35-328}        -suppress
set_msg_config -id {Vivado 12-1008}      -suppress
set_msg_config -id {Vivado 12-508}       -suppress
set_msg_config -id {filemgmt 56-12}      -suppress
set_msg_config -id {DRC CKLD-1}          -suppress
set_msg_config -id {DRC CKLD-2}          -suppress
set_msg_config -id {IP_Flow 19-2248}     -suppress
set_msg_config -id {Vivado 12-1580}      -suppress
set_msg_config -id {Constraints 18-550}  -suppress
set_msg_config -id {Synth 8-3295}        -suppress
set_msg_config -id {Synth 8-3321}        -suppress
set_msg_config -id {Synth 8-3331}        -suppress
set_msg_config -id {Synth 8-3332}        -suppress
set_msg_config -id {Synth 8-6014}        -suppress
set_msg_config -id {Timing 38-436}       -suppress
set_msg_config -id {DRC REQP-1853}       -suppress
set_msg_config -id {Synth 8-350}         -suppress
set_msg_config -id {Synth 8-3848}        -suppress
set_msg_config -id {Synth 8-3917}        -suppress

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

##################################################
### Strategy options 
##################################################
switch $strategy {
    "BASIC" {
        puts "BASIC strategy."
        source $HDK_SHELL_DIR/build/scripts/strategy_BASIC.tcl
    }
    "EXPLORE" {
        puts "EXPLORE strategy."
        source $HDK_SHELL_DIR/build/scripts/strategy_EXPLORE.tcl
    }
    "TIMING" {
        puts "TIMING strategy."
        source $HDK_SHELL_DIR/build/scripts/strategy_TIMING.tcl
    }
    "CONGESTION" {
        puts "CONGESTION strategy."
        source $HDK_SHELL_DIR/build/scripts/strategy_CONGESTION.tcl
    }
    "DEFAULT" {
        puts "DEFAULT strategy."
        source $HDK_SHELL_DIR/build/scripts/strategy_DEFAULT.tcl
    }
    default {
        puts "$strategy is NOT a valid strategy. Defaulting to strategy DEFAULT."
        source $HDK_SHELL_DIR/build/scripts/strategy_DEFAULT.tcl
    }
}

#Encrypt source code
source encrypt.tcl

#Set the Device Type
source $HDK_SHELL_DIR/build/scripts/device_type.tcl

#Procedure for running various implementation steps (impl_step)
source $HDK_SHELL_DIR/build/scripts/step_user.tcl -notrace

########################################
## Generate clocks based on Recipe 
########################################

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Calling aws_gen_clk_constraints.tcl to generate clock constraints from developer's specified recipe.";

source $HDK_SHELL_DIR/build/scripts/aws_gen_clk_constraints.tcl

##################################################
### CL XPR OOC Synthesis
##################################################
if {${cl.synth}} {
   source -notrace ./synth_${CL_MODULE}.tcl
}

##################################################
### Implementation
##################################################
if {$implement} {

   ########################
   # Link Design
   ########################
   if {$link} {
      ####Create in-memory prjoect and setup IP cache location
      create_project -part [DEVICE_TYPE] -in_memory
      set_property IP_REPO_PATHS $cacheDir [current_project]
      puts "\nAWS FPGA: ([clock format [clock seconds] -format %T]) - Combining Shell and CL design checkpoints";
      add_files $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
      add_files $CL_DIR/build/checkpoints/${timestamp}.CL.post_synth.dcp
      set_property SCOPED_TO_CELLS {CL} [get_files $CL_DIR/build/checkpoints/${timestamp}.CL.post_synth.dcp]

      #Read the constraints, note *DO NOT* read cl_clocks_aws (clocks originating from AWS shell)
      read_xdc [ list \
         $CL_DIR/build/constraints/cl_pnr_user.xdc
      ]
      set_property PROCESSING_ORDER late [get_files cl_pnr_user.xdc]

      puts "\nAWS FPGA: ([clock format [clock seconds] -format %T]) - Running link_design";
      link_design -top $TOP -part [DEVICE_TYPE] -reconfig_partitions {SH CL}

      puts "\nAWS FPGA: ([clock format [clock seconds] -format %T]) - PLATFORM.IMPL==[get_property PLATFORM.IMPL [current_design]]";
      ##################################################
      # Apply Clock Properties for Clock Table Recipes
      ##################################################
      puts "AWS FPGA: ([clock format [clock seconds] -format %T]) - Sourcing aws_clock_properties.tcl to apply properties to clocks. ";
      
      # Apply properties to clocks
      source $HDK_SHELL_DIR/build/scripts/aws_clock_properties.tcl

      # Write post-link checkpoint
      puts "\nAWS FPGA: ([clock format [clock seconds] -format %T]) - Writing post-link_design checkpoint ${timestamp}.post_link.dcp";
      write_checkpoint -force $CL_DIR/build/checkpoints/${timestamp}.post_link.dcp
   }

   ########################
   # CL Optimize
   ########################
   if {$opt} {
      puts "\nAWS FPGA: ([clock format [clock seconds] -format %T]) - Running optimization";
      impl_step opt_design $TOP $opt_options $opt_directive $opt_preHookTcl $opt_postHookTcl
      if {$psip} {
         impl_step opt_design $TOP "-merge_equivalent_drivers -sweep"
      }
   }

   ########################
   # CL Place
   ########################
   if {$place} {
      puts "\nAWS FPGA: ([clock format [clock seconds] -format %T]) - Running placement";
      if {$psip} {
         append place_options " -fanout_opt"
      }
      impl_step place_design $TOP $place_options $place_directive $place_preHookTcl $place_postHookTcl
   }

   ##############################
   # CL Post-Place Optimization
   ##############################
   if {$phys_opt} {
      puts "\nAWS FPGA: ([clock format [clock seconds] -format %T]) - Running post-place optimization";
      impl_step phys_opt_design $TOP $phys_options $phys_directive $phys_preHookTcl $phys_postHookTcl
   }

   ########################
   # CL Route
   ########################
   if {$route} {
      puts "\nAWS FPGA: ([clock format [clock seconds] -format %T]) - Routing design";
      impl_step route_design $TOP $route_options $route_directive $route_preHookTcl $route_postHookTcl
   }

   ##############################
   # CL Post-Route Optimization
   ##############################
   set SLACK [get_property SLACK [get_timing_paths]]
   #Post-route phys_opt will not be run if slack is positive or greater than -200ps.
   if {$route_phys_opt && $SLACK > -0.400 && $SLACK < 0} {
      puts "\nAWS FPGA: ([clock format [clock seconds] -format %T]) - Running post-route optimization";
      impl_step route_phys_opt_design $TOP $post_phys_options $post_phys_directive $post_phys_preHookTcl $post_phys_postHookTcl
   }

   ##############################
   # Final Implmentation Steps
   ##############################
   # Report final timing
   report_timing_summary -file $CL_DIR/build/reports/${timestamp}.SH_CL_final_timing_summary.rpt

   # This is what will deliver to AWS
   puts "AWS FPGA: ([clock format [clock seconds] -format %T]) - Writing final DCP to to_aws directory.";

   write_checkpoint -force $CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp

   # Generate debug probes file
   write_debug_probes -force -no_partial_ltxfile -file $CL_DIR/build/checkpoints/${timestamp}.debug_probes.ltx

   close_project
}

# ################################################
# Create Manifest and Tarball for delivery
# ################################################

# Create a zipped tar file, that would be used for createFpgaImage EC2 API

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) - Compress files for sending to AWS. "

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

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) - Finished creating final tar file in to_aws directory.";

if {[string compare $notify_via_sns "1"] == 0} {
  puts "AWS FPGA: ([clock format [clock seconds] -format %T]) - Calling notification script to send e-mail to $env(EMAIL)";
  exec $env(HDK_COMMON_DIR)/scripts/notify_via_sns.py
}

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) - Build complete.";


