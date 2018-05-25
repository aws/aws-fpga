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

#post_route_call
set CURRENT_PATH [pwd]
lock_design -level routing

if {[info exist FAAS_CL_DIR] eq 0} {
	if {[info exist ::env(FAAS_CL_DIR)]} {
		set FAAS_CL_DIR $::env(FAAS_CL_DIR)
	} else {
		::tclapp::xilinx::faasutils::make_faas -force -bypass_drcs -partial
#		send_msg_id "route_design_post 0-1" ERROR "FAAS_CL_DIR environment varaiable not set, please run the proc 'aws::make_faas_setup' at the Vivado TCL command prompt"
	}
}

set SLACK [get_property SLACK [get_timing_paths]]
#Post-route phys_opt will not be run if slack is positive or greater than -200ps.
#TODO - how to automate this
if {$SLACK > -0.400 && $SLACK < 0} {
#   set_property STEPS.POST_ROUTE_PHYS_OPT_DESIGN.IS_ENABLED true [get_runs impl_1]
#	phys_opt_design -directive Explore
}

#move to bitgen stage, add in tarball
set timestamp $::env(timestamp)
file mkdir "$FAAS_CL_DIR/build/checkpoints/to_aws"

set scripts_update_version 2017.1
set current_vivado_version [version -short]

if { [string first $scripts_update_version $current_vivado_version] == 0 } {
  write_checkpoint -force $FAAS_CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp
  write_checkpoint -force $FAAS_CL_DIR/build/checkpoints/to_aws/SH_CL_routed.dcp
} else {
  write_checkpoint -force $FAAS_CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp -encrypt
  write_checkpoint -force $FAAS_CL_DIR/build/checkpoints/to_aws/SH_CL_routed.dcp -encrypt
}



# Generate debug probes file
write_debug_probes -force -no_partial_ltxfile -file $FAAS_CL_DIR/build/checkpoints/to_aws/${timestamp}.debug_probes.ltx


##################################################
# Create TAR
##################################################


package require tar  

if {[info exist FAAS_CL_DIR] eq 0} {
	if {[info exist ::env(FAAS_CL_DIR)]} {
		set FAAS_CL_DIR $::env(FAAS_CL_DIR)
	} else {
		send_msg_id "write_bitstream_pre 0-1" ERROR "FAAS_CL_DIR environment variable not set, please run the proc 'aws::make_ipi' at the Vivado TCL command prompt"
	}
}

if {[file exists $FAAS_CL_DIR/build/checkpoints/enviroment_current.tcl]} {
	source $FAAS_CL_DIR/build/checkpoints/enviroment_current.tcl
}

#need:
#$vendor_id
#$device_id
#$subsystem_id
#$subsystem_vendor_id
#$shell_version
#$hdk_version
#$clock_recipe_a
#$clock_recipe_b
#$clock_recipe_c
#$timestamp

puts "tarball_variables: [file normalize [file join [file dirname [info script]] tarball_variables.tcl]]"
source [file normalize [file join [file dirname [info script]] tarball_variables.tcl]]

set manifest_file [open "$FAAS_CL_DIR/build/checkpoints/to_aws/${timestamp}.manifest.txt" w]
#bydem
if {[info exist ::env(OS)] eq 0} {
	put "OS Environment variable not set, assuming Linux"
	set ::env(OS) "linux"
}
if {[string match "*windows*" [string tolower $::env(OS)]]} {
	if {[info exist SCRIPT_DIR] eq 0} {
		set SCRIPT_DIR [set tclapp::xilinx::faasutils::make_faas::_nsvars::script_dir]
	}
	set sha256sum [file normalize [file join $SCRIPT_DIR .. .. .. sha256sum.exe]]
	if {[file exists $sha256sum] eq 0} {
		puts "Please add sha256sum to your install app tree at $SCRIPT_DIR or hardcode in [file join [file dirname $argv0] $argv0]"
		set hash "MISSING HASH!  HASH NOT RUN, INVALID MANIFEST"
	} else {
		puts "Getting hash"
		if {[file exist $FAAS_CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp] } {
			set routed_DCP $FAAS_CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp
		} elseif {[file exist $FAAS_CL_DIR/build/checkpoints/to_aws/SH_CL_routed.dcp] } {
			set routed_DCP $FAAS_CL_DIR/build/checkpoints/to_aws/SH_CL_routed.dcp
		} else {
			send_msg_id "write_bitstream_pre 0-1" ERROR "Cannot find routed dcp to hash"
		}
		set hash [lindex [split [exec $sha256sum $routed_DCP] ] 0]
	}
} else {
	set sha256sum sha256sum
	puts "Getting hash"
	set hash [lindex [split [exec $sha256sum $FAAS_CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp] ] 0]
}


# Clock Group A
switch $clock_recipe_a {
    "0" {
	set clock_recipe_a_sw "A0"
    }
    "1" {
	set clock_recipe_a_sw "A1"
    }
    "2" {
	set clock_recipe_a_sw "A2"
    }
    default {
        puts "$clock_recipe_a is NOT a valid clock_recipe_a."
    }
}

# Clock Group B
switch $clock_recipe_b {
    "0" {
	set clock_recipe_b_sw "B0"
    }
    "1" {
	set clock_recipe_b_sw "B1"
    }
    "2" {
	set clock_recipe_b_sw "B2"

    }
    "3" {
	set clock_recipe_b_sw "B3"
    }
    "4" {
	set clock_recipe_b_sw "B4"
    }
    "5" {
	set clock_recipe_b_sw "B5"
    }
    default {
        puts "$clock_recipe_b is NOT a valid clock_recipe_b."
    }
}

# Clock Group C
switch $clock_recipe_c {
    "0" {
	set clock_recipe_c_sw "C0"
    }
    "1" {
	set clock_recipe_c_sw "C1"
    }
    "2" {
	set clock_recipe_c_sw "C2"
    }
    "3" {
	set clock_recipe_c_sw "C3"
    }
    default {
        puts "$clock_recipe_c is NOT a valid clock_recipe_c."
    }
}

set vivado_version [version -short]
set ver_2017_4 2017.4

if { [string first $ver_2017_4 $vivado_version] == 0 } {
puts $manifest_file "manifest_format_version=2\n"
#puts "in 2017.4"
} else {
puts $manifest_file "manifest_format_version=1\n"
#puts "in 2017.1"
}

puts $manifest_file "pci_vendor_id=$vendor_id\n"
puts $manifest_file "pci_device_id=$device_id\n"
puts $manifest_file "pci_subsystem_id=$subsystem_id\n"
puts $manifest_file "pci_subsystem_vendor_id=$subsystem_vendor_id\n"
puts $manifest_file "dcp_hash=$hash\n"
puts $manifest_file "shell_version=$shell_version\n"
puts $manifest_file "dcp_file_name=${timestamp}.SH_CL_routed.dcp\n"
puts $manifest_file "hdk_version=$hdk_version\n"
if { [string first $ver_2017_4 $vivado_version] == 0} {
puts $manifest_file "tool_version=v2017.4\n"
}
puts $manifest_file "date=$timestamp\n"
puts $manifest_file "clock_recipe_a=$clock_recipe_a_sw\n"
puts $manifest_file "clock_recipe_b=$clock_recipe_b_sw\n"
puts $manifest_file "clock_recipe_c=$clock_recipe_c_sw\n"

close $manifest_file

# Delete old tar file with same name
if { [file exists $FAAS_CL_DIR/build/checkpoints/to_aws/${timestamp}.Developer_CL.tar] } {
        puts "Deleting old tar file with same name.";
        file delete -force $FAAS_CL_DIR/build/checkpoints/to_aws/${timestamp}.Developer_CL.tar
}

# Tar checkpoint to aws
cd $FAAS_CL_DIR/build/checkpoints
tar::create to_aws/${timestamp}.Developer_CL.tar [glob to_aws/${timestamp}*]


cd ${CURRENT_PATH}

send_msg_id {make_faas 3-1870} WARNING "Bitstream Generation Not Supported for AWS flow, creating TAR file instead."
puts "\n********************************************************************************"
send_msg_id {make_faas 10-4} INFO "SUCCESS!  TAR file generated at $FAAS_CL_DIR/build/checkpoints/to_aws/${timestamp}.Developer_CL.tar"
puts "********************************************************************************\n"






