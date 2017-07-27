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


set HDK_VERSION_DIR "shell_v062517b4"
set debugMode 1

set timestamp $::env(timestamp)
puts "timestamp:$timestamp"

if { [info exists ::env(HDK_DIR)] } {
        set HDK_DIR $::env(HDK_DIR)
        puts "Using hdk directory $HDK_DIR"
} else {
#!HACK
	set HDK_DIR [file normalize [file join [file dirname [info script]] .. .. .. .. .. .. .. DONOTINCLUDE_INAPP hdk_lite]]
#	set HDK_DIR [file normalize [file join $::tclapps::xilinx::faasutils::_nsvars::script_dir DONOTINCLUDE_INAPP hdk_lite]
	set ::env(HDK_DIR) $HDK_DIR
	puts "Using test shell, please run hdk_setup.sh for the real design"
}
if { [info exists ::env(HDK_COMMON_DIR)] } {
        set HDK_COMMON_DIR $::env(HDK_COMMON_DIR)
        puts "Using Shell common directory $HDK_COMMON_DIR"
} else {
	set HDK_COMMON_DIR [file join $HDK_DIR common]
	set ::env(HDK_COMMON_DIR) $HDK_COMMON_DIR
}
if { [info exists ::env(HDK_SHELL_DIR)] } {
        set HDK_SHELL_DIR $::env(HDK_SHELL_DIR)
} else {
	set HDK_SHELL_DIR [file join $HDK_COMMON_DIR $HDK_VERSION_DIR]
	set ::env(HDK_SHELL_DIR) $HDK_SHELL_DIR
}
if { [info exists ::env(HDK_SHELL_DESIGN_DIR)] } {
        set HDK_SHELL_DESIGN_DIR $::env(HDK_SHELL_DESIGN_DIR)
} else {
	set HDK_SHELL_DESIGN_DIR [file join $HDK_SHELL_DIR design]
	set ::env(HDK_SHELL_DESIGN_DIR) $HDK_SHELL_DESIGN_DIR
}


set hdk_version [tclapp::xilinx::faasutils::make_faas::findLineInFile  [file join $HDK_DIR hdk_version.txt] "HDK_VERSION"]
	set hdk_version [string map {"=" " "} $hdk_version]
	set hdk_version [regexp -all -inline {\S+} $hdk_version]
	set hdk_version [lindex $hdk_version 1]
	
set shell_version [tclapp::xilinx::faasutils::make_faas::findLineInFile  [file join $HDK_SHELL_DIR shell_version.txt] "SHELL_VERSION"]
	set shell_version [string map {"=" " "} $shell_version]
	set shell_version [regexp -all -inline {\S+} $shell_version]
	set shell_version [lindex $shell_version 1]
# mismatch check vs. ::env(FAAS_SHELL_VERSION)?
if {[info exist ::env(FAAS_SHELL_VERSION)]} {
	if {[string match $::env(FAAS_SHELL_VERSION) $shell_version] eq 0} {
		send_msg_id "write_bitstream_pre 1-1" "CRITICAL WARNING" "Shell version read from [file join $HDK_SHELL_DIR shell_version.txt] ($shell_version) does not match the shell version in IP Integrator ($::env(FAAS_SHELL_VERSION)).  Possible file mismatch."
	}
}

if {[info exist ::env(CLOCK_A_RECIPE)]} {
	set clock_recipe_a $::env(CLOCK_A_RECIPE)
} else {
	send_msg_id "synth_design_post 0-2" ERROR "CLOCK_A_RECIPE not set.  Please set CLOCK_A_RECIPE environment variable to a value between 0:2.\n  example:\n\t set ::env(CLOCK_A_RECIPE) 0"
}
if {[info exist ::env(CLOCK_B_RECIPE)]} {
	set clock_recipe_b $::env(CLOCK_B_RECIPE)
} else {
	send_msg_id "synth_design_post 0-2" ERROR "CLOCK_B_RECIPE not set.  Please set CLOCK_B_RECIPE environment variable to a value between 0:5.\n  example:\n\t set ::env(CLOCK_B_RECIPE) 0"
}
if {[info exist ::env(CLOCK_C_RECIPE)]} {
	set clock_recipe_c $::env(CLOCK_C_RECIPE)
} else {
	send_msg_id "synth_design_post 0-2" ERROR "CLOCK_C_RECIPE not set.  Please set CLOCK_C_RECIPE environment variable to a value between 0:3.\n  example:\n\t set ::env(CLOCK_C_RECIPE) 0"
}



if {[info exist ::env(device_id)]} {
	set device_id $::env(device_id)
} else {
	send_msg_id "synth_design_post 0-2" ERROR "device_id not set.  Please set device_id environment variable to a valid value.\n  example:\n\t set ::env(device_id) 0xF000"
}
if {[info exist ::env(vendor_id)]} {
	set vendor_id $::env(vendor_id)
} else {
	send_msg_id "synth_design_post 0-2" ERROR "vendor_id not set.  Please set vendor_id environment variable to a valid value.\n  example:\n\t set ::env(vendor_id) 0x0001"
}
if {[info exist ::env(subsystem_id)]} {
	set subsystem_id $::env(subsystem_id)
} else {
	send_msg_id "synth_design_post 0-2" ERROR "subsystem_id not set.  Please set subsystem_id environment variable to a valid value.\n  example:\n\t set ::env(subsystem_id) 0x1D51"
}
if {[info exist ::env(subsystem_vendor_id)]} {
	set subsystem_vendor_id $::env(subsystem_vendor_id)
} else {
	send_msg_id "synth_design_post 0-2" ERROR "subsystem_vendor_id not set.  Please set subsystem_vendor_id environment variable to a valid value.\n  example:\n\t set ::env(subsystem_vendor_id) 0xFEDD"
}


#set clock_recipe_a $::env(CLOCK_A_RECIPE)
#set clock_recipe_b $::env(CLOCK_B_RECIPE)
#set clock_recipe_c $::env(CLOCK_C_RECIPE)

#set device_id $::env(device_id)
#set vendor_id $::env(vendor_id)
#set subsystem_id $::env(subsystem_id)
#set subsystem_vendor_id $::env(subsystem_vendor_id)

set vendor_id
set device_id
set subsystem_id
set subsystem_vendor_id
set shell_version
set hdk_version
set clock_recipe_a
set clock_recipe_b
set clock_recipe_c
set timestamp


