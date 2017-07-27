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


dputs $debugMode "\n\n\n"
dputs $debugMode "********************************************************************************"
dputs $debugMode "********************************************************************************"
dputs $debugMode "Runing create_proj_from_magic.tcl\n starting with variables:"
foreach {_pass_var_to_script} $_pass_vars_to_script {
	dputs $debugMode "\t$_pass_var_to_script = [set [set _pass_var_to_script] ]"
}
if {[info exist _post_synth_dcp] eq 0} {
	send_msg_id "[file tail [info script]] 0-187" ERROR "Variable for post synthesis DCP does not exist.  Please ensure write_checkpoint_call has occurred post_synthesis (hook script).  Try:\n\tset_property -name {STEPS.SYNTH_DESIGN.TCL.POST} -value \[file join \$aws::make_faas::_nsvars::script_dir write_checkpoint_call.tcl\] -objects \[get_runs \$_current_synth_run\]"
}
if {[file exist $_post_synth_dcp] eq 0} {
	send_msg_id "[file tail [info script]] 1-187" ERROR "File $_post_synth_dcp for post synthesis DCP does not exist.  Please ensure write_checkpoint_call has occurred post_synthesis (hook script).  Try:\n\tset_property -name {STEPS.SYNTH_DESIGN.TCL.POST} -value \[file join \$aws::make_faas::_nsvars::script_dir write_checkpoint_call.tcl\] -objects \[get_runs \$_current_synth_run\]"
}

if {[string tolower [version -short]] eq "2017.1"} {	
	set HDK_VERSION_DIR "shell_v04151701"
} else {
	set HDK_VERSION_DIR "shell_v071417d3"
}
dputs $debugMode "Using Shell: $HDK_VERSION_DIR"


# Modified from hdk_setup.sh
set ::env(FAAS_CL_DIR) $FAAS_CL_DIR
if { [info exists ::env(HDK_DIR)] } {
        set HDK_DIR $::env(HDK_DIR)
        puts "Using hdk directory $HDK_DIR"
} else {
	set HDK_DIR [file join $_nsvars::script_dir DONOTINCLUDE_INAPP hdk_lite]
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

set strategy "EXPLORE"

set hdk_version [findLineInFile [file join $HDK_DIR hdk_version.txt] "HDK_VERSION"]
	set hdk_version [string map {"=" " "} $hdk_version]
	set hdk_version [regexp -all -inline {\S+} $hdk_version]
	set hdk_version [lindex $hdk_version 1]
	dputs $debugMode "  hdk_version is $hdk_version"
	
set shell_version [findLineInFile [file join $HDK_SHELL_DIR shell_version.txt] "SHELL_VERSION"]
	set shell_version [string map {"=" " "} $shell_version]
	set shell_version [regexp -all -inline {\S+} $shell_version]
	set shell_version [lindex $shell_version 1]
	dputs $debugMode "  shell_version is $shell_version"

# Get id0, id1, clock recipies from IP

if {$_cl_ips eq ""} {
# add rtl checks here (findLineInFile)
#id0_version=$(grep 'CL_SH_ID0' $FAAS_CL_DIR/design/cl_id_defines.vh | grep 'define' | sed 's/_//g' | awk -F "h" '{print $2}')
#device_id="0x${id0_version:0:4}";
#vendor_id="0x${id0_version:4:4}";
set id0_version [findLineInFile [file join $FAAS_CL_DIR design cl_id_defines.vh] "SL_SH_ID0"]
	set id0_version [string map {"_" ""} $id0_version]
	set id0_version [regexp -all -inline {\S+} $id0_version]
	set id0_version [lindex $id0_version 1]
	set device_id [join [lrange [split $id0_version ""] 0 3]]
	set vendor_id [join [lrange [split $id0_version ""] 4 7]]

#id1_version=$(grep 'CL_SH_ID1' $FAAS_CL_DIR/design/cl_id_defines.vh | grep 'define' | sed 's/_//g' | awk -F "h" '{print $2}')
#subsystem_id="0x${id1_version:0:4}";
#subsystem_vendor_id="0x${id1_version:4:4}";
set id1_version [findLineInFile [file join $FAAS_CL_DIR design cl_id_defines.vh] "SL_SH_ID1"]
	set id1_version [string map {"_" ""} $id1_version]
	set id1_version [regexp -all -inline {\S+} $id1_version]
	set id1_version [lindex $id1_version 1]
	set subsystem_id [join [lrange [split $id1_version ""] 0 3]]
	set subsystem_vendor_id [join [lrange [split $id1_version ""] 4 7]]

} else {
	set device_id [get_property CONFIG.DEVICE_ID $_cl_ips]
	set vendor_id [get_property CONFIG.VENDOR_ID $_cl_ips]
	set subsystem_id [get_property CONFIG.SUBSYSTEM_ID $_cl_ips]
	set subsystem_vendor_id [get_property CONFIG.SUBSYSTEM_VENDOR_ID $_cl_ips]
	set clock_recipe_a [get_property CONFIG.CLOCK_A_RECIPE $_cl_ips]
	set clock_recipe_b [get_property CONFIG.CLOCK_B_RECIPE $_cl_ips]
	set clock_recipe_c [get_property CONFIG.CLOCK_C_RECIPE $_cl_ips]
}



set run_aws_emulation 0
set notify_via_sns 0	




#set top top_sp
#set TOP cl_top


set logname "\{[file join $FAAS_CL_DIR SH_CL_$timestamp.log]\}"
set vivado_script "\{[file join $SCRIPT_DIR create_dcp_from_proj.tcl]\}"
set vivcmd "vivado -mode batch -nojournal -log ${logname} -source ${vivado_script} -tclargs $timestamp $strategy $hdk_version $shell_version $device_id $vendor_id $subsystem_id $subsystem_vendor_id $clock_recipe_a $clock_recipe_b $clock_recipe_c $run_aws_emulation $notify_via_sns"

puts "Running the following command from the TCL tab in Vivado\n\t$vivcmd"
puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Calling Vivado with ${vivado_script}";
exec {*}${vivcmd}
puts "Finished running the command from the TCL tab in Vivado\n\t$vivcmd"
puts "\n\n"
puts "Success! Design Complete: Please see log at ${logname}"
puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Completed Vivado with ${vivado_script}";




















