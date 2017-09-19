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


set script_dir $::env(FAAS_SCRIPT_DIR)
set sdp_script_dir [file dirname [info script]]



if {[info exist FAAS_CL_DIR] eq 0} {
	if {[info exist ::env(FAAS_CL_DIR)]} {
		set FAAS_CL_DIR $::env(FAAS_CL_DIR)
	} else {
		::tclapp::xilinx::faasutils::make_faas -force -bypass_drcs -partial
#		send_msg_id "synth_design_post 0-1" ERROR "FAAS_CL_DIR environment varaiable not set, please run the proc 'aws::make_faas_setup' at the Vivado TCL command prompt"
	}
}


set synth_directory [pwd]
set _post_synth_dcp [file normalize [file join $FAAS_CL_DIR build checkpoints CL.post_synth.dcp]]
set const_dir [file normalize [file join $FAAS_CL_DIR build constraints]]
file mkdir $const_dir
#file copy -force [file normalize [file join $sdp_script_dir xsdbm_timing_exception.xdc ]] [file normalize [file join $const_dir xsdbm_timing_exception.xdc]]
#file copy -force [file normalize [file join $sdp_script_dir cl_debug_bridge.xdc ]] [file normalize [file join $const_dir cl_debug_bridge.xdc]]
file copy -force [file normalize [file join $sdp_script_dir cl_debug_bridge_hlx.xdc ]] [file normalize [file join $const_dir cl_debug_bridge_hlx.xdc]]


set BD_PATH_EXISTS [get_files */cl.bd -quiet]

	if {$BD_PATH_EXISTS != ""} {
		set BD_PATH [get_files */cl.bd]
	} else {
		set BD_PATH "NONE"
	}

set AWS_RTL_XDC_EXISTS [get_files */cl_synth_aws.xdc -quiet]
	if {$AWS_RTL_XDC_EXISTS != ""} {
		set AWS_XDC_PATH [get_files */cl_synth_aws.xdc]
	} else {
		set AWS_XDC_PATH "NONE"
	}

set vivcmd "vivado -mode batch -source [file normalize [file join $sdp_script_dir make_post_synth_dcp.tcl ]] -tclargs -TOP [get_property top [current_fileset]] -IP_REPO [get_property IP_OUTPUT_REPO [get_project [get_projects]]] -SYNTH_DIR $synth_directory -BD_PATH ${BD_PATH} -XDC [get_files */cl_clocks_aws.xdc] -USR_XDC [get_files */cl_synth_user.xdc] -AWS_XDC ${AWS_XDC_PATH} -LINK_DCP_PATH $_post_synth_dcp"

puts "Running the following command from the TCL tab in Vivado\n\t$vivcmd"
exec {*}${vivcmd}
puts "Finished running the command from the TCL tab in Vivado\n\t$vivcmd"
puts "\n\n"


