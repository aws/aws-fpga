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

#link_faas_dcps_call


puts "CURRENT_PART [get_parts -of_objects [current_project]]"

set _this_flow_option 2
if {$_this_flow_option eq 1} {
	#step 1 - non-project flow
	send_msg_id {make_faas 0-1870} ERROR "Inline implementation not yet supported for FaaS flow.  Please use aws::make_faas_all or aws::make_ipi_faas_all"

} elseif {$_this_flow_option eq 2} {
	#step2 - hook script flow
	if {[info exist FAAS_CL_DIR] eq 0} {
		if {[info exist ::env(FAAS_CL_DIR)]} {
			set FAAS_CL_DIR $::env(FAAS_CL_DIR)
		} else {
			::tclapp::xilinx::faasutils::make_faas -force -bypass_drcs -partial
#			send_msg_id "opt_design_pre 0-1" ERROR "FAAS_CL_DIR environment varaiable not set, please run the proc 'aws::make_faas_setup' at the Vivado TCL command prompt"
		}
	}
	set top top_sp
	set timestamp $::env(timestamp)

	#finish the linked design, write to dcp
	file mkdir [file join $FAAS_CL_DIR build checkpoints]
	write_checkpoint -force $FAAS_CL_DIR/build/checkpoints/CL.post_synth_inline.dcp

	#close the current design, read in both checkpoints, link & write, then continue with normal (subverted) flow
	report_property [current_design]

	add_files $::env(HDK_SHELL_DIR)/build/checkpoints/from_aws/SH_CL_BB_routed.dcp

	
	set AWS_RTL_XDC_EXISTS [get_files */cl_synth_aws.xdc -quiet]

	set BD_PATH_EXISTS [get_files */cl.bd -quiet]

	if {$BD_PATH_EXISTS != ""} {
		set BD_CHECK_MODE [get_property synth_checkpoint_mode [get_files */cl.bd]]
		if {$BD_CHECK_MODE == "None"} {
		set BD_MODE "None"
		} else {
		set BD_MODE ""
		}
	} else {
		set BD_MODE ""	
	}
	
	#RTL Flow or IPI Flow
	if {$AWS_RTL_XDC_EXISTS != "" || $BD_MODE  == "None" } {
	add_files $FAAS_CL_DIR/build/checkpoints/CL.post_synth_inline.dcp
	set_property SCOPED_TO_CELLS {CL} [get_files $FAAS_CL_DIR/build/checkpoints/CL.post_synth_inline.dcp]
	} else {
	add_files $FAAS_CL_DIR/build/checkpoints/CL.post_synth.dcp
	set_property SCOPED_TO_CELLS {CL} [get_files $FAAS_CL_DIR/build/checkpoints/CL.post_synth.dcp]
	}
	
	read_xdc $::env(HDK_SHELL_DIR)/build/constraints/cl_ddr.xdc
	
	set PNR_USR_LOC $::env(PNR_USER)
	read_xdc ${PNR_USR_LOC}
	set_property PROCESSING_ORDER LATE [get_files $PNR_USR_LOC]
	set_property USED_IN {implementation} [get_files $PNR_USR_LOC]	

	link_design -top $top -part [get_parts -of_objects [current_project]] -reconfig_partitions {SH CL}
	source ${FAAS_CL_DIR}/build/constraints/aws_gen_clk_constraints.tcl

	switch  $::env(URAM_CASCADE) {
	    "2" {
	        set uramHeight 2
	    }
	    "3" {
	        set uramHeight 3
	    }
	    "4" {
	        set uramHeight 4
	    }
	    default {
	        set uramHeight 4
	    }
	}

	source $::env(HDK_SHELL_DIR)/build/scripts/check_uram.tcl
	
	write_checkpoint -force $FAAS_CL_DIR/build/checkpoints/${timestamp}.SH_CL.post_link_design.dcp



} elseif {$_this_flow_option eq 3} {
	#step3 - project flow, launch new project
	puts "NOT YET IMPLEMENTED!"
	close design
}


