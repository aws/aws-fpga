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

#set awsip_file_locations 
#lappend awsip_location

set abfi_script_dir [file dirname [info script]]

set_param hd.supportClockNetCrossDiffReconfigurablePartitions 1




set_property STEPS.OPT_DESIGN.ARGS.DIRECTIVE Explore [get_runs [current_run -implementation]]
set_property STEPS.PLACE_DESIGN.ARGS.DIRECTIVE Explore [get_runs [current_run -implementation]]
set_property STEPS.PHYS_OPT_DESIGN.IS_ENABLED true [get_runs [current_run -implementation]]
#set_property STEPS.PHYS_OPT_DESIGN.ARGS.DIRECTIVE Explore [get_runs [current_run -implementation]]

	if {[get_property "STEPS.SYNTH_DESIGN.ARGS.MORE OPTIONS" [get_runs [current_run -synthesis]]] == ""} {
		set_property -name "STEPS.SYNTH_DESIGN.ARGS.MORE OPTIONS" -value "-mode out_of_context -max_uram_cascade_height 1" -objects [get_runs [current_run -synthesis]]		
		set SYNTH_URAM_CMD [get_property "STEPS.SYNTH_DESIGN.ARGS.MORE OPTIONS" [get_runs [current_run -synthesis]]]
		set SYNTH_URAM_ID [lsearch -all $SYNTH_URAM_CMD *max_uram_cascade_height*]
		set ::env(URAM_CASCADE) [lindex $SYNTH_URAM_CMD [expr ${SYNTH_URAM_ID}+1]]
		
	} else {
		set SYNTH_URAM_CMD [get_property "STEPS.SYNTH_DESIGN.ARGS.MORE OPTIONS" [get_runs [current_run -synthesis]]]
		set SYNTH_URAM_ID [lsearch -all $SYNTH_URAM_CMD *max_uram_cascade_height*]
		set ::env(URAM_CASCADE) [lindex $SYNTH_URAM_CMD [expr ${SYNTH_URAM_ID}+1]]		
	}		

	if {$::env(URAM_CASCADE) != 2} {
 	set_param synth.elaboration.rodinMoreOptions {rt::set_parameter disableOregPackingUram true}
  	set_param physynth.ultraRAMOptOutput false
	}


set_property -name "STEPS.SYNTH_DESIGN.ARGS.MORE OPTIONS" -value "-mode out_of_context -max_uram_cascade_height 1" -objects [get_runs [current_run -synthesis]]
# HANDLED IN launch_runs_pre.tcl
#set_property -name "STEPS.SYNTH_DESIGN.TCL.PRE" \
#	-value [file normalize [file join $abfi_script_dir subscripts synth_design_pre.tcl]] \
#	-objects [get_runs [current_run -synthesis]]
set_property -name "STEPS.SYNTH_DESIGN.TCL.POST" \
	-value [file normalize [file join $abfi_script_dir subscripts synth_design_post.tcl]] \
	-objects [get_runs [current_run -synthesis]]


set_property -name "STEPS.OPT_DESIGN.TCL.PRE" \
	-value [file normalize [file join $abfi_script_dir subscripts opt_design_pre.tcl]] \
	-objects [get_runs [current_run -implementation]]
set_property -name "STEPS.OPT_DESIGN.TCL.POST" \
	-value [file normalize [file join $abfi_script_dir subscripts opt_design_post.tcl]] \
	-objects [get_runs [current_run -implementation]]
#set_property -name "STEPS.PLACE_DESIGN.TCL.PRE" \
#	-value [file normalize [file join $abfi_script_dir subscripts place_design_pre.tcl]] \
#	-objects [get_runs [current_run -implementation]]
set_property -name "STEPS.PLACE_DESIGN.TCL.POST" \
	-value [file normalize [file join $abfi_script_dir subscripts place_design_post.tcl]] \
	-objects [get_runs [current_run -implementation]]

#set_property -name "STEPS.ROUTE_DESIGN.TCL.PRE" \
#	-value [file normalize [file join $abfi_script_dir subscripts route_design_pre.tcl]] \
#	-objects [get_runs [current_run -implementation]]
set_property -name "STEPS.ROUTE_DESIGN.TCL.POST" \
	-value [file normalize [file join $abfi_script_dir subscripts route_design_post.tcl]] \
	-objects [get_runs [current_run -implementation]]


set_property -name "STEPS.WRITE_BITSTREAM.TCL.PRE" \
	-value [file normalize [file join $abfi_script_dir subscripts write_bitstream_pre.tcl]] \
	-objects [get_runs [current_run -implementation]]




#set_property -name "STEPS.SYNTH_DESIGN.TCL.POST" -value "synth_design_post.tcl" -objects [get_runs [current_run -synthesis]]

#set_property -name "STEPS.OPT_DESIGN.TCL.PRE" -value "opt_design_pre.tcl" -objects [get_runs [current_run -implementation]]
#set_property -name "STEPS.OPT_DESIGN.TCL.POST" -value "opt_design_post.tcl" -objects [get_runs [current_run -implementation]]

#set_property -name "STEPS.PLACE_DESIGN.TCL.PRE" -value "place_design_pre.tcl" -objects [get_runs [current_run -implementation]]
#set_property -name "STEPS.PLACE_DESIGN.TCL.POST" -value "place_design_post.tcl" -objects [get_runs [current_run -implementation]]

#set_property -name "STEPS.ROUTE_DESIGN.TCL.PRE" -value "route_design_pre.tcl" -objects [get_runs [current_run -implementation]]
#set_property -name "STEPS.ROUTE_DESIGN.TCL.POST" -value "route_design_post.tcl" -objects [get_runs [current_run -implementation]]


##make_faas_subscript_variables

##determine if in make_faas proc or in Tcl Console
#if {[info exist _THISTOPSPACE] eq 0} {
#	#in proc
##	set _THISNAMESPACE $_nsvars::_VARNAMESPACE
##	set _THISTOPSPACE $_nsvars::_VARTOPSPACE
#	set _myspace "_nsvars"
#} else {
#	set _myspace [set [set _THISNAMESPACE]::[set _THISTOPSPACE]::_nsvars]
#}

## synthesis options
#set _mystep "STEPS.SYNTH_DESIGN.ARGS.MORE OPTIONS"
#set _myinstep "INSTEPS.SYNTH_DESIGN.ARGS.MORE OPTIONS"
#set [set _myspace]::[set _mystep] \
#	{-mode out_of_context}
#set [set _myspace]::[set _myinstep] "-synthesis"
##set [set _myspace]::STEPS.SYNTH_DESIGN.TCL.PRE \
##	[file join [set [set _myspace]::script_dir] subscripts  encrypt_cl_bd_call.tcl]

##FROM JAMES
#set [set _myspace]::STEPS.SYNTH_DESIGN.TCL.PRE \
#	[file normalize [file join [set [set _myspace]::script_dir] subscripts  synth_design_pre.tcl]]
#set [set _myspace]::INSTEPS.SYNTH_DESIGN.TCL.PRE "-synthesis"

#set [set _myspace]::STEPS.SYNTH_DESIGN.TCL.POST \
#	[file normalize [file join [set [set _myspace]::script_dir] subscripts  synth_design_post.tcl]]
#set [set _myspace]::INSTEPS.SYNTH_DESIGN.TCL.POST "-synthesis"


## implementation options
#set [set _myspace]::STEPS.OPT_DESIGN.TCL.PRE \
#	[file normalize [file join [set [set _myspace]::script_dir] subscripts  link_faas_dcps_call.tcl]]
#set [set _myspace]::INSTEPS.OPT_DESIGN.TCL.PRE "-implementation"

#set [set _myspace]::STEPS.OPT_DESIGN.TCL.POST \
#	[file normalize [file join [set [set _myspace]::script_dir] subscripts  post_opt_call.tcl]]
#set [set _myspace]::INSTEPS.OPT_DESIGN.TCL.POST "-implementation"

#set [set _myspace]::STEPS.PLACE_DESIGN.TCL.POST \
#	[file normalize [file join [set [set _myspace]::script_dir] subscripts  post_place_call.tcl]]
#set [set _myspace]::INSTEPS.PLACE_DESIGN.TCL.POST "-implementation"

#set [set _myspace]::STEPS.ROUTE_DESIGN.TCL.POST \
#	[file normalize [file join [set [set _myspace]::script_dir] subscripts  post_route_call.tcl]]
#set [set _myspace]::INSTEPS.ROUTE_DESIGN.TCL.POST "-implementation"

##find these with 
##set _list_steps [info vars ::aws::make_faas::_nsvars::STEPS*]
##foreach {_list_step} $_list_steps {
##	set _list_name [lindex [wsplit $_list_step "::"] end]
##	set _list_value [set $_list_step]
##	set _list_object [set [string map {"STEPS" "INSTEPS"} $_list_step]]
##	set_property -name $_list_name -value $_list_value -objects [get_runs [current_run $_list_object]]
###	set_property -name {STEPS.OPT_DESIGN.TCL.PRE} -value [file join $_nsvars::script_dir link_faas_dcps_call.tcl] -objects [get_runs [current_run -implementation]]
#}
