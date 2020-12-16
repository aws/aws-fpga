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




set _aws_make_version 0.990


#post inline - only need to install one custom button
#aws::make_ipi - calls tclapp::xilinx::faasutils::make_ipi_faas_setup
#aws::make_ipi_faas - calls tclapp::xilinx::faasutils::make_ipi_faas_setup
#aws::make_ipi_all - calls ...make_ipi_faas_setup, then "launch_runs impl_1 -to_step write_bitstream"
#aws::make_rtl - calls tclapp::xilinx::faasutils::make_rtl_faas_setup

#NYI ---vvv
#aws::make_rtl_faas - calls tclapp::xilinx::faasutils::make_rtl_faas_setup
#aws::make_rtl_all - calls ...make_rtl_faas_setup, then "launch_runs impl_1 -to_step write_bitstream"

package require Vivado 1.2015.1


set _THISNAMESPACE "aws"
set _THISTOPSPACE  "make_faas"

if {[info exists ::tclapp::xilinx::faasutils::make_faas::public::bd_faas_root] eq 0} {
	send_msg_id "aws::make_faas 0-187" ERROR "::tclapp::xilinx::faasutils::make_faas not installed, please install this TCL application.  Add command here :)"
}

################################################################################
# hlx::Procs
################################################################################
namespace eval ${_THISNAMESPACE} { 
	namespace eval ${_THISTOPSPACE} {
		if {[info exist [set _THISNAMESPACE]::[set _THISTOPSPACE]::public::keepvars] eq 0} {
			namespace eval public {
				# public are locations / variables that exist from the perspective of the FaaS solution provider
				set bd_faas_root [file normalize [file join [file dirname [info script]] .. .. ..]]
				set bd_faas_initscript [file join $bd_faas_root build scripts aws_bd_faas_initscript.tcl]
				set bd_faas_examples_directory [file join $bd_faas_root hlx_examples]
				set bd_faas_design_directory [file join $bd_faas_root design]
				set keepvars 1
			}
		}
		if {[info exist [set _THISNAMESPACE]::[set _THISTOPSPACE]::user::keepvars] eq 0} {
			namespace eval user {
				#user are locations / variables that exist for the user output
				set examples_directory ""
					set keepvars 1
			}
		}
		namespace eval _nsvars {
			# _nsvars are specific to this namespace (e.g. variables local to this _THISNAMESPACE::_THISTOPSPACE)
			set script_dir [file dirname [info script]]
			# call as $_nsvars::script_dir in other procs :)
			set script_loc [file tail [info script]]
			set version $_make_faas_version
			set _VARNAMESPACE $_THISNAMESPACE
			set _VARTOPSPACE $_THISTOPSPACE
			# call as $_nsvars::_THISTOPSPACE
		}
	}
	namespace export [set _THISTOPSPACE] 
}



#proc [set _THISNAMESPACE]::make_faas {{args ""}} {
#	# Summary: 
#	# Argument Usage:
#	#[-examples <name>] (optional) creates an example project.  Use -examples list to list all available examples
#	#[-inline_examples <name>] (optional) Same as -examples, but works in the current project.
#	#[-save_examples <name>] (optional) Saves your current IP Integrator diagram to an example project that can be resourced.  Project is saved in the [PWD] directory structure.
#	#[-output_directory] (optional) output directory (default: use PWD)

#	# Return Value: 0

#	# Categories: HLx, IP Integrator, Vivado, Amazon

#	set _THISNAMESPACE $make_faas::_nsvars::_VARNAMESPACE
#	set _THISTOPSPACE  $make_faas::_nsvars::_VARTOPSPACE

#	return [aws::make_ipi {*}$args]
#}
#eval [list namespace eval [set _THISNAMESPACE]::[set _THISTOPSPACE] { } ]


proc [set _THISNAMESPACE]::update_public_faas_variables_to_parent_app {{args ""}} {
  # Summary : Run through synthesis for an IP Integrator GUI flow for FaaS
  # Argument Usage:
  # Return Value:
  # Categories:
	
	set _local_vars [info vars ::aws::make_faas::public::*]
	set _local_space "public"
	foreach {_local_var} $_local_vars {
		set _localized [lindex [split $_local_var :] end]
		set ::tclapp::xilinx::faasutils::make_faas::[set _local_space]::[set _localized] [set [set _local_var]]
	}
}

################################################################################
# Alternative Tops
################################################################################
proc [set _THISNAMESPACE]::make_ipi {{args ""}} {
  # Summary : Run through synthesis for an IP Integrator GUI flow for FaaS
  # Argument Usage:
  # Return Value:
  # Categories:
	set ::aws::make_faas::public::bd_faas_examples_directory [file normalize [file join $::aws::make_faas::public::bd_faas_root hlx_examples build IPI ]]
  
	update_public_faas_variables_to_parent_app
	::tclapp::xilinx::faasutils::make_faas -force -partial {*}$args
	if {[info exist ::env(FAAS_CL_DIR)]} {
		if {[file exist $::env(FAAS_CL_DIR)/build/constraints/cl_clocks_aws.xdc] eq 0} {
			file mkdir $::env(FAAS_CL_DIR)/build/constraints
			file copy -force $::env(HDK_SHELL_DIR)/build/constraints/cl_clocks_aws.xdc $::env(FAAS_CL_DIR)/build/constraints/cl_clocks_aws.xdc

	add_files -fileset constrs_1 -norecurse $::env(FAAS_CL_DIR)/build/constraints/cl_clocks_aws.xdc -force

	set_property PROCESSING_ORDER EARLY [get_files */cl_clocks_aws.xdc]
	set_property USED_IN {synthesis synthesis out_of_context implementation} [get_files */cl_clocks_aws.xdc]
	
		}
		
	}

        if {[current_project -quiet] ne ""} {
		if {[get_files */cl_pnr_user.xdc -quiet] == ""} {
			import_files -fileset constrs_1 $::aws::make_faas::_nsvars::script_dir/subscripts/cl_synth_user.xdc
			import_files -fileset constrs_1 $::aws::make_faas::_nsvars::script_dir/subscripts/cl_pnr_user.xdc
			set_property PROCESSING_ORDER LATE [get_files */cl_pnr_user.xdc]
			set_property USED_IN {implementation} [get_files */cl_pnr_user.xdc]
			
			set_property is_enabled false [get_files */cl_pnr_user.xdc]
			set ::env(PNR_USER) [get_files */cl_pnr_user.xdc]			
		} else {
		set ::env(PNR_USER) [get_files */cl_pnr_user.xdc]
		}			
			
		
		if {[get_files */tb.sv -quiet] == ""} {
add_files -fileset sim_1 [ list \
 $::env(HDK_SHELL_DESIGN_DIR)/ip/axi_clock_converter_0/axi_clock_converter_0.xci\
 $::env(HDK_SHELL_DESIGN_DIR)/ip/axi_register_slice/axi_register_slice.xci\
 $::env(HDK_SHELL_DESIGN_DIR)/ip/ddr4_core/ddr4_core.xci
]
			
			source $::aws::make_faas::_nsvars::script_dir/add_simulation.tcl
			
set_property -name {xsim.compile.tcl.pre} -value $::aws::make_faas::_nsvars::script_dir/../../verif/scripts/dpi_xsim.tcl -objects [get_filesets sim_1]
set_property -name {xsim.elaborate.xelab.more_options} -value {-sv_lib dpi} -objects [get_filesets sim_1]

set_property -name {questa.compile.tcl.pre} -value $::aws::make_faas::_nsvars::script_dir/../../verif/scripts/dpi.tcl -objects [get_filesets sim_1]
set_property -name {questa.compile.vlog.more_options} -value {-timescale 1ps/1ps +define+QUESTA_SIM} -objects [get_filesets sim_1]
set_property -name {questa.simulate.vsim.more_options} -value {-sv_lib libdpi} -objects [get_filesets sim_1]


set_property -name {ies.compile.tcl.pre} -value $::aws::make_faas::_nsvars::script_dir/../../verif/scripts/dpi.tcl -objects [get_filesets sim_1]
set_property -name {ies.compile.ncvlog.more_options} -value {+define+SV_TEST +define+SCOPE +define+IES_SIM} -objects [get_filesets sim_1]
set_property -name {ies.elaborate.ncelab.more_options} -value {+libext+.v+.sv -disable_sem2009 -timescale 1ps/1ps} -objects [get_filesets sim_1]
set_property -name {ies.simulate.ncsim.more_options} -value {-sv_lib libdpi} -objects [get_filesets sim_1]
        

set_property -name {vcs.compile.tcl.pre} -value $::aws::make_faas::_nsvars::script_dir/../../verif/scripts/dpi.tcl -objects [get_filesets sim_1]
set_property -name {vcs.compile.vlogan.more_options} -value {-ntb_opts tb_timescale=1ps/1ps -timescale=1ps/1ps -sverilog +systemverilogext+.sv +libext+.sv +libext+.v -full64 -lca -v2005 +v2k +define+VCS_SIM} -objects [get_filesets sim_1]
set_property -name {vcs.simulate.vcs.more_options} -value {-sv_lib libdpi} -objects [get_filesets sim_1]

			}		
	}
	
	return

}
#proc [set _THISNAMESPACE]::make_ipi_all {{args ""}} {
#  # Summary : Run through implementation for an IP Integrator GUI flow for FaaS
#  # Argument Usage:
#  # Return Value:
#  # Categories:

#	aws::make_ipi {*}$args

#	return [launch_runs impl_1 -to_step write_bitstream]
#}
#proc [set _THISNAMESPACE]::make_ipi_faas {{args ""}} {
#  # Summary : Run through synthesis for an IP Integrator GUI flow for FaaS
#  # Argument Usage:
#  # Return Value:
#  # Categories:

#	return [aws::make_ipi {*}$args]

#}
proc [set _THISNAMESPACE]::make_rtl {{args ""}} {
  # Summary : Run through synthesis for an IP Integrator GUI flow for FaaS
  # Argument Usage:
  # Return Value:
  # Categories:
#	return [make_faas -bypass_drcs -partial {*}$args]
	set ::aws::make_faas::public::bd_faas_examples_directory [file normalize [file join $::aws::make_faas::public::bd_faas_root hlx_examples build RTL ]]
	
	update_public_faas_variables_to_parent_app
	::tclapp::xilinx::faasutils::make_faas -force -bypass_drcs -partial {*}$args

	# Suppress Warnings - for RTL flow to match AWS env, future enable or disable in flow instead of hardcode
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
	
	if {[info exist ::env(FAAS_CL_DIR)]} {
		if {[file exist $::env(FAAS_CL_DIR)/build/constraints/cl_clocks_aws.xdc] eq 0} {
			file mkdir $::env(FAAS_CL_DIR)/build/constraints
			file copy -force $::env(HDK_SHELL_DIR)/build/constraints/cl_clocks_aws.xdc $::env(FAAS_CL_DIR)/build/constraints/cl_clocks_aws.xdc

	add_files -fileset constrs_1 -norecurse $::env(FAAS_CL_DIR)/build/constraints/cl_clocks_aws.xdc -force

	set_property PROCESSING_ORDER EARLY [get_files */cl_clocks_aws.xdc]
	set_property USED_IN {synthesis out_of_context implementation} [get_files */cl_clocks_aws.xdc]
	
		}
		
	}

        if {[current_project -quiet] ne ""} { 	       
		if {[get_files */cl_pnr_user.xdc -quiet] == ""} {
			#Initial adding of xdc files, simulation env and hdk ip and rtl
			import_files -fileset constrs_1 $::aws::make_faas::_nsvars::script_dir/subscripts/cl_synth_user.xdc
			import_files -fileset constrs_1 $::aws::make_faas::_nsvars::script_dir/subscripts/cl_pnr_user.xdc
			add_files -fileset constrs_1 -norecurse $::env(HDK_SHELL_DIR)/build/constraints/cl_synth_aws.xdc			
			
			set_property PROCESSING_ORDER LATE [get_files */cl_pnr_user.xdc]
			set_property USED_IN {implementation} [get_files */cl_pnr_user.xdc]
			
			set_property is_enabled false [get_files */cl_pnr_user.xdc]
			set ::env(PNR_USER) [get_files */cl_pnr_user.xdc]			
		} else {
		set ::env(PNR_USER) [get_files */cl_pnr_user.xdc]
		}
	
		if {[get_files */tb.sv -quiet] == ""} {

			source $::aws::make_faas::_nsvars::script_dir/add_hdk_rtl_ip.tcl

add_files -fileset sim_1 [ list \
  $::env(HDK_SHELL_DESIGN_DIR)/sh_ddr/sim/sync.v\
  $::env(HDK_SHELL_DESIGN_DIR)/sh_ddr/sim/flop_ccf.sv\
  $::env(HDK_SHELL_DESIGN_DIR)/sh_ddr/sim/ccf_ctl.v\
  $::env(HDK_SHELL_DESIGN_DIR)/sh_ddr/sim/mgt_acc_axl.sv  \
  $::env(HDK_SHELL_DESIGN_DIR)/sh_ddr/sim/mgt_gen_axl.sv  \
  $::env(HDK_SHELL_DESIGN_DIR)/sh_ddr/sim/sh_ddr.sv
]

			source $::aws::make_faas::_nsvars::script_dir/add_simulation.tcl

set_property -name {xsim.compile.tcl.pre} -value $::aws::make_faas::_nsvars::script_dir/../../verif/scripts/dpi_xsim.tcl -objects [get_filesets sim_1]
set_property -name {xsim.elaborate.xelab.more_options} -value {-sv_lib dpi} -objects [get_filesets sim_1]

set_property -name {questa.compile.tcl.pre} -value $::aws::make_faas::_nsvars::script_dir/../../verif/scripts/dpi.tcl -objects [get_filesets sim_1]
set_property -name {questa.compile.vlog.more_options} -value {-timescale 1ps/1ps +define+QUESTA_SIM} -objects [get_filesets sim_1]
set_property -name {questa.simulate.vsim.more_options} -value {-sv_lib libdpi} -objects [get_filesets sim_1]


set_property -name {ies.compile.tcl.pre} -value $::aws::make_faas::_nsvars::script_dir/../../verif/scripts/dpi.tcl -objects [get_filesets sim_1]
set_property -name {ies.compile.ncvlog.more_options} -value {+define+SV_TEST +define+SCOPE +define+IES_SIM} -objects [get_filesets sim_1]
set_property -name {ies.elaborate.ncelab.more_options} -value {+libext+.v+.sv -disable_sem2009 -timescale 1ps/1ps} -objects [get_filesets sim_1]
set_property -name {ies.simulate.ncsim.more_options} -value {-sv_lib libdpi} -objects [get_filesets sim_1]
        

set_property -name {vcs.compile.tcl.pre} -value $::aws::make_faas::_nsvars::script_dir/../../verif/scripts/dpi.tcl -objects [get_filesets sim_1]
set_property -name {vcs.compile.vlogan.more_options} -value {-ntb_opts tb_timescale=1ps/1ps -timescale=1ps/1ps -sverilog +systemverilogext+.sv +libext+.sv +libext+.v -full64 -lca -v2005 +v2k +define+VCS_SIM} -objects [get_filesets sim_1]
set_property -name {vcs.simulate.vcs.more_options} -value {-sv_lib libdpi} -objects [get_filesets sim_1]


			}			
	}
	
	return
}

source [file dirname [info script]]/aws_proc_overrides.tcl
if {[info exist ::env(OS)] eq 0} {
	#info_msg "OS Environment variable not set, assuming Linux"
	set ::env(OS) "linux"
}
if {[string match "*windows*" [string tolower $::env(OS)]]} {
	source [file dirname [info script]]/hdk_setup.tcl
}

