#© Copyright 2017 Xilinx, Inc. All rights reserved.

#This file contains confidential and proprietary information of Xilinx, Inc. and is protected under U.S. and
#international copyright and other intellectual property laws.

#DISCLAIMER
#This disclaimer is not a license and does not grant any rights to the materials distributed herewith.
#Except as otherwise provided in a valid license issued to you by Xilinx, and to the maximum extent
#permitted by applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
#FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS, IMPLIED, OR
#STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NONINFRINGEMENT,
#OR FITNESS FOR ANY PARTICULAR PURPOSE; and (2) Xilinx shall not be liable (whether
#in contract or tort, including negligence, or under any other theory of liability) for any loss or damage of
#any kind or nature related to, arising under or in connection with these materials, including for any
#direct, or any indirect, special, incidental, or consequential loss or damage (including loss of data,
#profits, goodwill, or any type of loss or damage suffered as a result of any action brought by a third
#party) even if such damage or loss was reasonably foreseeable or Xilinx had been advised of the
#possibility of the same.

#CRITICAL APPLICATIONS
#Xilinx products are not designed or intended to be fail-safe, or for use in any application requiring failsafe
#performance, such as life-support or safety devices or systems, Class III medical devices, nuclear
#facilities, applications related to the deployment of airbags, or any other applications that could lead to
#death, personal injury, or severe property or environmental damage (individually and collectively,
#"Critical Applications"). Customer assumes the sole risk and liability of any use of Xilinx products in
#Critical Applications, subject only to applicable laws and regulations governing limitations on product
#liability.

#THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE AT ALL TIMES.




set _make_faas_version 0.911
#NYI indicates Not Yet Implemented
#0.850-	initial files
#0.904- set_params for 2017.1*
#0.905- inline implementation flow added, bd.faas_initscript (...::make_faas::public::bd_faas_initscript et.al.)
#0.907- fixed some issues with examples, moved the namespace
#0.908- directory structure - NYI
#0.909- Move DRC for RTL (-bypass) mode
#0.911- Moved bd_location env, messaging cleanup
#0.912- add -selftest option (tcl testbench) - NYI
#0.962- export sim? -NYI


# make_faas commands (NYI)
# make_ipi_faas
# make_ipi_faas_setup
# make_ipi_faas_all
# make_rtl_faas

#post inline - only need to install one custom button
#extra namespace - add into another file (elmo_me.tcl) 

package require Vivado 1.2015.1

#set _THISNAMESPACE "::tclapp::xilinx::designutils"
set _THISNAMESPACE "::tclapp::xilinx::faasutils"
set _THISTOPSPACE  "make_faas"


################################################################################
# hlx::Procs
################################################################################
namespace eval ${_THISNAMESPACE} { 
	namespace eval ${_THISTOPSPACE} {
		if {[info exist [set _THISNAMESPACE]::[set _THISTOPSPACE]::public::keepvars] eq 0} {
			namespace eval public {
				# public are locations / variables that exist from the perspective of the FaaS solution provider
				set bd_faas_root [file normalize [file join [file dirname [info script]] .. .. .. github hdk common hlx_v062517b4]]
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
			set script_loc [file tail [info script]]
			set version $_make_faas_version
#			set examples_directory ""
			# call as $_nsvars::script_dir in other procs :)
			set _VARNAMESPACE $_THISNAMESPACE
			set _VARTOPSPACE $_THISTOPSPACE
			# call as $_nsvars::_THISTOPSPACE
		}
	}
	namespace export [set _THISTOPSPACE] 
}


proc [set _THISNAMESPACE]::make_faas {{args ""}} {
	# Summary: 

#regexp_switch_arguments [list -bypass_drcs -examples -force -no_encyrpt -output_directory -partial -cache_directory -version -help -usage -resource]

	# Argument Usage:
	#[-bypass_drcs]: skip DRC checks (else run prior to action)
	#[-examples 
	#[-force]: forces project & IP to match requirements (NYI)
	#[-reset]: resets current state, entire flow is rerun (NYI)
	#[-install]: installs board / ip / app / cache / other (NYI)
	#[-output_directory]: output directory
	#[-encrypt_sources]: encrypt sources (else encrypt DCP)
	#[-global_synth]: use global synthesis (else use OOC2)

	# Return Value: 0

	# Categories: HLx, IP Integrator, Vivado, FaaS

	set _THISNAMESPACE $make_faas::_nsvars::_VARNAMESPACE
	set _THISTOPSPACE  $make_faas::_nsvars::_VARTOPSPACE

	return [uplevel [concat [list [set _THISNAMESPACE]::[set _THISTOPSPACE]::[set _THISTOPSPACE] {*}$args]]]
}
eval [list namespace eval [set _THISNAMESPACE]::[set _THISTOPSPACE] { } ]
#eval [list namespace eval [set _THISNAMESPACE]::make_ipi_faas { } ]
#eval [list namespace eval [set _THISNAMESPACE]::make_rtl_faas { } ]

# Add subprocs & other required procs
source [file join [file dirname [info script]] subprocs.tcl] -quiet
source [file join [file dirname [info script]] encrypt_synth_files.tcl] -quiet
source [file join [file dirname [info script]] helper.tcl] -quiet

################################################################################
# Alternative Tops
################################################################################
proc [set _THISNAMESPACE]::make_ipi_faas_setup {{args ""}} {
  # Summary : Run through synthesis for an IP Integrator GUI flow for FaaS
  # Argument Usage:
  # Return Value:
  # Categories:
	return [make_faas -force -partial {*}$args]
}
proc [set _THISNAMESPACE]::make_ipi_faas_all {{args ""}} {
  # Summary : Run through implementation for an IP Integrator GUI flow for FaaS
  # Argument Usage:
  # Return Value:
  # Categories:
	return [make_faas -force {*}$args]
}
proc [set _THISNAMESPACE]::make_ipi_faas {{args ""}} {
  # Summary : Run through synthesis for an IP Integrator GUI flow for FaaS
  # Argument Usage:
  # Return Value:
  # Categories:
	return [make_faas -force {*}$args]
}
proc [set _THISNAMESPACE]::make_rtl_faas {{args ""}} {
  # Summary : Run through synthesis for an IP Integrator GUI flow for FaaS
  # Argument Usage:
  # Return Value:
  # Categories:
	return [make_faas -bypass_drcs {*}$args]
}

################################################################################
#  HELPERS
################################################################################
proc [set _THISNAMESPACE]::[set _THISTOPSPACE]::make_faas_help {} {
  # Summary :
  # Argument Usage:
  # Return Value:
  # Categories:


puts "$_nsvars::_VARNAMESPACE\::make_faas"
puts [format {

Usage:
  Name			Description
  ---------------------------------
  [-examples <name>] (optional) creates an example project.  Use -examples list to list all available examples
  [-inline_examples <name>] (optional) Same as -examples, but works in the current project.
  [-save_examples <name>] (optional) Saves your current IP Integrator diagram to an example project that can be resourced.  Project is saved in the [PWD] directory structure.
  [-partial] (optional) Stops the command prior to synthesis, useful in setting up a project.
  [-force] (optional) sets project and IP directories to match TCL App directory 
      DEFAULTED ON for make_ipi_faas_setup
  [-bypass_drcs] (optional) skip DRC checks for IP Integrator & Project/Board aware flow (default: run prior to action)
      DEFAULTED TO ON for make_rtl_faas
  [-output_directory] (optional) output directory (default: use PWD)
  [-cache_directory] (optional) directory to cache IP Out-Of-Context synthesis to (default: local project) - Not Yet Implemented

Summary: 

Return Value: 
  0

Categories: 
  HLx, IP Integrator, IP Packager

Example:
  The following ...

	::tclapp::xilinx::faasutils::make_faas

} ]
}

################################################################################
################################################################################
#                                                                              #
#                                MAIN PROC                                     #
#                                                                              #
################################################################################
################################################################################
proc [set _THISNAMESPACE]::[set _THISTOPSPACE]::make_faas {{args ""}} {
  # Summary :
  # Argument Usage:
  # Return Value:
  # Categories:

	upvar 1 env parent_env 
	set ::parent_env(example_env_var) 1

# Namespace Proc Variables
	set _procName $_nsvars::_VARTOPSPACE

# Local Proc Variables
	set arg_error 1
	set debugMode 0
	set help 0
	set usage 0
	set resource 0
	set first_time 0

#0.860a
	if {[string tolower [version -short]] eq "2017.1"} {
	
		# Vendor Specific values
		set _faas_ip_vlnv "*:ip:aws:*"
		set _faas_board "f1_cl"
		set _faas_interface "S_SH"
	} else {	
		set _faas_ip_vlnv "*[lindex [lsort [get_param bd.faas_ipname]] end]*"
		set _faas_board [get_param bd.faas_board]
		set _faas_interface [get_param bd.faas_interface]

#TODO FILE CR (missing part0 in bd.faas_board)
		set _faas_board_list [split $_faas_board ":"]
		set _faas_board_length [llength $_faas_board_list]

		if {[lsearch $_faas_board_list part0] > -1} {
			dputs $debugMode "Updating board based on part0"
			set _faas_board [lindex $_faas_board_list [expr ( [lsearch $_faas_board_list part0] - 1 ) ] ]
			set _faas_board "xilinx.com:$_faas_board:part0:1.0"			
		} elseif {$_faas_board_length eq 2} {
			dputs $debugMode "Updating board based 2 elements"
			set _faas_board "xilinx.com:[lindex $_faas_board_list 1]:part0:1.0"
		} elseif {$_faas_board_length eq 3} {
			if {[lindex $_faas_board_list 0] eq "xilinx.com"} {
				dputs $debugMode "Updating board based on xilinx.com"
				set _faas_board "xilinx.com:[lindex $_faas_board_list 1]:part0:1.0"
			} else {
				dputs $debugMode "Updating board based on missing xilinx.com"
				set _faas_board "xilinx.com:[lindex $_faas_board_list 0]:part0:1.0"
			}
		} elseif {$_faas_board_length eq 4} {
			#no-op
		} else {
			#set_msg_config -id {common 17-39} -suppress
			send_msg_id "$_procName 0-0" "ERROR" "Parameter bd.faas_board not set prpertly, please set the correct paramters in your vivado_init.tcl (set_param bd.faas_board xilinx.com:f1_cl:part0:1.0)"
			return 187
		}

	}
# More Vendor Specific values
	set max_num_cl_ip 1
	# max_num_cl_ip sets a DRC to only allow upto this number of IP onto canvas, use 2 if splitting master/slave interfaces onto 2 blocks

# Manually set per FaaS Vendor
	set _faas_instance [lindex [split $_faas_ip_vlnv ":"] 2]
	set _faas_auto_instance_until_version_short 2017.3
	# _faas_auto_instance_until... automatically adds the IP when testing in earlier versions.  Auto add is enabled with bd.faas params starting in 2017.3, 2017.1_sdx




#0.859- check for option on write_checkpoint, else encrypt here
	set _write_checkpoint_can_encrypt 0
#0.860c
	set write_checkpoint_is_posthook 1


# Proc Argument Defaults
	set force 0
#0.859 - remove source file encryption	set no_encrypt 0
	set no_encrypt 1
	set output_directory ""
	set bypass_drcs 0
	set examples ""
	set partial_examples 1
	set save_examples 0
	set inline_examples 0
#temp override - set cache_directory to "" to use local cache or customer set cache
#	set cache_directory ""
	set cache_directory "inside make_faas app"

	if {$_write_checkpoint_can_encrypt} {
		set encrypt_sources 0
	} else {
		set encrypt_sources 1
	}

while {[llength $args]} {
#created with regexp_switch_arguments.tcl
#regexp_switch_arguments [list -bypass_drcs -examples -save_examples -inline_examples -force -no_encyrpt -output_directory -partial -cache_directory -version -help -usage -resource]
	set name [string tolower [lshift args]]
	switch -regexp -- $name {
		-bypass_drcs -
		{^-b(y(p(a(s(s(_(d(r(c(s?)?)?)?)?)?)?)?)?)?)?$} {
			set bypass_drcs 1
			#set bypass_drcs [lshift args]
		}
		-examples -
		{^-e(x(a(m(p(l(e(s?)?)?)?)?)?)?)?$} {
			set examples [lshift args]
			if {$examples eq ""} {
				set examples "list"
			}
		}
		-save_examples -
		{^-s(a(v(e(_(e(x(a(m(p(l(e(s?)?)?)?)?)?)?)?)?)?)?)?)?$} {
			set save_examples 1
			set examples [lshift args]

		}
		-inline_examples -
		{^-i(n(l(i(n(e(_(e(x(a(m(p(l(e(s?)?)?)?)?)?)?)?)?)?)?)?)?)?)?$} {
			set inline_examples 1
			set examples [lshift args]
		}
		-force -
		{^-f(o(r(c(e?)?)?)?)?$} {
			set force 1
		}
		-no_encyrpt -
		{^-n(o(_(e(n(c(y(r(p(t?)?)?)?)?)?)?)?)?)?$} {
			set no_encrypt 1
		}
		-output_directory -
		{^-o(u(t(p(u(t(_(d(i(r(e(c(t(o(r(y?)?)?)?)?)?)?)?)?)?)?)?)?)?)?)?$} {
			set output_directory [lshift args]
		}
		-cache_directory -
		{^-c(a(c(h(e(_(d(i(r(e(c(t(o(r(y?)?)?)?)?)?)?)?)?)?)?)?)?)?)?$} {
			set cache_directory [lshift args]
			if {$cache_directory eq "" || $cache_directory eq "on"} {
				set cache_directory "inside make_faas app"
			}
		}
		-partial -
		{^-p(a(r(t(i(a(l?)?)?)?)?)?)?$} {
			set partial_examples 1
		}
		-version -
		{^-v(e(r(s(i(o(n?)?)?)?)?)?)?$} {
			puts $_nsvars::version
			return
		}
		-help -
		{^-h(e(l(p?)?)?)?$} {
			set help 1
		}
		-usage -
		{^-u(s(a(g(e?)?)?)?)?$} {
			set usage 1
		}
		-resource -
		{^-r(e(s(o(u(r(c(e?)?)?)?)?)?)?)?$} {
			set resource 1
		}
		default {
			if {[string match "-*" $name]} {
				send_msg_id "$_procName 0-187" "ERROR" "ption '$name' is not a valid option. Use the -help option for more details"
				set help 1
			} else {
				set _mainArg $name
			}
		}
	}
}


	if {$resource} {
		puts "-resource option not supported (works in wrong namespace), please run the following command"
		set _file_was [file join $_nsvars::script_dir $_nsvars::script_loc]
		puts "  source $_file_was"
#		source $_file_was
#		puts "$_file_was updated"
		return {}
	}

	if {$help || $usage} {
		make_faas_help
		return {}
	}

################################################################################
#  USER CODE HERE
################################################################################

	########################################################################
	#  Step -100: Load an example
	########################################################################
	if {$examples ne ""} {
		dputs $debugMode "Loading Examples"
		set _examples_board [split [string map {":" " "} $_faas_board] " "]
		set _examples_board [regexp -all -inline {\S+} $_examples_board]
		if {[llength $_examples_board] eq 0} {
			send_msg_id "$_procName 0-0" "ERROR" "Parameter bd.faas_board not set properly, please set the correct paramters in your vivado_init.tcl (set_param bd.faas_board xilinx.com:f1_cl:part0:1.0)"
			return 187
		} elseif {[llength $_examples_board] > 1} {
			#check for part0
			if {[lsearch $_examples_board part0] < 0} {
				if {[llength $_examples_board] eq 2} {
					set _examples_board [lindex $_examples_board 1]
				} else {
					send_msg_id "$_procName 0-0" "ERROR" " Unable to determine correct board.  Please set parameter bd.faas_board to <vendor>:<board name>:part0:<version>"
					return 8
				}
			} else {
				set _examples_board [lindex $_examples_board [expr ( [lsearch $_examples_board part0] - 1 ) ] ]
			}
		}

		set example_list ""
		set example_dirs "$_nsvars::script_dir/$_examples_board\_examples/sed/IPI"
		lappend example_dirs "$user::examples_directory"
		lappend example_dirs "$user::examples_directory/$_examples_board\_examples"
		lappend example_dirs "$user::examples_directory/$_examples_board\_examples/sed"
		lappend example_dirs "$user::examples_directory/$_examples_board\_examples/sed/IPI"
		lappend example_dirs "$public::bd_faas_examples_directory"
		lappend example_dirs "$public::bd_faas_examples_directory/IPI"
		lappend example_dirs "$public::bd_faas_examples_directory/build/IPI"
		lappend example_dirs "$public::bd_faas_examples_directory/hlx_examples/build/IPI"
		foreach {example_dir} $example_dirs {
			if {[file isdirectory $example_dir]} {
				set this_dirs [glob -types d -directory $example_dir *]
				foreach {this_dir} $this_dirs {
					if {[file exist [file join $this_dir init.tcl ]]} {
						set this_tail [file tail $this_dir]
						if {[lsearch $example_list $this_tail] > -1} {
							send_msg_id "$_procName 1-13" "CRITICAL WARNING" "Duplicate example $this_tail found in $this_dir, ignoring.  Please modify the directory name for uniqueness.\n e.g.\n\tfile rename $this_dir $this_dir\_[incr dupcount]"
						} else { 
							lappend example_list [file tail $this_dir]
							lappend example_find [file tail $this_dir]
							lappend example_find [file join $this_dir init.tcl]
						}
					}
				}
			}
		}


		if {[string match [string tolower $examples] "list"]} {
			puts "Available examples for $_faas_board:"
			set spacespaceN "\n  "
			puts "  [join [lsort $example_list] $spacespaceN]"
			return 
		} elseif {$save_examples} {
			set examples_DisplayName "$examples (IPI)"
			set examples_Name $examples
			regsub -all { } $examples_Name {_} examples_Name
			regsub -all {[~!@#$%^&*()-+]} $examples_Name {} examples_Name
			regsub -all {[`=\|"';:/?.>,<]} $examples_Name {} examples_Name
			

			if {$user::examples_directory eq ""} {
				set user::examples_directory [pwd]
			}
			file mkdir [file normalize [file join $user::examples_directory $_examples_board\_examples ]]
			set example_directory [file normalize [file join $user::examples_directory $_examples_board\_examples $examples_Name ]]
			

			dputs $debugMode "Saving Example Design to directory $example_directory"
			if {[file isdirectory $example_directory]} {
				set rename_example_directory $example_directory\_[clock format [clock seconds] -format "%y_%m_%d-%H%M%S"]
				dputs $debugMode " Renaming $example_directory to $rename_example_directory"
				file rename $example_directory $rename_example_directory
			}
			file mkdir $example_directory
			set bd_faas_examples_templates [file normalize [file join public::bd_faas_examples_directory .. IPI_template  ]]
			foreach {thisFile} [list params.tcl init.tcl faas_project.tcl supported_parts_boards.tcl] {
				set check_file [file join $_nsvars::script_dir  sed IPI_template $thisFile]
				if {[file exist $check_file]} {
					file copy -force $check_file [file join $example_directory $thisFile]
				} 
			}
			if {[get_files -quiet cl.bd] ne ""} {
				if {[current_bd_design -quiet] eq ""} {
					open_bd_design [get_files cl.bd]
				}
				write_bd_tcl -force [file join $example_directory $examples_Name]
			}
			set writeThisFile [open [file join $example_directory design.xml] w]
			puts $writeThisFile "<ExampleDesign>\n<Vendor>xilinx.com</Vendor>\n<Library>design</Library>"
			puts $writeThisFile "<Name>$examples_Name</Name>\n<Version>1.0</Version>"
			puts $writeThisFile "<Design>init.tcl</Design>\n<DisplayName>$examples_DisplayName</DisplayName>"
			puts $writeThisFile "<Description>$examples_DisplayName</Description>\n<Image>$examples_Name.png</Image>\n</ExampleDesign>"
			close $writeThisFile


			return [make_faas -examples list]
		} else {
			if {[lsearch $example_list $examples] < 0} {
				puts "example $examples not found"
				puts "Available examples for $_faas_board:"
				set spacespaceN "\n  "
				puts "  [join [lsort $example_list] $spacespaceN]"
				return 10
			} else {
				if {$inline_examples eq 1 && [get_files -quiet cl.bd] ne ""} {
					set errorCode 100
					send_msg_id "$_procName 0-$errorCode" "ERROR" "cl.bd already exists, attempting to overwrite failed.  Please manually delete cl.bd prior to running $_procName with -inline_examples swtich."
					return $errorCode
				} else {
					set example_found [ expr ( [lsearch $example_find $examples] + 1 ) ]
					if {$example_found <= [llength $example_find]} {
						if {$debugMode eq 1} { 
							source [lindex $example_find $example_found] 
						} else {
							source [lindex $example_find $example_found] -notrace
						}
						set partial_examples 1
					}

					if {$output_directory ne ""} {
						set output_directory [get_property DIRECTORY [current_project]]
					}
				}
			}
		}
	}
	

	########################################################################
	#  Step -1: Only work in project mode
	########################################################################
	dputs $debugMode "Step -1: Checking for project"
	if { [ catch {
		set _cproj [current_project -quiet]
	} err ] } { 
		if {$_cproj eq ""} {
			set errorCode 12
			send_msg_id "$_procName 0-$errorCode" "ERROR" "$_procName User Exception: No open project. Please create or open a project before executing this command."
			return $errorCode
		}
	}

	########################################################################
	#  Step 0: Install / Autoinstall?
	########################################################################
	if {$force} {
		dputs $debugMode "Step 0: Force and Install"
		# Auto-add board files
		if {[lsearch [get_board_parts] "*$_faas_board*" ] < 0} {
			set urepo1 [file join $_nsvars::script_dir boards]
			set_property BOARD_PART_REPO_PATHS ${urepo1} [current_project]
			dputs $debugMode "Added board repository [get_property BOARD_PART_REPO_PATHS [current_project]]"

		}
		if {[lsearch [get_board_parts] "*$_faas_board*" ] < 0} {
			set urepo1 [file join $public::bd_faas_design_directory]
			set_property BOARD_PART_REPO_PATHS ${urepo1} [current_project]
			dputs $debugMode "Added board repository [get_property BOARD_PART_REPO_PATHS [current_project]]"

		}


		if {[llength [get_board_parts "*$_faas_board*"]] > 1} {
			set errorCode 200
			send_msg_id "$_procName 0-$errorCode" "ERROR" "$_procName User Exception: Too many available boards match $_faas_board.  Please set parameter bd.faas_board to one of the following boards.\n[join [get_board_parts *$_faas_board*] \n]"
			return $errorCode
		} elseif {[current_board_part -quiet] ne [get_board_parts "*$_faas_board*"]} {
			dputs $debugMode "INFO: setting current project to board [get_board_parts *$_faas_board*]"
			set_property board_part [get_board_parts "*$_faas_board*"] [current_project]
		}
			
		# Auto-update IP repository to add IP in TCL App Repo to this project
		dputs $debugMode "INFO: Checking for IP Install"
		if {[lsearch [get_ipdefs] $_faas_ip_vlnv] < 0} {
			set warnCode 2
			send_msg_id "$_procName 1-$warnCode" "WARNING" "IP $_faas_ip_vlnv not found, attempting to add IP Repository to project"
#			set_property  ip_repo_paths  [file join $_nsvars::script_dir ip]  [current_project]
			set_property  ip_repo_paths  [file join $public::bd_faas_design_directory]  [current_project]
#TODO: FILE CR, adding PWD
#			set_property  ip_repo_paths  [list [get_property ip_repo_paths [current_project]] [file join $_nsvars::script_dir ip] ] [current_project]
			update_ip_catalog
		}
		if {[lsearch [get_ipdefs] $_faas_ip_vlnv] < 0} {
			send_msg_id "$_procName 0-$warnCode" "ERROR" "IP $_faas_ip_vlnv not found in [get_property ip_repo_paths [current_project]]"
		}
		if {[info exist DELAYEDEXAMPLE]} {
			dputs $debugMode "INFO: \[$_procName\] $DELAYEDEXAMPLE"
			{*}$DELAYEDEXAMPLE
			unset DELAYEDEXAMPLE
			#examples hack back - no force on the IP/interface
			if {$_faas_board ne [get_param bd.faas_board]} {
				set_param bd.faas_board $_faas_board
			}
			set _faas_board_list [split $_faas_board ":"]
			set _faas_board_length [llength $_faas_board_list]
			if {$_faas_board_length eq 1} {
				set_param bd.faas_board "xilinx.com:$_faas_board:part0:1.0"			
			}

		}
#		# Auto-update board files to add boards in TCL App Repo to this project
#		if {[lsearch [get_board_parts] $_faas_board ] < 0} {
#			dputs $debugMode "INFO: Updating Board Files for this project"
#			set urepo1 [file join $_nsvars::script_dir boards]
#			set_property BOARD_PART_REPO_PATHS ${urepo1} [current_project]
#		}
	}


	########################################################################
	#  Step 1: Run DRCs
	########################################################################
	dputs $debugMode "Step 1: DRCs"
	set _cl_ips ""
	if {$bypass_drcs eq 0} {
		# Test for: board
		if {[lsearch [get_board_parts] *$_faas_board* ] < 0} {
			dputs $debugMode "INFO: Updating boards available to this project"
			set urepo1 [file join $_nsvars::script_dir boards]
			set_property BOARD_PART_REPO_PATHS ${urepo1} [current_project]

		}
		if {[lsearch [get_board_parts] "*$_faas_board*" ] < 0} {
			set urepo1 [file join $public::bd_faas_design_directory]
			set_property BOARD_PART_REPO_PATHS ${urepo1} [current_project]
			dputs $debugMode "Added board repository [get_property BOARD_PART_REPO_PATHS [current_project]]"

		}
		if {[string match [get_board_parts "*$_faas_board*"] [current_board_part -quiet]] eq 0} {
			set errorCode 3
			send_msg_id "$_procName 0-$errorCode" "ERROR" "Required board [get_board_parts *$_faas_board*] is not the current board - [current_board_part -quiet], please set the board correctly or use \"$_procName -force\" to update the project"
			return $errorCode
		} 


		# Test for: cl.bd
		set _mandatoryBD [get_files -quiet cl.bd]
		set _theBDs [get_files -filter {FILE_TYPE == "Block Designs"} -quiet]
		if {[lsearch $_theBDs $_mandatoryBD] < 0} {
				if {$force} {
				# Force Update cl.bd
					set first_time 1
					set warnCode 1
					set warnMessage "\[$_procName 1-$warnCode\] Required file $_mandatoryBD not found in current sources list, adding a block diagram named \"cl\" to your project"
					set warnInfo $warnMessage
					puts "WARNING: $warnMessage"
					create_bd_design "cl"
#					update_compile_order -fileset sources_1
					#Add IP in 2017.1
					set version_split [split [version -short] "_"]
					if {[lindex $version_split 1] eq "sdx" || [lindex $version_split 1] eq "sdxop" } {
						set version_add 0.2
					} else {
						set version_add 0.0
					}
					set version_short [ expr ( [lindex $version_split 0] + $version_add ) ]
					if {$version_short < $_faas_auto_instance_until_version_short} {
						create_bd_cell -type ip -vlnv [get_ipdefs $_faas_ip_vlnv] $_faas_instance\_0
						make_bd_intf_pins_external  [get_bd_intf_pins $_faas_instance\_0/$_faas_interface]
					}
				} else {
					set errorCode 1
					send_msg_id "$_procName 0-$errorCode" "ERROR" "Required file $_mandatoryBD not found in current sources list, please add a block diagram named \"cl\" to your project"
					return $errorCode
				}
		} else {
			# generate IP Integrator IP files if necessary
			open_bd_design [get_files -quiet cl.bd]
			validate_bd_design
			set _full_loc_bd [lindex $_theBDs [lsearch $_theBDs $_mandatoryBD]]
			generate_target all [get_files  $_full_loc_bd]

		}
#		set ::env(BD_LOCATION) [get_files cl.bd]

		# Test for multiple IPs (not at end of script)
		open_bd_design [get_files -quiet cl.bd]
		set _cl_ipdefs [get_ipdefs $_faas_ip_vlnv]
		foreach {_cl_ipdef} $_cl_ipdefs {
			set this_bd_cell [get_bd_cell -hierarchical -filter "VLNV == $_cl_ipdef"]
			lappend _cl_ips $this_bd_cell
			# EXPORT _cl_ips to create_dcp_from_magic.tcl - will use variable _cl_ips later in this proc
		}
		if {[llength $_cl_ips] > $max_num_cl_ip} {
			puts 
			set errorCode 7
			send_msg_id "$_procName 0-$errorCode" "ERROR" "Too many cl IP instantiated in cl.bd. Current lit is "
			return $errorCode
		}

		# Test for: cl_top.sv
		set _theFiles [get_files -quiet -filter {FILE_TYPE == VHDL || FILE_TYPE == Verilog || FILE_TYPE == SystemVerilog} -compile_order sources -used_in synthesis]
		set _mandatoryFiles [get_files -quiet cl_top.sv]
		# Auto-add cl_top.sv
		if {[lsearch $_theFiles cl_top.sv] < 0 && $force eq 1} {
#			add_files -norecurse [file join $_nsvars::script_dir src cl_top.sv]
			add_files -norecurse [file join $public::bd_faas_design_directory lib cl_top.sv]
		}

		# IPI: test for cl_top_wrapper.v, IP exists? (not in  RTL only?)
# not used	lappend _mandatoryFiles "cl_wrapper.v"
#		lappend _mandatoryFiles [get_files -quiet cl.v]
	
#		dputs $debugMode "INFO: Checking for necessary files ($_mandatoryFiles)"
#		foreach {_mandatoryFile} $_mandatoryFiles {		
#			if {[lsearch $_theFiles $_mandatoryFile] < 0} {
#				set errorCode 2
#				send_msg_id "$_procName 0-$errorCode" "ERROR" "Required file $_mandatoryFile not found in current synthesis files list, please generate correct files / set correct level / or use \"$_procName -force\" to update the project"
#				return $errorCode
#			}
#		}
	}	


	########################################################################
	#  Step 1b: Check Args (output_directory)
	########################################################################
	dputs $debugMode "Step 1b: Arg Check"
	set DOTIMESTAMPOPTION 1	
	if {$DOTIMESTAMPOPTION ne 0} {
		# Timestamp on output_directory
		set _now [clock format [clock seconds] -format "%y_%m_%d-%H%M%S"]
		set ::env(timestamp) $_now
	} else {
		set _now ""
	}
	if {$output_directory ne ""} {
		#set output_directory "$output_directory\_$_now"
		# check if output_directory exists, else make it
		if {[file isdirectory $output_directory] eq 0} {
			file mkdir $output_directory
		}
	} else {
#		set output_directory [file join [pwd] "faas_results_$_now"]
		set output_directory [get_property DIRECTORY [current_project]]
	}
#	set _nsvars::output_directory $output_directory
	dputs $debugMode "INFO: output directory is $output_directory"

	set synth_run_number [string map {"synth_" ""} [current_run -synthesis]]
	set project_name [get_property NAME [current_project]]
	set _faas_runs_dir [file normalize [file join $output_directory $project_name.runs faas_$synth_run_number ]]
#	set _faas_runs_dir [file normalize [file join $output_directory $project_name.runs faas_$synth_run_number $::env(timestamp)]]


	########################################################################
	#  Step 2: (Re)Set Project Options
	########################################################################
	dputs $debugMode "Step 2: Project Settings"

	if {[get_param bd.faas_initscript -quiet] ne ""} {
		set ::env(FAAS_HOOK_FILE) [get_param bd.faas_initscript -quiet]
	} elseif {[info exists ::env(FAAS_HOOK_TCL)]} { 
	} elseif {[info exist public::bd_faas_initscript]} {
		set ::env(FAAS_HOOK_FILE) $public::bd_faas_initscript
	} else {
		set ::env(FAAS_HOOK_FILE) [file join $_nsvars::script_dir make_faas_subscript_variables.tcl]
	}

	if { [file exists $::env(FAAS_HOOK_TCL)] } {
		source -quiet $::env(FAAS_HOOK_TCL)
	} else {
		send_msg_id "$_procName 1-91" "CRITICAL WARNING" "Required file $::env(FAAS_HOOK_TCL) does not exist, please set the ::env(FAAS_HOOK_TCL) variable to a valid file"
	}

#	set _list_steps [info vars [set _VARNAMESPACE]::[set _VARTOPSPACE]::_nsvars::STEPS*]
	set _list_steps [lreverse [info vars _nsvars::STEPS*]]
	foreach {_list_step} $_list_steps {
		set _list_name [lindex [wsplit $_list_step "::"] end]
		set _list_value [set $_list_step]
		set _list_object [set [string map {"STEPS" "INSTEPS"} $_list_step]]
		dputs $debugMode "setting property \n\t-name $_list_name\n\t-value $_list_value\n\t -objects \get_runs \[current_run $_list_object\]\]"
		set_property -name $_list_name -value $_list_value -objects [get_runs [current_run $_list_object]]
	}

	if {$cache_directory eq "inside make_faas app"} {
		set cache_directory [file join $_nsvars::script_dir ip cache]
	}
	if {$cache_directory eq "inside make_faas app"} {
		set cache_directory [file join $public::bd_faas_design_dirctory cache]
	}
	if {$cache_directory ne ""} {
		config_ip_cache -import_from_project -use_cache_location $cache_directory
		update_ip_catalog
	}

	# Environment Variables - current location
	if {[get_files -quiet cl.bd] ne ""} {
		set ::env(BD_LOCATION) [get_files cl.bd]
	}
	set ::env(FAAS_CL_DIR) $_faas_runs_dir
	set ::env(FAAS_SCRIPT_DIR) $_nsvars::script_dir
	file mkdir [file join $::env(FAAS_CL_DIR) build checkpoints]

	puts "INFO: \[$_procName 10-1\] Finished setting up project [current_project] for enhanced FaaS flow with Vivado HLx."


	########################################################################
	#  Step 2b: Encrypt prior to synthesis (optional)
	########################################################################
#0.859 - remove source file encryption - commented out this section
#	if {$no_encrypt eq 0 && $encrypt_sources eq 1} {
#		dputs $debugMode "Step 2b: Pre-encrypt RTL"
#		encrypt_synth_files
#	}


	return 0
}




