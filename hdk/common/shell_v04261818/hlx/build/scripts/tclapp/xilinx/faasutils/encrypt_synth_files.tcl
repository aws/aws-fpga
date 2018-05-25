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

set _esf_version 0.854
#0.850-	initial files
#0.851- do not attempt to encrypt .dcp files (somehow get in source list) - completed
#0.852- use FaaS key files
#0.853- add SystemVerilog & synth_run & nobackup & _now
#0.854- default copy the original file (if not encrypted), -nobackup - moves to .vhdcopy, .vcopy
#0.85x- remove new backup files if file was already encrypted NYI

package require Vivado 1.2015.1

#set _THISNAMESPACE "::tclapp::xilinx::designutils"
if {[info exist _THISNAMESPACE] eq 0} {
	set _THISNAMESPACE "hlx"
}
if {[info exist _THISTOPSPACE] eq 0} {
	set _THISTOPSPACE  "encrypt_synth_files"
}

################################################################################
# hlx::Procs
################################################################################
namespace eval ${_THISNAMESPACE} { 
	namespace eval ${_THISTOPSPACE} {
		namespace eval _nsvars {
			set script_dir [file dirname [info script]]
			# call as $_nsvars::script_dir in other procs :)
			set _VARNAMESPACE $_THISNAMESPACE
			set _VARTOPSPACE $_THISTOPSPACE
		}
	}
	namespace export [set _THISTOPSPACE] 
}


proc [set _THISNAMESPACE]::encrypt_synth_files {{args ""}} {
	# Summary: Run IEEE1732 v2 encryption on all files in the synthesis que

	# Argument Usage:
	#[-keep_original]: Create a copy of the original files and deliver encrypted files with either .vp or .vhdp
	#[-synth_run]: NYI? which synthesis run to use?
	#[-key]: Alternate keyfiles location, should contain keyfile_ver.txt, keyfile_vhd.txt

	# Return Value: Encrypted file list

	# Categories: HLx, IP Integrator, IP Packager, encryption

	set _THISNAMESPACE $encrypt_synth_files::_nsvars::_VARNAMESPACE
	set _THISTOPSPACE  $encrypt_synth_files::_nsvars::_VARTOPSPACE

	return [uplevel [concat [list [set _THISNAMESPACE]::[set _THISTOPSPACE]::[set _THISTOPSPACE] {*}$args]]]
}
eval [list namespace eval [set _THISNAMESPACE]::[set _THISTOPSPACE] { } ]

if {[info exists [set _THISNAMESPACE]::[set _THISTOPSPACE]::dputs] eq 0} {
	puts "Sourcing [file join [file dirname [info script]] subprocs.tcl]"
	source [file join [file dirname [info script]] subprocs.tcl]
}

################################################################################
#  HELPERS
################################################################################
proc [set _THISNAMESPACE]::[set _THISTOPSPACE]::encrypt_synth_files_help {} {
  # Summary :
  # Argument Usage:
  # Return Value:
  # Categories:

puts "$_nsvars::_VARNAMESPACE\::encrypt_synth_files"
puts [format {

Usage:
  Name			Description
  ---------------------------------
  [-keep_original] (optional) Create a copy of the original files and deliver 
	encrypted files with either .vp or .vhdp
  [-synth_run] (optional) Not Yet Implemented
  [-key] <directory_with_keys> (optional) Alternate keyfiles location, 
	directory should contain keyfile_ver.txt, keyfile_vhd.txt

Summary: 
  Run IEEE1732 v2 encryption on all files in the synthesis que

Return Value: 
  Encrypted file list

Categories: 
  HLx, IP Integrator, IP Packager, encryption

Example:
  The following runs encryption on the synthesis centric files

	hlx::encrypt_synth_files

} ]
}

################################################################################
################################################################################
#                                                                              #
#                                MAIN PROC                                     #
#                                                                              #
################################################################################
################################################################################
proc [set _THISNAMESPACE]::[set _THISTOPSPACE]::encrypt_synth_files {{args ""}} {
  # Summary :
  # Argument Usage:
  # Return Value:
  # Categories:

	upvar 1 env parent_env 

	set error 0
	set debugMode 1
	set help 0


	set keep_original 0
	set synth_run 0
	set key ""
	set nobackup 0
	set _now ""

	while {[llength $args]} {
	#created with regexp_switch_arguments.tcl
	#regexp_switch_arguments [list -keep_original -synth_run -key -nobackup -now -help -usage]
		set name [string tolower [lshift args]]
		switch -regexp -- $name {
			-keep_orignal -
			{^-kee(p(_(o(r(i(g(i(n(a(l?)?)?)?)?)?)?)?)?)?)?$} {
				set keep_original 1
			}
			-synth_run -
			{^-s(y(n(t(h(_(r(u(n?)?)?)?)?)?)?)?)?$} {
				set synth_run 1
			}
			-key -
			{^-key?$} {
				set key [lshift $args]
			}
			-nobackup -
			{^-nob(a(c(k(u(p?)?)?)?)?)?$} {
				set nobackup 1
			}
			-now -
			{^-now?$} {
				set _now [lshift $args]
			}
			-help -
			{^-h(e(l(p?)?)?)?$} {
				set help 1
			}
			-usage -
			{^-u(s(a(g(e?)?)?)?)?$} {
				set help 1
			}
			default {
				if {[string match "-*" $name]} {
					puts " -E- option '$name' is not a valid option. Use the -help option for more details"
					incr error
					return 1000
				} else {
					set _mainArg $name
				}
			}
		}
	}

	if {$help} {
		encrypt_synth_files_help
		return {}
	}

	if {$key eq ""} { set key $_nsvars::script_dir }
	set ext ""
	if {$keep_original} { set ext "-ext" }

#0.851	set _theFiles [get_files -compile_order sources -used_in synthesis]
	set _theFiles [get_files -filter {FILE_TYPE == VHDL || FILE_TYPE == Verilog || FILE_TYPE == SystemVerilog} -compile_order sources -used_in synthesis]

	foreach {_theFile} $_theFiles {
		if {[file exist $_theFile] && [get_files $_theFile] ne ""} {
			set _fileType [get_property FILE_TYPE [get_files $_theFile]]
#0.854
			if {$nobackup eq 0} {
				if {$_now eq ""} {
#					set _today [clock format [clock seconds] -format "%m%d%y"]
#					set _now "$_today\_[clock seconds]"
					set _now [clock format [clock seconds] -format "%y_%m_%d-%H%M%S"]
				}
				file copy $_theFile "$_theFile\_$_now"
			}
		} else {
			puts "No file found $_theFile"
			continue 
		}
		set _retFile $_theFile
		if {$_fileType eq "Verilog"} {
#0.852			set keyfile [file join $key keyfile_ver.txt]
			set keyfile [file join $key keyfile_v2.txt]
			set lang verilog
			if {$ext ne ""} {
				set ext ".vp"
				set _retFile [string map {".v" ".vp"} $_retFile]
			}
		} elseif {$_fileType eq "SystemVerilog"} {
#0.852/0.853		set keyfile [file join $key keyfile_ver.txt]
			set keyfile [file join $key keyfile_v2.txt]
			set lang verilog
			if {$ext ne ""} {
				set ext ".vp"
				set _retFile [string map {".v" ".vp"} $_retFile]
			}
		} else {
#0.852			set keyfile [file join $key keyfile_vhd.txt]
			set keyfile [file join $key keyfile_v2_vhd.txt]
			set lang vhdl
			if {$ext ne ""} {
				set ext ".vhdp"
				set _retFile [string map {".vhd*" ".vhdp"} $_retFile]
			}
		}
		if {$ext ne ""} {
			if { [ catch {
				encrypt -key $keyfile -lang $lang -ext $ext $_theFile
				dputs $debugMode "Running: encrypt -key $keyfile -lang $lang -ext $ext $_theFile"
			} err ] } { 
				if {[string match "*Vivado 12-3330*" $err] eq 0} {
					dputs $debugMode "$_nsvars::_VARNAMESPACE\::encrypt_synth_files - Copying $_theFile to backup $_theFile$_now"
					dputs $debugMode $err 
				} else {
					#remove copied file
					if {$_now ne ""} {
						file delete "$_theFile\_$_now"
					}
				}
			}
		} else {
			if { [ catch {
				encrypt -key $keyfile -lang $lang $_theFile
				dputs $debugMode "Running: encrypt -key $keyfile -lang $lang $_theFile"
			} err ] } { 
				if {[string match "*Vivado 12-3330*" $err] eq 0} {
					dputs $debugMode "$_nsvars::_VARNAMESPACE\::encrypt_synth_files - Copying $_theFile to backup $_theFile$_now"
					dputs $debugMode $err 
				} else {
					#remove copied file
					if {$_now ne ""} {
						file delete "$_theFile\_$_now"
					}
				}
			}
		}
		lappend _retFiles $_retFile
	}
	return $_retFiles
}




