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

set currentFile [file normalize [info script]]
set currentDir [file dirname $currentFile]

# source pre-calls (proc defines, params, boards, ip)
source -notrace [file join $currentDir params.tcl]
source -notrace [file join $currentDir supported_parts_boards.tcl]
if {[getSupportedBoards] eq ""} {
	set_param board.repoPaths [file join $currentDir boards]
}

#create project, create IPI
if {[info exist inline_examples] eq 0} {
	source -notrace [file join $currentDir faas_project.tcl]
} else {
	if {$inline_examples eq 0} {
		source -notrace [file join $currentDir faas_project.tcl]
	}
}

set SYNTH_CONST [file join $currentDir constraints cl_synth_user.xdc]
set IMPL_CONST [file join $currentDir constraints cl_pnr_user.xdc]

set VERIF [file join $currentDir verif test_cl.sv]

import_files -fileset constrs_1 -force $SYNTH_CONST
import_files -fileset constrs_1 -force $IMPL_CONST

set_property PROCESSING_ORDER LATE [get_files */cl_pnr_user.xdc]
set_property USED_IN {implementation} [get_files */cl_pnr_user.xdc]

set_property is_enabled false [get_files */cl_pnr_user.xdc]
set ::env(PNR_USER) [get_files */cl_pnr_user.xdc]			

import_files -fileset sim_1 -norecurse $VERIF
update_compile_order -fileset sim_1

set DELAYEDEXAMPLE [file join $currentDir [file tail $currentDir].tcl]
set DELAYEDEXAMPLE "source $DELAYEDEXAMPLE -notrace"

# if parent is not magic_button, exec DELAYEDEXAMPLE (SED flow)
if {[info exist _nsvars::script_dir] eq 0} {
	puts "INFO: \[[file dirname $currentFile]\] $DELAYEDEXAMPLE"
	{*}$DELAYEDEXAMPLE
	unset DELAYEDEXAMPLE
}


