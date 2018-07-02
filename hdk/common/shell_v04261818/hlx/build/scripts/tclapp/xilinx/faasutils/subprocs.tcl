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

package require Vivado 1.2015.1

#set _THISNAMESPACE "::tclapp::xilinx::designutils"
if {[info exist _THISNAMESPACE] eq 0} {
	set _THISNAMESPACE "aws"
}
if {[info exist _THISTOPSPACE] eq 0} {
	set _THISTOPSPACE  "encrypt_synth_files"
}

################################################################################
#  SUBPROCS
################################################################################
proc [set _THISNAMESPACE]::[set _THISTOPSPACE]::dputs {{dbgToken ""} {putString ""} {nullify "0"}} {
  # Summary : Print debug information onto the TCL console based on token level
  # Argument Usage:
  # Return Value:
  # Categories:

	if {$nullify eq 0} {
		if {$dbgToken ne "0"} {
			puts $putString
		}
	}
}

proc [set _THISNAMESPACE]::[set _THISTOPSPACE]::wsplit {{theString ""} {theWord ""}} {
	# like split, but splits on the whole "word" instead of elements in word
	set theWordLength [llength [split $theWord ""]]
	set theLoc [string first $theWord $theString]
	set theLister ""
	while {$theLoc ne -1} {
		set theStringExp [split $theString ""]
		set theFront [join [lrange $theStringExp 0 [expr $theLoc - 1]] ""]
		set theBack  [join [lrange $theStringExp [expr $theLoc + $theWordLength] end] ""]
		lappend theLister $theFront
		set theString $theBack

#		puts "$theLoc.$theString.$theFront.$theBack.$theLister."
		set theLoc [string first $theWord $theString]
	}
	lappend theLister $theString
	return $theLister
}

proc [set _THISNAMESPACE]::[set _THISTOPSPACE]::putsf {arg1 arg2} {
  # Summary : Optionally puts text to file
  # Argument Usage:
  # Return Value:
  # Categories:

	if {$arg1 eq 1} {
		puts $arg2
	} elseif {$arg1 ne 0} {
		puts $arg1 $arg2
	}
}
proc [set _THISNAMESPACE]::[set _THISTOPSPACE]::lshift {inputlist} {
  # Summary : Shift off arguments from a list
  # Argument Usage: A list
  # Return Value: First element in the list
  # Categories:

  upvar $inputlist argv
  set arg  [lindex $argv 0]
  set argv [lrange $argv 1 end]
  #puts "shifted $arg"
  return $arg
}
proc [set _THISNAMESPACE]::[set _THISTOPSPACE]::lunshift {inputlist inputelement} {
  # Summary : Shift on arguments from a list
  # Argument Usage: A list, an element
  # Return Value: A larger list
  # Categories:

  upvar $inputlist argv
  set argv [linsert $argv 0 $inputelement]
  return $argv
}

proc [set _THISNAMESPACE]::[set _THISTOPSPACE]::findLineInFile {thefile {thestring ""} {exactloc "any"} } {
  # Summary : Read a file and returns line(s) that match thestring
  # Argument Usage: A file, a string, wildcard settings
  # Return Value: A list
  # Categories:

	set debugMode 0

	if {[string tolower $exactloc] eq "front"} {
		set thestring "$thestring*"
	} elseif {[string tolower $exactloc] eq "back"} {
		set thestring "*$thestring"
	} elseif {[string tolower $exactloc] eq "exact"} {
		set thestring "$thestring"
	} elseif {[string tolower $exactloc] eq "any"} {
		set thestring "*$thestring*"
	} else {
		puts "invalid use of findLineInFile <thefile> <thestring> \{front back exact any\}"
	}
	dputs $debugMode "Looking for string $thestring (findLineInFile)"

	set foundLine ""
	set openThisFile [open $thefile r]
	while { [gets $openThisFile line] >= 0 } {
		dputs $debugMode "uncaptured line $line"
		if {[string match $thestring $line]} {
			lappend foundLine $line
			dputs $debugMode "captured line $line"
		}
	}
	close $openThisFile
	return $foundLine
}


