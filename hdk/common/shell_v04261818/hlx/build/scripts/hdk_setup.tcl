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



# TCL equivalent for hdk_setup.sh - Enables use of F1 on Windows to develop (implement to .tar) and then use AMI to create AFI

#package require TclCurl


set script_dir [file normalize [file dirname [info script]]]
#set script_dir [string map {"-dontpull" ""} $script_dir]
set script_name [file tail [info script]]
set full_script [file normalize [info script]]

set debug 0

# This function checks if an environment module exists
# Returns 0 if it exists, and returns 1 if it doesn't
#proc does_module_exist {}
# USE [file exist $::env()] instead

set info_incr 0
proc info_msg { theMsg } {
    upvar 1 info_incr info_cnt
    send_msg_id "hdk_setup 10-[incr info_cnt]" "INFO" $theMsg
}

set debug_incr 0
proc debug_msg { theMsg } {
    upvar 1 debug_incr debug_cnt
    send_msg_id "hdk_setup 9-[incr debug_cnt]" "INFO" "DEBUG: $theMsg"
}
set warn_incr 0
proc warn_msg { theMsg } {
    upvar 1 warn_incr warn_cnt
    send_msg_id "hdk_setup 1-[incr warn_cnt]" "WARNING" $theMsg
}
set crit_incr 0
proc crit_msg { theMsg } {
    upvar 1 crit_incr crit_cnt
    send_msg_id "hdk_setup 1-[incr crit_cnt]" "CRITICAL WARNING" $theMsg
}
set error_incr 0
proc err_msg { theMsg } {
    upvar 1 error_incr error_cnt
    send_msg_id "hdk_setup 0-[incr error_cnt]" "ERROR" $theMsg
}

proc hdk_setup_usage { } {
    upvar 1 full_script full_script
    puts "USAGE: source $full_script \[-d|-debug\] \[-h|-help\]"
}
proc hdk_setup_help { } {
    upvar 1 script_name script_name
    info_msg "$script_name"
    info_msg " "
    info_msg "Sets up the environment for AWS FPGA HDK tools."
    info_msg " "
    info_msg "hdk_setup.tcl script will:"
#	info_msg "  (1) Check if Xilinx Vivado is installed,"
    info_msg "  (2) Set up key environment variables HDK_*, and"
    info_msg "  (3) Download/update the HDK shell's checkpoint"
#	info_msg "  (4) Prepare DRAM controller and PCIe IP modules if they are not already available in your directory."
    echo " "
    usage
}

# Add & Call hdk_setup_proc
proc hdk_setup_proc {{args ""}} {
# Use parent's workspace for key variables in the main script
    upvar 1 env env

# This script is only for Windows.  All others should use hdk_setup.sh
    if {[info exist ::env(OS)] eq 0} {
        info_msg "OS Environment variable not set, assuming Linux"
        set ::env(OS) "linux"
    }
    if {[string match "*windows*" [string tolower $::env(OS)]] eq 0} {
        err_msg "OS does not appear to be Windows.  Please use hdk_setup.sh in bash.  Exiting hdk_setup_proc. ($::env(OS))"
    }



    upvar 1 debug debug
    upvar 1 script_dir script_dir

# Process command line args
    while {[llength $args]} {
    #created with regexp_switch_arguments.tcl
    #regexp_switch_arguments [list -debug -help]
        set name [string tolower [lshift args]]
        switch -regexp -- $name {
            -debug -
            {^-d(e(b(u(g?)?)?)?)?$} {
                set debug 1
            }
            -help -
            {^-h(e(l(p?)?)?)?$} {
                hdk_setup_help
                return 0
            }
            default {
                err_msg "Invalid option: '$name'"
                return 1
            }
        }
    }

# Make sure that AWS_FPGA_REPO_DIR is set to the location of the hdk_setup.sh (not this file's directory).
    set script_dir [file normalize [file join $script_dir .. .. .. .. .. .. ]]
    if {[info exist ::env(AWS_FPGA_REPO_DIR)] eq 0} {
        debug_msg "AWS_FPGA_REPO_DIR not set so setting to $script_dir"
        set ::env(AWS_FPGA_REPO_DIR) $script_dir
    } elseif {[string match $::env(AWS_FPGA_REPO_DIR) $script_dir] eq 0} {
        info_msg "Changing AWS_FPGA_REPO_DIR from $::env(AWS_FPGA_REPO_DIR) to $script_dir"
        set ::env(AWS_FPGA_REPO_DIR) $script_dir
    } else {
        debug_msg "AWS_FPGA_REPO_DIR=$script_dir"
    }
    set AWS_FPGA_REPO_DIR $script_dir

#Searching for Vivado version and comparing it with the list of supported versions
    set VIVADO_VER [version -short]
    set ::env(VIVADO_VER) $VIVADO_VER

    info_msg "Using $VIVADO_VER"

    if { [::tclapp::xilinx::faasutils::make_faas::findLineInFile $AWS_FPGA_REPO_DIR/supported_vivado_versions.txt $VIVADO_VER] ne "" } {
        debug_msg "$VIVADO_VER is supported by this HDK release."
    } else {
        err_msg "$VIVADO_VER is not supported by this HDK release."
        err_msg "Supported versions are:"
        puts [::tclapp::xilinx::faasutils::make_faas::findLineInFile $AWS_FPGA_REPO_DIR/supported_vivado_versions.txt *]
        return 1
    }

    debug_msg "Vivado check succeeded"

    info_msg "Setting up environment variables"

# Clear environment variables
#unset HDK_DIR
#unset HDK_COMMON_DIR
#unset HDK_SHELL_DIR
#unset HDK_SHELL_DESIGN_DIR

    set HDK_DIR $AWS_FPGA_REPO_DIR/hdk
    set ::env(HDK_DIR) $HDK_DIR

# The next variable should not be modified and should always point to the /common directory under HDK_DIR
#export HDK_COMMON_DIR=$HDK_DIR/common
    set HDK_COMMON_DIR $HDK_DIR/common
    set ::env(HDK_COMMON_DIR) $HDK_COMMON_DIR

# Point to the latest version of AWS shell
#export HDK_SHELL_DIR=$(readlink -f $HDK_COMMON_DIR/shell_stable)
#hdk_shell_version=$(readlink $HDK_COMMON_DIR/shell_stable)
#	set hdk_shell_version in argument!
    set hdk_shell_version [::tclapp::xilinx::faasutils::make_faas::findLineInFile $HDK_COMMON_DIR/shell_stable *]
    set HDK_SHELL_DIR $HDK_COMMON_DIR/$hdk_shell_version
    if {[file exist $HDK_SHELL_DIR] eq 0} {
        err_msg "$HDK_SHELL_DIR does not exist.  Cannot set HDK_SHELL_DIR"
        return 1
    }
    set ::env(HDK_SHELL_DIR) $HDK_SHELL_DIR

# Set the common shell design dir
#export HDK_SHELL_DESIGN_DIR=$HDK_SHELL_DIR/design
    set HDK_SHELL_DESIGN_DIR $HDK_SHELL_DIR/design
    set ::env(HDK_SHELL_DESIGN_DIR) $HDK_SHELL_DESIGN_DIR

##export PATH=$(echo $PATH | sed -e 's/\(^\|:\)[^:]\+\/hdk\/common\/scripts\(:\|$\)/:/g; s/^://; s/:$//')
#	set PATH $::env(PATH)
#	set PATH_list [split $PATH ";"]
#	foreach {PATH_el} $PATH_list {
#		if {[string match "*/hdk/common/scripts*" $PATH_el] eq 0} {
#			lappend PATH_ret $PATH_el
#		}
#	}
#	set PATH [join $PATH_ret ";"]
##	set ::env(PATH) $PATH
#	set PATH $AWS_FPGA_REPO_DIR/hdk/common/scripts;$PATH


debug_msg "Done setting environment variables."

# Download correct shell DCP
    info_msg "Using HDK shell version $hdk_shell_version"
    debug_msg "Checking HDK shell's checkpoint version"
    set hdk_shell_dir $HDK_SHELL_DIR/build/checkpoints/from_aws
    set hdk_shell $hdk_shell_dir/SH_CL_BB_routed.dcp
    set hdk_shell_s3_bucket aws-fpga-hdk-resources
    set s3_hdk_shell $hdk_shell_s3_bucket/hdk/$hdk_shell_version/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
# Download the sha256
    file mkdir $hdk_shell_dir
    if {[file exist $hdk_shell_dir] eq 0} {
        err_msg "Failed to create $hdk_shell_dir"
    }

#NOT SUPPORTED, CUSTOM DOWNLOAD!
## Use curl instead of AWS CLI so that credentials aren't required.
#	set curlHandle [ ::curl::init ]
#	$curlHandle configure \
#		-url s3.amazonaws.com/$s3_hdk_shell.sha256
#		-file $hdk_shell.sha256 \
#		-proxytype https \
#		-errorbuffer errorBuffer \
#		-failonerror 1 \
#		-followlocation 1
#
#	if { [ catch { $curlHandle perform } result ] } {
#		$curlHandle cleanup
#		return -code error "$result $errorBuffer"
#	}
#	$curlHandle cleanup

# Check sha256
# NOT SUPPORTED, MANUALLY VERIFY
    if {[file exist $hdk_shell] eq 0} {
        crit_msg "SH_CL_BB_routed.dcp not found at location $hdk_shell.  Please download and update from the following location\n\thttps://s3.amazonaws.com/$s3_hdk_shell"
        file mkdir [file dirname $hdk_shell]
    } else {
        info_msg "SH_CL_BB_routed.dcp found in required location $hdk_shell"
        warn_msg "Cannot verify shell DCP is of correct version, please ensure you are up to date with \n\thttps://s3.amazonaws.com/$s3_hdk_shell"
    }


# Create DDR and PCIe IP models and patch PCIe
    set models_dir $HDK_COMMON_DIR/verif/models
    set ddr4_model_dir $models_dir/ddr4_model
    if {[file exist $ddr4_model_dir/arch_defines.v]} {
        # Models already built
        # Check to make sure they were built with this version of vivado
        if {[file exist $models_dir/.vivado_version]} {
            set models_vivado_version [::tclapp::xilinx::faasutils::make_faas::findLineInFile $models_dir/.vivado_version *]
            info_msg "DDR4 model files in $ddr4_model_dir/ were built with $models_vivado_version"
            if { [ string match $models_vivado_version $VIVADO_VER ] eq 0 } {
                info_msg "  Wrong vivado version so rebuilding with $VIVADO_VER"
            }
        } else {
            set models_vivado_version UNKNOWN
            info_msg "DDR4 model files in $ddr4_model_dir/ were built with UNKNOWN Vivado version so rebuilding."

        }
    } else {
        # Models haven't been built
        set models_vivado_version NOT_BUILT
        info_msg "DDR4 model files in $ddr4_model_dir/ do NOT exist. Running model creation step."

    }


# Prevent multiple users from building in the same directory.
    set lockfile_filename $models_dir/build.lock
    if {[file exist $lockfile_filename] eq 0} {
        if {[ string match $models_vivado_version $VIVADO_VER ] eq 0} {
            set ddr4_build_dir $AWS_FPGA_REPO_DIR/ddr4_model_build
            set ::env(ddr4_build_dir) $ddr4_build_dir
            set ::env(models_dir) $models_dir
            crit_msg "  Must rebuild DDR4 Models.  Building in $ddr4_build_dir"
            crit_msg "  This could take 5-10 minutes, please be patient!"
            file mkdir $ddr4_build_dir
            set backdir [pwd]
            # $HDK_DIR/common/verif/scripts/init.sh
            if {[file exist $HDK_DIR/common/verif/scripts/hdk_initsh.tcl] eq 0} {
                err_msg "Cannot find hdk_initsh.tcl at $HDK_DIR/common/verif/scripts/"
                return 2
            } else {
#				cd $ddr4_build_dir
#				err_msg "Verification models not built.  Please press continue and run the following commands to create the DDR4 Models \n\tsource $HDK_DIR/common/verif/scripts/hdk_initsh.tcl\n\thdk_initsh_tcl_proc $models_dir"
                err_msg "Verification models not built.  Please press continue and run the following command to create the DDR4 Models \n\tsource $HDK_DIR/common/verif/scripts/hdk_initsh.tcl"
    #RECURSIVE!			source $HDK_DIR/common/verif/scripts/hdk_initsh.tcl
#				if {[hdk_initsh_tcl_proc $models_dir] eq 2} {
#					err_msg "DDR4 model build failed."
#					err_msg "  Build dir=$ddr4_build_dir"
#					cd $backdir
#					return 2
#				}
            }
#			cd $backdir
#			info_msg "DDR4 model build passed."
#			file delete -force $ddr4_build_dir
        }
    } else {
        debug_msg "DDR4 model files exist in $ddr4_model_dir/. Skipping model creation step."
    }


# NOT SUPPORTED FOR WINDOWS

    info_msg "AWS HDK setup COMPLETE (unverified SH_CL_BB_routed.dcp)."



}

hdk_setup_proc


