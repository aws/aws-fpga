# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
# =============================================================================


###############################################################################
# Common functions
###############################################################################

######################################
# print:
#   Print a message
######################################
proc print {message} {
    set prefix "\nAWS FPGA: ([clock format [clock seconds] -format %T]): "
    append output $prefix $message "\n"
    puts $output
}

######################################
# check_timing_path:
#   Check and report negative slack timing path
######################################
proc check_timing_path { {verbose 1} } {

  set setupPaths [get_timing_paths -max_paths 1 -slack_lesser_than 0 -setup]
  set holdPaths  [get_timing_paths -max_paths 1 -slack_lesser_than 0 -hold]

  if {$verbose>0} {
    print "Checking the negative slack path of the existing design"
  }

  if {[llength $setupPaths] == 0 && [llength $holdPaths] == 0} {
    if {$verbose>0} {
      print "SUCCESS: Design has no negative slack path"
    }
    return 0
  } else {
    if {$verbose>0} {
      print "CRITICAL WARNING: Found $setupPaths negative setup slack paths and $holdPaths negative hold slack hold paths"
    }
    return 1
  }
}

######################################
# create_dir:
#   Create a directory at $path/$name
######################################
proc create_dir {name path {verbose 0}} {

    # Better to use absolute path
    set cur [pwd]
    # Check if the $path exists
    if {![file isdirectory $path]} {
        error "$path doesn't exist"
    }
    cd $path
    set path_abs [pwd]

    cd $cur
    # Check and create the directory if not exists
    if {![file isdirectory $path_abs/$name]} {
        file mkdir $path_abs/$name
        if {$verbose>0} {
            print "Creating new folder $path_abs/$name"
        }
    } elseif {$verbose>0} {
        print "Found existing folder $path_abs/$name. Folder creation skipped"
    }
    return $path_abs/$name
}

######################################
# display_proj:
#   Display project's building parameters
######################################
proc display_proj {} {
    global VIVADO_TOOL_VERSION
    global CL
    global SHELL_MODE
    global BUILD_FLOW
    global PLACE_DIRECT
    global PHY_OPT_DIRECT
    global ROUTE_DIRECT
    global TAG
    global clock_recipe_a
    global clock_recipe_b
    global clock_recipe_c
    global clock_recipe_hbm


    set rpt "
    ==================================================
    Running CL builds w/ updated build tag
    ==================================================
    vivado_tool      : $VIVADO_TOOL_VERSION
    cl               : $CL
    mode             : $SHELL_MODE
    clock_recipe_a   : $clock_recipe_a
    clock_recipe_b   : $clock_recipe_b
    clock_recipe_c   : $clock_recipe_c
    clock_recipe_hbm : $clock_recipe_hbm
    flow             : $BUILD_FLOW
    place_direct     : $PLACE_DIRECT
    phy_opt_direct   : $PHY_OPT_DIRECT
    route_direct     : $ROUTE_DIRECT
    build_tag        : $TAG
    ==================================================
    "
    puts "$rpt"
}


###############################################################################
#  Parsing build variables
###############################################################################
set PLACE_DIRECT     [lindex $argv 0]
set PHY_OPT_DIRECT   [lindex $argv 1]
set ROUTE_DIRECT     [lindex $argv 2]
set clock_recipe_a   [lindex $argv 3]
set clock_recipe_b   [lindex $argv 4]
set clock_recipe_c   [lindex $argv 5]
set clock_recipe_hbm [lindex $argv 6]


###############################################################################
# Setup Project
###############################################################################
# Project attributes
set DEVICE_TYPE "xcvu47p-fsvh2892-2-e"


if { [info exists ::env(BUILD_FLOW)] } {
  set BUILD_FLOW $::env(BUILD_FLOW)
} else {
  set BUILD_FLOW "BuildAll"
}

if { [info exists ::env(CL)] } {
  set CL $::env(CL)
} else {
  set CL "cl_dram_hbm_dma"
}

if { [info exists ::env(SHELL_MODE)] } {
  set SHELL_MODE $::env(SHELL_MODE)
} else {
  set SHELL_MODE "xdma_shell"
}

if { [info exists ::env(BUILD_TAG)] } {
  set TAG $::env(BUILD_TAG)
} else {
  set TAG "00_00_0000-999999"
}

if { [info exists ::env(HDK_SHELL_DIR)] } {
    set HDK_SHELL_DIR $::env(HDK_SHELL_DIR)
} else {
    print "ERROR: HDK_SHELL_DIR not set. Please run hdk_setup.sh to set required env variables."
    exit
}

if { [info exists ::env(HDK_SHELL_DESIGN_DIR)] } {
    set HDK_SHELL_DESIGN_DIR $::env(HDK_SHELL_DESIGN_DIR)
} else {
    print "ERROR: HDK_SHELL_DESIGN_DIR not set. Please run hdk_setup.sh to set required env variables."
    exit
}

if { [info exists ::env(HDK_COMMON_DIR)] } {
    set HDK_COMMON_DIR $::env(HDK_COMMON_DIR)
} else {
    print "ERROR: HDK_COMMON_DIR not set. Please run hdk_setup.sh to set required env variables."
    exit
}

if { [info exists ::env(HDK_IP_SRC_DIR)] } {
    set HDK_IP_SRC_DIR $::env(HDK_IP_SRC_DIR)
} else {
    print "ERROR: HDK_IP_SRC_DIR not set. Please run hdk_setup.sh to set required env variables."
    exit
}

if { [info exists ::env(HDK_BD_SRC_DIR)] } {
    set HDK_BD_SRC_DIR $::env(HDK_BD_SRC_DIR)
} else {
    print "ERROR: HDK_BD_SRC_DIR not set. Please run hdk_setup.sh to set required env variables."
    exit
}

if { [info exists ::env(HDK_BD_GEN_DIR)] } {
    set HDK_BD_GEN_DIR $::env(HDK_BD_GEN_DIR)
} else {
    print "ERROR: HDK_BD_GEN_DIR not set. Please run hdk_setup.sh to set required env variables."
    exit
}

if { [info exists ::env(CL_DIR)] } {
    set CL_DIR $::env(CL_DIR)
} else {
    print "ERROR: CL_DIR not set. Please run hdk_setup.sh to set required env variables."
    exit
}

if { [info exists ::env(VIVADO_TOOL_VERSION)] } {
    set VIVADO_TOOL_VERSION $::env(VIVADO_TOOL_VERSION)
} else {
    print "ERROR: VIVADO_TOOL_VERSION not set. Please run hdk_setup.sh to set required env variables."
    exit
}


###############################################################################
# Implementation Flow
###############################################################################
display_proj

set scripts_dir [pwd]
set build_dir [file dirname $scripts_dir]

create_dir "reports"              $build_dir
create_dir "checkpoints"          $build_dir
create_dir "src_post_encryption"  $build_dir

# Setup CL build sub-directories
set design_dir       "${CL_DIR}/design"
set constraints_dir  "${build_dir}/constraints"
set reports_dir      "${build_dir}/reports"
set checkpoints_dir  "${build_dir}/checkpoints"
set reports_dir      "${build_dir}/reports"
set src_post_enc_dir "${build_dir}/src_post_encryption"

cd $scripts_dir

#
# Create clock constraints file based on clock recipes
#
print "Generating clock contraints for CL source clocks"
source $HDK_SHELL_DIR/build/scripts/aws_gen_clk_constraints.tcl

#
# Add source code
#
print "Encrypting CL source code"
source encrypt.tcl

#
# Build
#
switch $BUILD_FLOW {
  "SynthCL" {
    source ${scripts_dir}/synth_${CL}.tcl
  }

  "ImplCL" {
    source ${scripts_dir}/build_level_1_cl.tcl
  }

  default {
    source ${scripts_dir}/synth_${CL}.tcl
    source ${scripts_dir}/build_level_1_cl.tcl
  }
}
