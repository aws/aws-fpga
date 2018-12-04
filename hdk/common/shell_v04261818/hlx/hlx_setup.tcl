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

# add checks for completeness
# add call for aws namespace (elmo_me.tcl)
#	need to redirect aws:: to ...:: for below work (upvar?)



# Where is this script?
set awsip_script_dir [file dirname [info script]]

# Set the root locations for git and tcl repositories (change default below)
set awsip_gitloc $awsip_script_dir
set awsip_tclloc [file normalize [file join $awsip_script_dir build scripts tclapp]]

# Initialize the TCL App(s) (not needed if installed as a TCL app)
source [file join $awsip_tclloc xilinx faasutils make_faas.tcl]
source [file join $awsip_gitloc build scripts aws_make.tcl]


# variables in the aws namespace
set aws::make_faas::public::bd_faas_root $awsip_gitloc

set aws::make_faas::public::bd_faas_build_directory [file join $awsip_script_dir build]

set aws::make_faas::public::bd_faas_design_directory [file join $awsip_script_dir design]

set aws::make_faas::public::bd_faas_examples_directory [file normalize [file join $awsip_script_dir hlx_examples build IPI ]]


# Environment variable used by TCL app to find the bd_faas_initscript
set aws::make_faas::public::bd_faas_initscript [file join $aws::make_faas::public::bd_faas_build_directory scripts aws_bd_faas_initscript.tcl]
set ::env(FAAS_HOOK_TCL) $::aws::make_faas::public::bd_faas_initscript


