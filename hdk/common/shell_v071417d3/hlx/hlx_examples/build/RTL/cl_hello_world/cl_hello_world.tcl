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

################################################################
# This is a generated script based on design: cl
#
# Though there are limitations about the generated script,
# the main purpose of this utility is to make learning
# IP Integrator Tcl commands easier.
################################################################

namespace eval _tcl {
proc get_script_folder {} {
   set script_path [file normalize [info script]]
   set script_folder [file dirname $script_path]
   return $script_folder
}
}
variable script_folder
set script_folder [_tcl::get_script_folder]

################################################################
# Check if script is running in correct Vivado version.
################################################################
set scripts_vivado_version 2017.1
set current_vivado_version [version -short]

if { [string first $scripts_vivado_version $current_vivado_version] == -1 } {
   puts ""
   catch {common::send_msg_id "BD_TCL-109" "ERROR" "This script was generated using Vivado <$scripts_vivado_version> and is being run in <$current_vivado_version> of Vivado. Please run the script in Vivado <$scripts_vivado_version> then open the design in Vivado <$current_vivado_version>. Upgrade the design by running \"Tools => Report => Report IP Status...\", then run write_bd_tcl to create an updated script."}

   return 1
}

set PWD_DIR $::env(PWD)
set CL_DESIGN_DIR "${PWD_DIR}/../cl_hello_world/design"
set CL_COMMON_DIR "${PWD_DIR}/../common/design"
set CL_CONST_DIR "${PWD_DIR}/../cl_hello_world/build/constraints"
set CL_VERIF_DIR "${PWD_DIR}/../cl_hello_world/verif/tests"


read_verilog -sv [glob ${CL_DESIGN_DIR}/*.?v]
read_verilog -sv [glob ${CL_COMMON_DIR}/*.vh]

add_files -fileset constrs_1 -norecurse  ${CL_CONST_DIR}/cl_synth_user.xdc
add_files -fileset constrs_1 -norecurse  ${CL_CONST_DIR}/cl_pnr_user.xdc
add_files -fileset constrs_1 -norecurse  $::env(HDK_SHELL_DIR)/build/constraints/cl_synth_aws.xdc			

set_property PROCESSING_ORDER LATE [get_files */cl_pnr_user.xdc]
set_property USED_IN {implementation} [get_files */cl_pnr_user.xdc]

set_property is_enabled false [get_files */cl_pnr_user.xdc]
set ::env(PNR_USER) [get_files */cl_pnr_user.xdc]			


add_files -fileset sim_1 -norecurse ${CL_VERIF_DIR}/test_null.sv
add_files -fileset sim_1 -norecurse ${CL_VERIF_DIR}/test_gl_cntr.sv
add_files -fileset sim_1 -norecurse ${CL_VERIF_DIR}/test_hello_world.sv

update_compile_order -fileset sim_1

set_property verilog_define {CL_NAME=cl_hello_world TEST_NAME=test_hello_world} [get_filesets sim_1]
