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

#################################################
## Command-line Arguments
#################################################
set timestamp      [lindex $argv 0]
set notify_via_sns [lindex $argv 1]
set gui            [lindex $argv 2]

if {[string compare $notify_via_sns "1"] == 0} {
  if {![info exists env(EMAIL)]} {
    puts "AWS FPGA: ([clock format [clock seconds] -format %T]) EMAIL variable empty!  Completition notification will *not* be sent!";
    set notify_via_sns 0;
  } else {
    puts "AWS FPGA: ([clock format [clock seconds] -format %T]) EMAIL address for completion notification set to $env(EMAIL).";
  }
}

#################################################
## Create BD (Block Design) of example Hello World design
#################################################
if { [catch {aws::make_ipi -examples cl_hello_world_ref}] == 1 } {
  set custom_err_hlx "**************************************************************************************************************\n"
  append custom_err_hlx "* ERROR: \[HLx Setup\] $::env(HDK_SHELL_DIR)/hlx/hlx_setup.tcl is not sourced\n"
  append custom_err_hlx "** Please add the command \"source $::env(HDK_SHELL_DIR)/hlx/hlx_setup.tcl\" in your .Vivado_init.tcl\n"
  append custom_err_hlx "*** For more information, please refer to https://github.com/aws/aws-fpga/hdk/docs/IPI_GUI_Vivado_Setup.md \n"
  append custom_err_hlx "**************************************************************************************************************\n"
  error $custom_err_hlx
}
update_compile_order -fileset sources_1
update_compile_order -fileset sim_1

#################################################
## Run synthesis and implementation
#################################################
if {[string compare $gui "0"] == 0} {
  launch_runs impl_1
  wait_on_run impl_1

  if {[string compare $notify_via_sns "1"] == 0} {
    puts "AWS FPGA: ([clock format [clock seconds] -format %T]) - Calling notification script to send e-mail to $env(EMAIL)";
    exec $env(HDK_COMMON_DIR)/scripts/notify_via_sns.py
  }
}
