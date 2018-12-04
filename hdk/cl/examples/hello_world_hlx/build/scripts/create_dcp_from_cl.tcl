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
if { [catch {aws::make_ipi -examples hello_world}] == 1 } {
  set custom_err_hlx "**************************************************************************************************************\n"
  append custom_err_hlx "* ERROR: \[HLx Setup\] $::env(HDK_SHELL_DIR)/hlx/hlx_setup.tcl is not sourced\n"
  append custom_err_hlx "** Please add the command \"source $::env(HDK_SHELL_DIR)/hlx/hlx_setup.tcl\" in your .Vivado_init.tcl\n"
  append custom_err_hlx "*** For more information, please refer to https://github.com/aws/aws-fpga/hdk/docs/IPI_GUI_Vivado_Setup.md \n"
  append custom_err_hlx "**************************************************************************************************************\n"
  error $custom_err_hlx
}
update_compile_order -fileset sources_1
update_compile_order -fileset sim_1
set_property USED_IN_SIMULATION 0 [get_files -regexp -of_objects [get_files -regexp -of_objects [get_filesets sources_1] {.*bd_.*\.bd}] {.*\.bmm}]
set_property USED_IN_IMPLEMENTATION 0 [get_files -regexp -of_objects [get_files -regexp -of_objects [get_filesets sim_1] {.*bd_.*\.bd}] {.*\.bmm}]
set_property SCOPED_TO_CELLS {card/fpga/sh/DDR4_3/inst/u_ddr4_mem_intfc/u_ddr_cal_riu/mcs0/inst/microblaze_I} [get_files -regexp -of_objects [get_filesets sim_1] {.*data/mb_bootloop_le\.elf}]

#################################################
## Run synthesis and implementation
#################################################
if {[string compare $gui "0"] == 0} {
  launch_runs impl_1
  wait_on_run impl_1

  if {[string compare $notify_via_sns "1"] == 0} {
    puts "AWS FPGA: ([clock format [clock seconds] -format %T]) - Calling notification script to send e-mail to $env(EMAIL)";
    exec $env(AWS_FPGA_REPO_DIR)/shared/bin/scripts/notify_via_sns.py
  }
}
