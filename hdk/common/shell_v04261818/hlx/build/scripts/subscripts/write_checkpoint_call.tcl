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

if { [info exists ::env(SYNTH_DCP_OUTPUT_DIRECTORY)] eq 0} {}
if { [info exists SYNTH_DCP_OUTPUT_DIRECTORY] eq 0} {
	set SYNTH_DCP_OUTPUT_DIRECTORY [file join [pwd] "faas_results"]
}
set _procName "write_checkpoint_call"

if {[info exist _write_checkpoint_can_encrypt] eq 0} {
	set _write_checkpoint_can_encrypt 0
}



puts "Post-encrypting DCP"

puts "INFO \[write_checkpoint_call.tcl\]"

set _post_synth_dcp [file join $SYNTH_DCP_OUTPUT_DIRECTORY build checkpoints CL.post_synth.dcp]
set _post_impl_dcp [file join $SYNTH_DCP_OUTPUT_DIRECTORY build checkpoints CL.post_impl.dcp]
file mkdir [file join $SYNTH_DCP_OUTPUT_DIRECTORY build checkpoints]


puts "at level [info level]"

#report_property [current_fileset]
#report_property [current_project]
#report_property [current_run -synthesis]


#report_property [current_run]
#if {[get_property IS_SYNTHESIS [current_run]]} {puts "In Synthesis"}

if {0} {

	set synth_run [uplevel 1 [current_run -synthesis]]
#	set synth_run [get_runs [current_run -synthesis]]
	set impl_run [get_runs [current_run -implementation]]
	puts "get_runs:[get_runs]\ncurrent:[current_run]\nget_current:[get_runs [current_run]]\nsynth:$synth_run\nimpl:$impl_run"
	open_run [current_run -synthesis]
}

if {$_write_checkpoint_can_encrypt eq 0} {
	write_checkpoint -force $_post_synth_dcp
	set critWarnCode 1
	send_msg_id "$_procName 0-$critWarnCode" "CRITICAL WARNING" "Encryption for user source code has not occurred.  Please make sure your source code has been encrypted as necessary"
#	puts "CRITICAL WARNING: $critWarnMessage"
#	set critWarnMessage "\[$_procName 0-$critWarnCode\] Encryption for user source code has not occurred.  Please make sure your source code has been encrypted as necessary"
#	puts "CRITICAL WARNING: $critWarnMessage"
} else {
	write_checkpoint -force -encrypt $keyfile $_post_synth_dcp
}

puts "Wrote chckpoint $_post_synth_dcp"


