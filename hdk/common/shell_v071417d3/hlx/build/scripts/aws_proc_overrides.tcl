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

proc rethrow_error { eid } {
	set err_is [lindex [tclapp::xilinx::faasutils::make_faas::wsplit $eid "\n"] 0]
	set severity_is [lindex [split $err_is ":"] 0]
	set number_is [lindex [split [lindex [split $err_is "\["] 1] "\]"] 0]
	set data_is [lindex [split $err_is "\]"] 1]
	puts "rethrowing $err_is"
	send_msg_id $number_is $severity_is $data_is
}



puts "*Modifying Vivado command: launch_runs (aws_proc_overrides.tcl)"
puts "script dir $aws::make_faas::_nsvars::script_dir"
if {[info commands launch_runs_faas] eq ""} {
	proc my_launch_runs {args} {

		puts "Running pre-hook on launch_runs"
		if { [ catch {
			source $aws::make_faas::_nsvars::script_dir/subscripts/launch_runs_pre.tcl -notrace
		} eid ] } {
			if {[string match "ERROR*" $eid]} {
				rethrow_error $eid
			} else {
				send_msg_id "aws_proc_overrides 0-2" ERROR "Script launch_runs_pre.tcl threw error: $eid"
			}
			send_msg_id "aws_proc_overrides 0-1" ERROR "An error occurred while sourcing $aws::make_faas::_nsvars::script_dir/subscripts/launch_runs_pre.tcl\n\tplease check the tcl console\n$eid"
		}
		puts "Launching runs with argument(s) $args"
		launch_runs_faas {*}$args

	}
	rename launch_runs launch_runs_faas 
	rename my_launch_runs launch_runs 
}



#also create_run (set faas_has_new_create_run)

if {[info commands create_run_faas] eq ""} {
	proc my_create_run {args} {

		upvar 1 env env

		puts "Creating runs with argument(s) $args"
		create_run_faas {*}$args

		puts "Running post-hook on create_run"
		if { [ catch {

			if {[info exist ::env(FAAS_CL_DIR)]} {
puts "Unsetting FAAS_CL_DIR environment variable, this will force an update to run settings when runs are launched"
				unset ::env(FAAS_CL_DIR)
			}

#			if {[get_files -quiet cl.bd] ne ""} {
#				aws::make_ipi
#			} else {
#				aws::make_rtl
#			}


		} eid ] } {
			if {[string match "ERROR*" $eid]} {
				rethrow_error $eid
			} else {
				send_msg_id "aws_proc_overrides 0-2" ERROR "Script launch_runs_pre.tcl threw error: $eid"
			}
			send_msg_id "aws_proc_overrides 0-1" ERROR "An error occurred while sourcing $aws::make_faas::_nsvars::script_dir/subscripts/launch_runs_pre.tcl\n\tplease check the tcl console\n$eid"
		}

	}
	rename create_run create_run_faas 
	rename my_create_run create_run 
}

## and current_run (check for faas_has_new_run)
#if {[info commands current_run_faas] eq ""} {
#	proc my_current_run {args} {

#		puts "Creating runs with argument(s) $args"
#		current_run_faas {*}$args

#		upvar 1 faas_has_new_create_run faas_has_new_create_run
#		if {[info exist faas_has_new_create_run]} {
#			set faas_has_new_create_run 0
##			unset faas_has_new_create_run 		
#			if {$faas_has_new_create_run} {
#				puts "Running post-hook on current_run"
#				if { [ catch {

#					if {[get_files -quiet cl.bd] ne ""} {
#						aws::make_ipi
#					} else {
#						aws::make_rtl
#					}


#				} eid ] } {
#					if {[string match "ERROR*" $eid]} {
#						rethrow_error $eid
#					} else {
#						send_msg_id "aws_proc_overrides 0-2" ERROR "Script launch_runs_pre.tcl threw error: $eid"
#					}
#					send_msg_id "aws_proc_overrides 0-1" ERROR "An error occurred while sourcing $aws::make_faas::_nsvars::script_dir/subscripts/launch_runs_pre.tcl\n\tplease check the tcl console\n$eid"
#				}
#			}
#		} else {
#puts "so sad"
#		}


#puts "resource:\n\tsource $aws::make_faas::_nsvars::script_dir/aws_proc_overrides.tcl"

#	}
#	rename current_run current_run_faas 
#	rename my_current_run current_run 
#}

