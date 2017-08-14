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

proc impl_step {phase top {options none} {directive none} {pre none} {post none} } {
   upvar  bitDir    bitDir
   upvar  implDir   implDir
   upvar  rptDir    rptDir
   upvar  timestamp timestamp

   if {[string match $phase "write_bitstream"]} {
      set stepDir $bitDir
   } else {
      set stepDir $implDir
   }

   #Set value > 1 to get DCPs and reports for all phases
   set verbose 1

   #Make sure $phase is valid and set checkpoint in case no design is open
   if {[string match $phase "opt_design"]} {
      set checkpoint1 "$implDir/${timestamp}.post_link_design.dcp"
   } elseif {[string match $phase "place_design"]} {
      set checkpoint1 "$implDir/${timestamp}.post_opt_design.dcp"
   } elseif {[string match $phase "phys_opt_design"]} {
      set checkpoint1 "$implDir/${timestamp}.post_place_design.dcp"
   } elseif {[string match $phase "route_design"]} {
      set checkpoint1 "$implDir/${timestamp}.post_phys_opt_design.dcp"
      set checkpoint2 "$implDir/${timestamp}.post_place_design.dcp"
   } elseif {[string match $phase "route_phys_opt_design"]} {
      set checkpoint1 "$implDir/${timestamp}.post_route_design.dcp"
   } elseif {[string match $phase "write_bitstream"]} {
      set checkpoint1 "$implDir/${timestamp}.post_route_phys_opt_design.dcp"
      set checkpoint2 "$implDir/${timestamp}.post_route_design.dcp"
   } else {
      set errMsg "\nERROR: Value $phase is not a recognized step of implementation. Valid values are:\n\topt_design\n\tplace_design\n\tphys_opt_design\n\troute_design\n\troute_phys_opt_design\n\twrite_bitstream\n"
      error $errMsg
   }
   #If no design is open
   if { [catch {current_instance} errMsg]} {
      puts "\tNo open design" 
      if {[info exists checkpoint1] || [info exists checkpoint2]} {
         if {[file exists $checkpoint1]} {
            puts "\tOpening checkpoint $checkpoint1 for $timestamp"
            open_checkpoint $checkpoint1
         } elseif {[file exists $checkpoint2]} {
            puts "\tOpening checkpoint $checkpoint2 for $timestamp"
            open_checkpoint $checkpoint2
         } else {
            set errMsg "\nERROR: Checkpoint required for step $phase not found. Rerun necessary previous steps first."
            error $errMsg
         }
      } else {
        set errMsg "\nERROR: No checkpoint defined."
        error $errMsg
      }
   }
  
   #Setup phase-specific settings.
   if {[string match $phase "write_bitstream"]} {
      set impl_step "$phase -force -file $bitDir/$timestamp"
   } elseif {[string match $phase "route_phys_opt_design"]} {
      set impl_step "phys_opt_design"
   } else {
      set impl_step $phase
   }

   #Run any specified pre-phase scripts
   if {![string match $pre "none"] && ![string match $pre ""] } {
      foreach script $pre {
         if {[file exists $script]} {
            puts "\tRunning pre-$phase script $script"
            source $script
         } else {
            set errMsg "\nERROR: Script $script specified for pre-${phase} does not exist"
            error $errMsg
         }
      }
   }
 
   #Append options to command
   if {[string match $options "none"]==0 && [string match $options ""]==0} {
      append impl_step " $options"
   }

   #Append directives to command
   if {[string match $directive "none"]==0 && [string match $directive ""]==0} {
      append impl_step " -directive $directive"
   }

   #Run the specified Implementation phase
   set start_time [clock seconds]
   puts "\n\t################################"
   puts "\t$phase start time: \[[clock format $start_time -format {%a %b %d %H:%M:%S %Y}]\]"
   puts "\tCOMMAND: $impl_step"
   if {[catch $impl_step $errMsg]} {
      if {[string match $phase "route_design"]} {
         puts "\tERROR: $phase failed. Writing $phase checkpoint for debug\n\t$stepDir/${timestamp}.post_${phase}_error.dcp"
         write_checkpoint -force $stepDir/${timestamp}.post_${phase}_error.dcp
      }
      append errMsg "\nERROR: $phase failed."
      error $errMsg
   }
   if {![string match $phase "write_bitstream"]} {
      set SLACK [get_property SLACK [get_timing_paths]]
      puts "\tCompleted: $phase (WNS=$SLACK)"
   } else {
      puts "\tCompleted: $phase"
   }
   puts "\t################################"

   #Run any specified post-phase scripts
   if {![string match $post "none"] && ![string match $post ""] } {
      foreach script $post {
         if {[file exists $script]} {
            puts "\tRunning post-$phase script $script"
            source $script
         } else {
            set errMsg "\nERROR: Script $script specified for post-${phase} does not exist"
            error $errMsg
         }
      }
   }
      
   #Write out checkpoint for successfully completed phase
   if {($verbose > 1  || [string match $phase "opt_design"] || [string match $phase "route_design"] || [string match $phase "route_phys_opt_design"]) && ![string match $phase "write_bitstream"]} {
      set start_time [clock seconds]
      puts "\tWriting $phase checkpoint: $stepDir/${timestamp}.post_$phase.dcp \[[clock format $start_time -format {%a %b %d %H:%M:%S %Y}]\]\n"
      write_checkpoint -force $stepDir/${timestamp}.post_$phase.dcp
      report_timing -cell CL -delay_type max -max_paths 10 -sort_by group -input_pins -file  $rptDir/${timestamp}.post${phase}_timing_max.rpt
      report_timing -cell CL -delay_type min -max_paths 10 -sort_by group -input_pins -file  $rptDir/${timestamp}.post${phase}_timing_min.rpt
   }

   #Write out additional reports controled by verbose level
   if {($verbose > 1 || [string match $phase "route_design"] || [string match $phase "route_phys_opt_design"]) && ![string match $phase "write_bitstream"]} {
      puts "\tGenerating report files"
      report_utilization -pblock [get_pblocks pblock_CL] -file $rptDir/${timestamp}.utilization_${phase}.rpt
      report_timing_summary -cell CL -file $rptDir/${timestamp}.timing_summary_$phase.rpt
   }

   if {[string match $phase "route_design"]} {
      puts "\tGenerating route_status report"
      report_route_status -file $rptDir/${timestamp}.route_status.rpt
   }
}

