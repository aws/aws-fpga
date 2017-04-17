proc impl_step {phase top {options none} {directive none} {pre none} } {
   upvar  bitDir bitDir
   upvar  implDir implDir
   upvar  rptDir rptDir

   #Set value > 1 to get reports for all phases
   set verbose 1

   #Make sure $phase is valid and set checkpoint in case no design is open
   if {[string match $phase "opt_design"]} {
      set checkpoint1 "$implDir/${top}.post_link_design.dcp"
   } elseif {[string match $phase "place_design"]} {
      set checkpoint1 "$implDir/${top}.post_opt_design.dcp"
   } elseif {[string match $phase "phys_opt_design"]} {
      set checkpoint1 "$implDir/${top}.post_place_design.dcp"
   } elseif {[string match $phase "route_design"]} {
      set checkpoint1 "$implDir/${top}.post_phys_opt_design.dcp"
      set checkpoint2 "$implDir/${top}.post_place_design.dcp"
   } elseif {[string match $phase "route_phys_opt_design"]} {
      set checkpoint1 "$implDir/${top}.post_route_design.dcp"
   } elseif {[string match $phase "write_bitstream"]} {
      set checkpoint1 "$implDir/${top}.post_route_phys_opt_design.dcp"
      set checkpoint2 "$implDir/${top}.post_route_design.dcp"
   } else {
      set errMsg "\nERROR: Value $phase is not a recognized step of implementation. Valid values are:\n\topt_design\n\tplace_design\n\tphys_opt_design\n\troute_design\n\troute_phys_opt_design\n\twrite_bitstream\n"
      error $errMsg
   }
   #If no design is open
   if { [catch {current_instance > $implDir/temp.log} errMsg]} {
      puts "\tNo open design" 
      if {[info exists checkpoint1] || [info exists checkpoint2]} {
         if {[file exists $checkpoint1]} {
            puts "\tOpening checkpoint $checkpoint1 for $top"
            open_checkpoint $checkpoint1 > $implDir/open_checkpoint_${top}_$phase.log
         } elseif {[file exists $checkpoint2]} {
            puts "\tOpening checkpoint $checkpoint2 for $top"
            open_checkpoint $checkpoint2 > $implDir/open_checkpoint_${top}_$phase.log
         } else {
            set errMsg "\nERROR: Checkpoint required for step $phase not found. Rerun necessary previous steps first."
            error $errMsg
         }
      } else {
        set errMsg "\nERROR: No checkpoint defined."
        error $errMsg
      }
   }
  
   #Run any specified pre-phase scripts
   if {![string match $pre "none"] && ![string match $pre ""] } {
      foreach script $pre {
         if {[file exists $script]} {
            puts "\tRunning pre-$phase script $script"
            source $script > $implDir/pre_${phase}_script.log
         } else {
            set errMsg "\nERROR: Script $script specified for pre-${phase} does not exist"
            error $errMsg
         }
      }
   }
 
   if {[string match $phase "write_bitstream"]} {
      set_property IS_ENABLED FALSE [get_drc_checks IOPL-8]
      set implDir $bitDir
      set impl_step "$phase -force -file $implDir/$top"
   } elseif {[string match $phase "route_phys_opt_design"]} {
      set impl_step "phys_opt_design"
   } else {
      set impl_step $phase
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
   set log "$implDir/$phase.log"
   set start_time [clock seconds]
   puts "\t################################"
   puts "\t$phase start time: \[[clock format $start_time -format {%a %b %d %H:%M:%S %Y}]\]"
   puts "\tCOMMAND: $impl_step"
   puts "\tDirecting output to $log"
   if {[catch "$impl_step > $log" $errMsg]} {
      if {[string match $phase "route_design"]} {
         puts "\tERROR: $phase failed. Writing $phase checkpoint for debug\n\t$implDir/${top}.post_${phase}_error.dcp"
         write_checkpoint -force $implDir/${top}.post_${phase}_error.dcp > $implDir/write_checkpoint.log
      }
      append errMsg "\nERROR: $phase failed.\nSee log file $log for more details."
      error $errMsg
   }
   if {![string match $phase "write_bitstream"]} {
      set SLACK [get_property SLACK [get_timing_paths]]
      puts "\tCompleted: $phase (WNS=$SLACK)"
   } else {
      puts "\tCompleted: $phase"
   }
   puts "\t################################"
      
   #Write out checkpoint for successfully completed phase
   if {![string match $phase "write_bitstream"]} {
      set start_time [clock seconds]
      puts "\tWriting $phase checkpoint: $implDir/${top}.post_$phase.dcp \[[clock format $start_time -format {%a %b %d %H:%M:%S %Y}]\]\n"
      write_checkpoint -force $implDir/${top}.post_$phase.dcp > $implDir/write_checkpoint.log
   }

   #Write out additional reports controled by verbose level
   if {($verbose > 1 || [string match $phase "route_design"]) && ![string match $phase "write_bitstream"]} {
      puts "\tGenerating report files"
      report_utilization -file $rptDir/utilization_${phase}.rpt
      #report_design_analysis -complexity -timing -setup -max_paths 10 -congestion -file $rptDir/$top.design_analysis_report.rpt
      report_timing_summary -file $rptDir/timing_summary_$phase.rpt
      report_drc -file $rptDir/drc_$phase.rpt
   } else {
      report_timing -file $rptDir/timing_$phase.rpt > $implDir/temp.log
   }

   if {[string match $phase "route_design"]} {
      puts "\tGenerating route_status report"
      report_route_status -file $rptDir/route_status.rpt
   }
}

