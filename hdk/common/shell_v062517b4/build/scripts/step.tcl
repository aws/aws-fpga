proc impl_step {phase top {options none} {directive none} {pre none} } {
   upvar  implDir implDir
   upvar  rptDir rptDir
   upvar  timestamp timestamp

   #Set value > 1 to get reports for all phases
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
   } else {
      set errMsg "\nERROR: Value $phase is not a recognized step of implementation. Valid values are:\n\topt_design\n\tplace_design\n\tphys_opt_design\n\troute_design\n\troute_phys_opt_design\n"
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
   if {[string match $phase "route_phys_opt_design"]} {
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
   puts "\t################################"
   puts "\t$phase start time: \[[clock format $start_time -format {%a %b %d %H:%M:%S %Y}]\]"
   puts "\tCOMMAND: $impl_step"
   if {[catch "$impl_step" $errMsg]} {
      if {[string match $phase "route_design"]} {
         puts "\tERROR: $phase failed. Writing $phase checkpoint for debug\n\t$implDir/${timestamp}.post_${phase}_error.dcp"
         write_checkpoint -force $implDir/${timestamp}.post_${phase}_error.dcp
      }
      append errMsg "\nERROR: $phase failed.\nSee log file for more details."
      error $errMsg
   }
   set SLACK [get_property SLACK [get_timing_paths]]
   puts "\tCompleted: $phase (WNS=$SLACK)"

   puts "\t################################"
      
   #Write out checkpoint and timing reports for successfully completed phase
   set start_time [clock seconds]
   puts "\tWriting $phase checkpoint: $implDir/${timestamp}.post_$phase.dcp \[[clock format $start_time -format {%a %b %d %H:%M:%S %Y}]\]\n"
   write_checkpoint -force $implDir/${timestamp}.post_$phase.dcp
   report_timing -delay_type max -max_paths 10 -sort_by group -input_pins -file  $rptDir/${timestamp}.post${phase}_timing_max.rpt
   report_timing -delay_type min -max_paths 10 -sort_by group -input_pins -file  $rptDir/${timestamp}.post${phase}_timing_min.rpt

   #Write out additional reports controlled by verbose level
   if {($verbose > 1 || [string match $phase "route_design"] || [string match $phase "route_phys_opt_design"]) } {
      puts "\tGenerating report files"
      report_utilization -file $rptDir/${timestamp}.utilization_${phase}.rpt
      report_drc -file $rptDir/${timestamp}.drc_$phase.rpt
   }

   if {[string match $phase "route_design"]} {
      puts "\tGenerating route_status report"
      report_route_status -file $rptDir/${timestamp}.route_status.rpt
   }
}

