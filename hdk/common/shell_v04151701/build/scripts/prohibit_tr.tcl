if [string match "2017.1" [version -short]] {
   puts "Running LUT utilization analysis"
   set lutDemand [llength [get_cells -hierarchical -filter { PRIMITIVE_TYPE =~ CLB.LUT.* } ]]
   set lutCapacity [llength [get_bels -filter { TYPE =~  "SLICE*6LUT" && PROHIBIT == "FALSE" } -of_objects [get_sites -filter { SITE_TYPE =~ "SLICE*" && PROHIBIT == "FALSE"} ] ]
   ]
   set lutUtil [expr (100 * $lutDemand) / $lutCapacity]
   
   #prohibit sites if utilization is low
   if {$lutUtil < 80} { 
     puts "Low LUT utilization detected. Prohibit placement in low routable regions"
     resize_pblock [get_pblocks pblock_CL] -remove {CLOCKREGION_X5Y10:CLOCKREGION_X5Y14}
     resize_pblock [get_pblocks pblock_CL_top] -remove {CLOCKREGION_X5Y10:CLOCKREGION_X5Y14}
   
     create_pblock prohibit_placement
     resize_pblock [get_pblocks prohibit_placement] -add {CLOCKREGION_X5Y10:CLOCKREGION_X5Y14}
     set_property EXCLUDE_PLACEMENT ON [get_pblocks prohibit_placement]
   }
}
