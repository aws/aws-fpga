if [string match "2017.1" [version -short]] {
   puts "Running LUT utilization analysis"
   set lutDemand [llength [get_cells -hierarchical -filter { PRIMITIVE_TYPE =~ CLB.LUT.* } ]]
   set lutCapacity [llength [get_bels -filter { TYPE =~  "SLICE*6LUT" && PROHIBIT == "FALSE" } -of_objects [get_sites -filter { SITE_TYPE =~ "SLICE*" && PROHIBIT == "FALSE"} ] ]
   ]
   set lutUtil [expr (100 * $lutDemand) / $lutCapacity]
   
   #prohibit sites if utilization is low
   if {$lutUtil < 80} { 
      puts "Low LUT utilization detected. Prohibit placement in low routable regions"
      set_property PROHIBIT 1 [get_sites -of [get_clock_region {X5Y10 X5Y11 X5Y12 X5Y13 X5Y14}] -filter {NAME =~ "SLICE_*"}]
   }
}
