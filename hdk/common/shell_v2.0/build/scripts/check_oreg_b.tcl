set clean 1
foreach uram [get_cells -hier -filter REF_NAME==URAM288] {
   set oregB [get_property OREG_B $uram]
   if {![string match -nocase "false" $oregB] || $oregB} {
      set clean '0'
      puts "Error: URAM288 instance \'$uram\' has OREG_B set to $oregB."
   }

   set oregEccB [get_property OREG_ECC_B $uram]
   if {![string match -nocase "false" $oregEccB] || $oregEccB} {
      set clean 0
      puts "Error: URAM288 instance \'$uram\' has OREG_ECC_B set to $oregEccB."
   }
   puts "Debug: Uram:$uram\t OREG_B:$oregB\t OREG_ECC_B\t$oregEccB"
}

if {!$clean} {
   set errMsg "\nError: 1 or more URAM288 cells in the design are using OREG_B port. This is not supported for this flow. Review previous error messages and update URAM288 to set OREG_B and OREG_ECC_B properties to false."
   error $errMsg
}
