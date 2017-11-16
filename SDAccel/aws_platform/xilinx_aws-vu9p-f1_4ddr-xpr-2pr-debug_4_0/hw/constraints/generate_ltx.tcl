if { $argc != 1 } {
	#puts "The generate_ltx.tcl script requires the xclbin dir to be input."
	#puts "For example, tclsh generate_ltx.tcl /proj/example/test1/xclbin."
	set xclbin_dir $::env(DEBUG_LTX_DIR)
	puts $xclbin_dir
} else {
	set xclbin_dir [lindex $argv 0]
}
append xclbin_dir "/debug_probes.ltx"
puts "Generating LTX file: $xclbin_dir"
write_debug_probes -force -no_partial_ltxfile $xclbin_dir