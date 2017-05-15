#checking if HDK_SHELL_DIR env variable exists                                                                                                 
if { [info exists ::env(HDK_SHELL_DIR)] } {                                                                                                    
        set HDK_SHELL_DIR $::env(HDK_SHELL_DIR)
        puts "Using Shell directory $HDK_SHELL_DIR";                                                                                           
} else { 
        puts "Error: HDK_SHELL_DIR environment variable not defined ! ";                                                                       
        puts "Run the hdk_setup.sh script from the root directory of aws-fpga";                                                                
        exit 2
} 

if {[llength [get_cells -quiet CL/CL_DEBUG_BRIDGE]]} {
   puts "AWS FPGA: Found debug_bridge instance in CL. Processing debug constraints"
   read_xdc  $HDK_SHELL_DIR/build/constraints/cl_debug_bridge.xdc
   read_xdc -cell CL/CL_DEBUG_BRIDGE/inst/xsdbm/inst  $HDK_SHELL_DIR/build/constraints/xsdbm_timing_exception.xdc
}
