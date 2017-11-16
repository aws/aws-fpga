set platform_constraints_dir ""
if { $argc != 1 } {
	#puts "The debug_constraints.tcl script requires the platform constraints dir to be input."
	#puts "For example, tclsh debug_constraints.tcl $SDACCEL_DIR/aws_platform/xilinx_aws-vu9p-f1_4ddr-xpr-2pr-debug_4_0/hw/constraints"
	
	set platform_constraints_dir $::env(AWS_DEBUG_SCRIPTS_DIR)
	puts $platform_constraints_dir
} else {
	set platform_constraints_dir [lindex $argv 0]
}
	
set dbg_bridge [get_debug_cores -filter {NAME=~CL/*CL_DEBUG_BRIDGE* || NAME=~CL/dbg_hub_1}]
if {[llength $dbg_bridge]} {
   puts "AWS FPGA: Found debug_bridge instance $dbg_bridge in CL. Processing debug constraints"
   if { [get_cells $dbg_bridge] == "CL/CL_DEBUG_BRIDGE/inst/xsdbm"} {
	  set db_xdc $platform_constraints_dir 
	  append db_xdc "/cl_debug_bridge.xdc"			
	  read_xdc  $db_xdc
   }
   if { [get_cells $dbg_bridge] == "CL/dbg_hub_1"} {
	  set dh_xdc $platform_constraints_dir 
	  append dh_xdc "/cl_debug_bridge_hlx.xdc"	
	  read_xdc  $dh_xdc
   }   
   if {[llength [get_cells -quiet $dbg_bridge/inst]]} {
      set xsdbm_xdc $platform_constraints_dir 
	  append xsdbm_xdc "/xsdbm_timing_exception.xdc"	
	  read_xdc -cell $dbg_bridge/inst  $xsdbm_xdc
   }
   
   set dbg_cores [get_debug_cores -filter {NAME=~CL/*}]
   if {[llength $dbg_cores] > 1} {
	  set dbg_hub_cells [list \
		 *runtest_i_reg \
		 *tms_i_reg \
	  ]
   } else {
	  set dbg_hub_cells [list \
		 *runtest_i_reg \
		 *tms_i_reg \
		 *update_i_reg \
		 *shift_i_reg \
		 *sel_i_reg \
		 *tdi_i_reg \
		 *tms_i_reg \
		 *drck_i_reg \
		 *reset_i_reg \
		 *runtest_i_reg \
		 *capture_i_reg \
		 *bscanid_en_i_reg \
		 *bscanid_i_reg[*] \
	  ]
   }
   foreach cell $dbg_hub_cells {
	  set dbg_reg [get_cells -quiet -hier -filter NAME=~CL/*xsdbm*/$cell]
	  if [llength $dbg_reg] {
		 foreach reg $dbg_reg {
			puts "Setting false path to dbg register $reg"
			set_false_path -to [get_pins $reg/D]
		 }
	  }
   }
}


