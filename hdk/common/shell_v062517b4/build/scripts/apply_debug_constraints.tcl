#checking if HDK_SHELL_DIR env variable exists                                                                                                 
if { [info exists ::env(HDK_SHELL_DIR)] } {
        set HDK_SHELL_DIR $::env(HDK_SHELL_DIR)
        puts "Using Shell directory $HDK_SHELL_DIR";
} else {
        puts "Error: HDK_SHELL_DIR environment variable not defined ! ";
        puts "Run the hdk_setup.sh script from the root directory of aws-fpga";
        exit 2
}

#checking if CL_DIR env variable exists                                                                                                 
if { [info exists ::env(CL_DIR)] } {
        set CL_DIR $::env(CL_DIR)
        puts "Using CL directory $CL_DIR";
} else {
        puts "Error: CL_DIR environment variable not defined ! ";
        puts "Run the hdk_setup.sh script from the root directory of aws-fpga";
        exit 2
}

set dbg_bridge [get_debug_cores -filter {NAME=~CL/*CL_DEBUG_BRIDGE*}]
if {[llength $dbg_bridge]} {
   puts "AWS FPGA: Found debug_bridge instance $dbg_bridge in CL. Processing debug constraints"
   if {[llength [get_cells -quiet $dbg_bridge/inst/BSCANID.u_xsdbm_id/CORE_XSDB.UUT_MASTER/U_ICON_INTERFACE/U_CMD6_RD/U_RD_FIFO/SUBCORE_FIFO.xsdbm_v3_0_0_rdfifo_inst]]} {
      read_xdc  $HDK_SHELL_DIR/build/constraints/cl_debug_bridge.xdc
   }
   if {[llength [get_cells -quiet CL/CL_DEBUG_BRIDGE/inst/xsdbm/inst]]} {
      read_xdc -cell CL/CL_DEBUG_BRIDGE/inst/xsdbm/inst  $HDK_SHELL_DIR/build/constraints/xsdbm_timing_exception.xdc
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
