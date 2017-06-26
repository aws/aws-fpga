set dbg_cores [get_debug_cores -filter {NAME=~CL/*}]
if {[llength $dbg_cores]} {
   puts "AWS FPGA: Found debug_bridge instance in CL. Processing debug constraints"
   read_xdc  $HDK_SHELL_DIR/build/constraints/cl_debug_bridge.xdc
   read_xdc -cell CL/CL_DEBUG_BRIDGE/inst/xsdbm/inst  $HDK_SHELL_DIR/build/constraints/xsdbm_timing_exception.xdc
   
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
