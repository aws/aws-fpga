set CL_DIR [lindex $argv 0]
create_project -in_memory -part xcvu9p-flgb2104-2-i -force
source $CL_DIR/design/FireSim-generated.env.tcl
source $CL_DIR/build/scripts/synth_firesim_clk_wiz.tcl
exit
