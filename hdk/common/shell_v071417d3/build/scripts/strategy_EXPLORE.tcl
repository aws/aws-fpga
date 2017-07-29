source $HDK_SHELL_DIR/build/scripts/params.tcl
source $HDK_SHELL_DIR/build/scripts/uram_options.tcl

set synth_options "-keep_equivalent_registers -flatten_hierarchy rebuilt $synth_uram_option"
set synth_directive "default"

#Set psip to 1 to enable Physical Synthesis in Placer (2017.1+ only)
set psip 0

set link 1

set opt 1
set opt_options     ""
set opt_directive   "Explore"
set opt_preHookTcl  "$HDK_SHELL_DIR/build/scripts/check_uram.tcl"
set opt_postHookTcl "$HDK_SHELL_DIR/build/scripts/apply_debug_constraints.tcl"

set place 1
set place_options     ""
set place_directive   "Explore"
set place_preHookTcl  ""
set place_postHookTcl ""

set phys_opt 1
set phys_options     ""
set phys_directive   "Explore"
set phys_preHookTcl  ""
set phys_postHookTcl ""

set route 1
set route_options    ""
set route_directive  "Explore"
set route_preHookTcl ""
set route_postHookTcl ""

set route_phys_opt 0
set post_phys_options    ""
set post_phys_directive  "Explore"
set post_phys_preHookTcl ""
set post_phys_postHookTcl ""


