####Adjust cell bloating ratio in place_design
set_param place.GPAreaBloatBudgetRatioDiablo 0.1

####Disable global router
set_param route.enableGlobalRouting false


set synth_options "-no_lc -shreg_min_size 5 -fsm_extraction one_hot -resource_sharing off"
set synth_directive "default"

#Set psip to 1 to enable Physical Synthesis in Placer (2017.1+ only)
set psip 0

set link 1

set opt 1
set opt_options    ""
set opt_directive  "Explore"
set opt_preHookTcl ""

set place 1
set place_options    ""
set place_directive  "ExtraNetDelay_high"
set place_preHookTcl "$HDK_SHELL_DIR/build/scripts/prohibit_tr.tcl $CL_DIR/build/scripts/apply_debug_constraints.tcl $HDK_SHELL_DIR/build/scripts/cl_xpr_xdc.tcl"

set phys_opt 1
set phys_options    ""
set phys_directive  "Explore"
set phys_preHookTcl ""

set route 1
set route_options    "-tns_cleanup"
set route_directive  "Explore"
set route_preHookTcl ""

set route_phys_opt 1
set post_phys_options    ""
set post_phys_directive  "Explore"
set post_phys_preHookTcl ""


