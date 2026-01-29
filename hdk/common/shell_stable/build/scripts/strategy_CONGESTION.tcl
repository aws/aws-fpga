# adapted from aws-fpga's strategies (minus the extra params + hook tcl)

set synth_options "-no_lc -shreg_min_size 10 -control_set_opt_threshold 16 -retiming"
set synth_directive "AlternateRoutability"

set opt 1
set opt_options    "-bufg_opt -control_set_merge -hier_fanout_limit 512 -muxf_remap -propconst -retarget -sweep"
set opt_directive  ""

set place_options    ""
set place_directive  "AltSpreadLogic_medium"

set phys_opt 1
set phys_options     ""
set phys_directive   "AggressiveExplore"

set route_options    ""
set route_directive  "Explore"

set route_phys_opt 0
set post_phys_options    ""
set post_phys_directive  ""
