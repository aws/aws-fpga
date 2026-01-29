# adapted from aws-fpga's strategies (minus the extra params + hook tcl)

set synth_options "-keep_equivalent_registers -retiming"
set synth_directive "default"

set opt 1
set opt_options     ""
set opt_directive   "ExploreWithRemap"

set place_options    ""
set place_directive  "Explore"

set phys_opt 1
set phys_options     ""
set phys_directive   "AggressiveExplore"

set route_options     ""
set route_directive   "Explore"

set route_phys_opt 1
set post_phys_options     ""
set post_phys_directive   "AggressiveExplore"
