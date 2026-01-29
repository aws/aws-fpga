# adapted from aws-fpga's strategies (minus the extra params + hook tcl)

set synth_options "-keep_equivalent_registers -flatten_hierarchy rebuilt -retiming"
set synth_directive "default"

set opt 1
set opt_options    ""
set opt_directive  ""

set place_options    ""
set place_directive  ""

set phys_opt 0
set phys_options    ""
set phys_directive  ""

set route_options    ""
set route_directive  ""

set route_phys_opt 0
set post_phys_options    ""
set post_phys_directive  ""
