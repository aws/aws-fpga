## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## verify_cl.tcl: Combine HL and CL checkpoints
## =============================================================================

##################################################
### Combine CL_routed.dcp and HL_CL_BB_routed.dcp (Done by AWS and Customer)
##################################################

open_checkpoint ../checkpoints/from_aws/HL_CL_BB_routed.dcp
read_checkpoint -strict -cell CL ../checkpoints/CL_routed.dcp

#../constraints/top.xdc
read_xdc {
../constraints/ddr.xdc
}

phys_opt_design -directive Explore
route_design -finalize

report_drc -file ../reports/HL_CL_combined_DRC.rpt
write_checkpoint -force ../checkpoints/HL_CL_combined.dcp
report_timing_summary -file ../reports/HL_CL_combined_timing.rpt
pr_verify -full_check ../checkpoints/from_aws/HL_CL_BB_routed.dcp ../checkpoints/HL_CL_combined.dcp
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
write_bitstream -force -bin_file ../bitstreams/HL_CL_combined
close_design

