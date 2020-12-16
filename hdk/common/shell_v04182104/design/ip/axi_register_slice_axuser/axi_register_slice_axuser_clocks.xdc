###############################################################################################################
# Core-Level Timing Constraints for axi_register_slice Component "axi_register_slice_axuser"
###############################################################################################################
#
# This component is not configured in a multi-SLR crossing mode.
# No timing core-level constraints are needed.
#
#

create_waiver -internal -scope -type CDC -id CDC-7 -user axi_register_slice -tags "1040889" -to [get_pins -filter {REF_PIN_NAME=~CLR} -of_objects  [get_cells -hierarchical -regexp .*15.*_multi/.*/common.srl_fifo_0/asyncclear_.*]] \
-description {Waiving CDC-7, CDC between 2 known synchronous clock domains}
