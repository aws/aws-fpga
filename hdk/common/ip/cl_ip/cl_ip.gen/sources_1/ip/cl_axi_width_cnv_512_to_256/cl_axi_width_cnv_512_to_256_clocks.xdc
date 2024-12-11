###############################################################################################################
# Core-Level Timing Constraints for axi_dwidth_converter Component "cl_axi_width_cnv_512_to_256"
###############################################################################################################
#
# This component is not configured to perform asynchronous clock-domain-crossing.
# No timing core-level constraints are needed.
# (Synchronous clock-domain-crossings, if any, remain covered by your system-level PERIOD constraints.)

create_waiver -type CDC -id {CDC-1} -user "axi_dwidth_converter" -desc "Timing-uncritical signals driving a simple status LED (combined from multiple sources)" -tags "1165309" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*CE -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_upsizer.gen_full_upsizer.axi_upsizer_inst/USE_*.gen_pktfifo_*_upsizer.pktfifo_*_data_inst/dw_fifogen_*/inst_fifo_gen/gaxi_full_lite.*_ch.*.axi_*/grf.rf/gntv_or_sync_fifo.gl0.*/*/*[*]}]]

create_waiver -type CDC -id {CDC-1} -user "axi_dwidth_converter" -desc "Timing-uncritical signals driving a simple status LED (combined from multiple sources)" -tags "1165309" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~* -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_upsizer.gen_full_upsizer.axi_upsizer_inst/USE_*.gen_pktfifo_*_upsizer.pktfifo_*_data_inst/dw_fifogen_*/inst_fifo_gen/gaxi_full_lite.*_ch.*.axi_*/grf.rf/gntv_or_sync_fifo.*/gdm.dm_gen.dm/*/*}]]

create_waiver -type CDC -id {CDC-1} -user "axi_dwidth_converter" -desc "Timing-uncritical signals driving a simple status LED (combined from multiple sources)" -tags "1165309" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_upsizer.gen_full_upsizer.axi_upsizer_inst/USE_*.gen_pktfifo_*_upsizer.pktfifo_*_data_inst/dw_fifogen_*/inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gl0.rd/gr1.gr1_int.*/*}]]

create_waiver -type CDC -id {CDC-1} -user "axi_dwidth_converter" -desc "Timing-uncritical signals driving a simple status LED (combined from multiple sources)" -tags "1165309" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_upsizer.gen_full_upsizer.axi_upsizer_inst/USE_*.gen_pktfifo_*_upsizer.pktfifo_*_data_inst/dw_fifogen_*/inst_fifo_gen/gconvfifo.rf/grf.rf/gntv_or_sync_fifo.gl0.rd/gr1.gr1_int.*/*[*]}]]

create_waiver -type CDC -id {CDC-1} -user "axi_dwidth_converter" -desc "Timing-uncritical signals driving a simple status LED (combined from multiple sources)" -tags "1165309" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~* -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_upsizer.gen_full_upsizer.axi_upsizer_inst/USE_*.gen_pktfifo_*_upsizer.pktfifo_*_data_inst/dw_fifogen_*/inst_fifo_gen/gaxi_full_lite.*_ch.*.axi_*/grf.rf/gntv_or_sync_fifo.gl0.*/*.*/*}]]

create_waiver -type CDC -id {CDC-1} -user "axi_dwidth_converter" -desc "Timing-uncritical signals driving a simple status LED (combined from multiple sources)" -tags "1165309" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_upsizer.gen_full_upsizer.axi_upsizer_inst/USE_*.gen_b_clk_conv.gen_*_sync_conv.*_sync_clock_converter/gen_sync_clock_converter.s_tready_*_reg}]]

create_waiver -type CDC -id {CDC-1} -user "axi_dwidth_converter" -desc "Timing-uncritical signals driving a simple status LED (combined from multiple sources)" -tags "1165309" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~* -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_upsizer.gen_full_upsizer.axi_upsizer_inst/USE_*.gen_pktfifo_*_upsizer.pktfifo_*_data_inst/*}]]

create_waiver -type CDC -id {CDC-1} -user "axi_dwidth_converter" -desc "Timing-uncritical signals driving a simple status LED (combined from multiple sources)" -tags "1165309" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~* -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_upsizer.gen_full_upsizer.axi_upsizer_inst/*}]]

create_waiver -type CDC -id {CDC-1} -user "axi_dwidth_converter" -desc "Timing-uncritical signals driving a simple status LED (combined from multiple sources)" -tags "1165309" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_upsizer.gen_full_upsizer.axi_upsizer_inst/gen_clock_conv.gen_sync_conv.axic_sample_cycle_inst/gen_sample_cycle.*_*_*_reg}]]

create_waiver -type CDC -id {CDC-1} -user "axi_dwidth_converter" -desc "Timing-uncritical signals driving a simple status LED (combined from multiple sources)" -tags "1165309" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_upsizer.gen_full_upsizer.axi_upsizer_inst/gen_clock_conv.gen_sync_conv.axic_sample_cycle_inst/gen_sample_cycle.gen_delay[*].sample_cycle_d_reg[*]}]]

create_waiver -type CDC -id {CDC-10} -user "axi_dwidth_converter" -desc "Timing-uncritical signals driving a simple status LED (combined from multiple sources)" -tags "1165309" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_upsizer.gen_full_upsizer.axi_upsizer_inst/gen_clock_conv.gen_sync_conv.axic_sample_cycle_inst/gen_sample_cycle.gen_delay[*].sample_cycle_d_reg[*]}]]

create_waiver -type CDC -id {CDC-10} -user "axi_dwidth_converter" -desc "Timing-uncritical signals driving a simple status LED (combined from multiple sources)" -tags "1165309" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*PRE -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_upsizer.gen_full_upsizer.axi_upsizer_inst/*/dw_fifogen_*/inst_fifo_gen/*/grf.rf/rstblk/*/arststages_ff_reg[*]}]]

create_waiver -type CDC -id {CDC-10} -user "axi_dwidth_converter" -desc "Timing-uncritical signals driving a simple status LED (combined from multiple sources)" -tags "1165309" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*PRE -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_upsizer.gen_full_upsizer.axi_upsizer_inst/*/inst_fifo_gen/*/grf.rf/rstblk/*/arststages_ff_reg[*]}]]

create_waiver -type CDC -id {CDC-2} -user "axi_dwidth_converter" -desc "Timing-uncritical signals driving a simple status LED (combined from multiple sources)" -tags "1165309" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_upsizer.gen_full_upsizer.axi_upsizer_inst/gen_clock_conv.gen_sync_conv.axic_sample_cycle_inst/gen_sample_cycle.gen_delay[*].sample_cycle_*_reg[*]}]]

create_waiver -type CDC -id {CDC-11} -user "axi_dwidth_converter" -desc "Timing-uncritical signals driving a simple status LED (combined from multiple sources)" -tags "1165309" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*PRE -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_upsizer.gen_full_upsizer.axi_upsizer_inst/*/*/inst_fifo_*/*/grf.rf/rstblk/*/arststages_ff_reg[*]}]]

create_waiver -type CDC -id {CDC-11} -user "axi_dwidth_converter" -desc "Timing-uncritical signals driving a simple status LED (combined from multiple sources)" -tags "1165309" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*PRE -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/gen_upsizer.gen_full_upsizer.axi_upsizer_inst/*/inst_fifo_gen/*/grf.rf/rstblk/*/arststages_ff_reg[*]}]]




