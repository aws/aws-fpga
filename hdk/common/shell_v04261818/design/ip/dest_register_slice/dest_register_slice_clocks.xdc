###############################################################################################################
# Core-Level Timing Constraints for axi_register_slice Component "dest_register_slice"
###############################################################################################################
#
# This component is not configured in a multi-SLR crossing mode.
# No timing core-level constraints are needed.
#
#

create_waiver -internal -scope -type CDC -id CDC-7 -user axi_register_slice -tags "1040889" -to [get_pins -filter {REF_PIN_NAME=~CLR} -of_objects  [get_cells -hierarchical -regexp .*15.*_multi/.*/common.srl_fifo_0/asyncclear_.*]] \
-description {Waiving CDC-7, CDC between 2 known synchronous clock domains}

create_waiver -type CDC -id {CDC-1} -user "axi_register_slice" -desc "Timing uncritical paths" -tags "1165639" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*CE -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/aw12.slr_master_aw/tdm.laguna_m_payload_i_reg[*]}]]

create_waiver -type CDC -id {CDC-1} -user "axi_register_slice" -desc "Timing uncritical paths" -tags "1165639" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*CE -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/aw12.slr_slave_aw/tdm.laguna_s_payload_d_reg[*]}]]

create_waiver -type CDC -id {CDC-1} -user "axi_register_slice" -desc "Timing uncritical paths" -tags "1165639" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*CE -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/aw12.slr_slave_aw/tdm.payload_tdm_d4_reg[*]}]]

create_waiver -type CDC -id {CDC-1} -user "axi_register_slice" -desc "Timing uncritical paths" -tags "1165639" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/*12.slr_master_aw/tdm.laguna_m_payload_i_reg[*]}]]

create_waiver -type CDC -id {CDC-1} -user "axi_register_slice" -desc "Timing uncritical paths" -tags "1165639" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*CE -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/*.slr_*_*/tdm.laguna_*_payload_*_reg[*]}]]
	
create_waiver -type CDC -id {CDC-1} -user "axi_register_slice" -desc "Timing uncritical paths" -tags "1165639" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/*.slr_*_*/tdm.laguna_*_payload_*_reg[*]}]]

create_waiver -type CDC -id {CDC-1} -user "axi_register_slice" -desc "Timing uncritical paths" -tags "1165639" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*CE -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/*.slr_*_*/tdm.payload_tdm_d*_reg[*]}]]

create_waiver -type CDC -id {CDC-1} -user "axi_register_slice" -desc "Timing uncritical paths" -tags "1165639" -scope -internal \
    -from [get_pins -quiet -filter REF_PIN_NAME=~*C -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/*12.slr_*_*/tdm.tdm_sample_inst/slow_clk_div2_reg}]] \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/*12.slr_*_*/tdm.tdm_sample_inst/posedge_finder_*_reg}]]

create_waiver -type CDC -id {CDC-1} -user "axi_register_slice" -desc "Timing uncritical paths" -tags "1165639" -scope -internal \
    -from [get_pins -quiet -filter REF_PIN_NAME=~*C -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/*12.slr_*_*/tdm.tdm_sample_inst/slow_clk_div2_reg}]] \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */*12.slr_*_*/tdm.tdm_sample_inst/sample_cycle_r_reg}]]
create_waiver -type CDC -id {CDC-1} -user "axi_register_slice" -desc "Timing uncritical paths" -tags "1182745" -scope -internal \
    -from [get_pins -quiet -filter REF_PIN_NAME=~*C -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/*12.slr_*_*/tdm.*_ready_*_reg*}]] \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*R -of_objects [get_cells -hierarchical -filter {NAME =~ */*12.slr_*_*/tdm.laguna_m_payload_i_reg*}]]
