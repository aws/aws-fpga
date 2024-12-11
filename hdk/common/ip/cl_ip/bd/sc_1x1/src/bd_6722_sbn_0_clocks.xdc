################################################################################
# (c) Copyright 2013 Advanced Micro Devices, Inc. All rights reserved.
# 
# This file contains confidential and proprietary information
# of Advanced Micro Devices, Inc. and is protected under U.S. and
# international copyright and other intellectual property
# laws.
# 
# DISCLAIMER
# This disclaimer is not a license and does not grant any
# rights to the materials distributed herewith. Except as
# otherwise provided in a valid license issued to you by
# AMD, and to the maximum extent permitted by applicable
# law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
# WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
# AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
# BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
# INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
# (2) AMD shall not be liable (whether in contract or tort,
# including negligence, or under any other theory of
# liability) for any loss or damage of any kind or nature
# related to, arising under or in connection with these
# materials, including for any direct, or any indirect,
# special, incidental, or consequential loss or damage
# (including loss of data, profits, goodwill, or any type of
# loss or damage suffered as a result of any action brought
# by a third party) even if such damage or loss was
# reasonably foreseeable or AMD had been advised of the
# possibility of the same.
# 
# CRITICAL APPLICATIONS
# AMD products are not designed or intended to be fail-
# safe, or for use in any application requiring fail-safe
# performance, such as life-support or safety devices or
# systems, Class III medical devices, nuclear facilities,
# applications related to the deployment of airbags, or any
# other applications that could lead to death, personal
# injury, or severe property or environmental damage
# (individually and collectively, "Critical
# Applications"). Customer assumes the sole risk and
# liability of any use of AMD products in Critical
# Applications, subject only to applicable laws and
# regulations governing limitations on product liability.
# 
# THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
# PART OF THIS FILE AT ALL TIMES.
#
################################################################################
create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.gen_fifo_req.inst_fifo_req/gen_reg_fifo.inst_reg_fifo/gen_single_rank.inst_cntr/*}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.gen_fifo_req.inst_fifo_req/gen_reg_fifo.inst_reg_fifo/gen_single_rank.*}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -from [get_pins -quiet -filter REF_PIN_NAME=~*C -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.gen_fifo_req.inst_fifo_req/gen_reg_fifo.inst_reg_fifo/inst_sample_cycle_ratio/gen_sample_cycle.slow_clk_div2_reg}]] \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.gen_fifo_req.inst_fifo_req/gen_reg_fifo.inst_reg_fifo/inst_sample_cycle_ratio/gen_sample_cycle.posedge_finder_*_reg}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -from [get_pins -quiet -filter REF_PIN_NAME=~*C -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.gen_fifo_req.inst_fifo_req/gen_reg_fifo.inst_reg_fifo/inst_sample_cycle_ratio/gen_sample_cycle.slow_clk_div2_reg}]] \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.gen_fifo_req.inst_fifo_req/gen_reg_fifo.inst_reg_fifo/inst_sample_cycle_ratio/gen_sample_cycle.sample_cycle_r_reg}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*CE -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.inst_fifo_node_payld/gen_reg_fifo.inst_reg_fifo/gen_single_rank.data_reg[*]}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.inst_fifo_node_payld/gen_reg_fifo.inst_reg_fifo/inst_sample_cycle_ratio/gen_sample_cycle.posedge_finder_*_reg}]]


create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.inst_fifo_node_payld/gen_reg_fifo.inst_reg_fifo/inst_sample_cycle_ratio/gen_sample_cycle.sample_cycle_r_reg}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.inst_fifo_node_payld/gen_reg_fifo.inst_reg_fifo/gen_single_rank.full_r_reg}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.inst_fifo_node_payld/gen_reg_fifo.inst_reg_fifo/gen_single_rank.inst_cntr/count_r_reg[*]}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.inst_fifo_node_payld/gen_reg_fifo.inst_reg_fifo/gen_single_rank.inst_cntr/is_zero_r_reg}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.gen_fifo_req.inst_fifo_req/gen_xpm_memory_fifo.inst_fifo/gen_mem_rep[0].inst_xpm_memory/xpm_memory_base_inst/gen_rd_b.gen_rd_b_synth_template.gen_rf_narrow_reg.doutb_reg_reg[*]}]]

create_waiver -type CDC -id {CDC-4} -user "sc_node" -desc "Reads to LUTRAM are asyncronous,no synchronizer for xpm configurations" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.gen_fifo_req.inst_fifo_req/gen_xpm_memory_fifo.inst_fifo/gen_related_clocks.*_addr*_sync_i_reg[*]}]]

create_waiver -type CDC -id {CDC-4} -user "sc_node" -desc "Reads to LUTRAM are asyncronous,no synchronizer for xpm configurations" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.inst_fifo_node_payld/gen_xpm_memory_fifo.inst_fifo/gen_related_clocks.*_addr*_sync_i_reg[*]}]]

create_waiver -type CDC -id {CDC-2} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.inst_fifo_node_payld/gen_xpm_memory_fifo.inst_fifo/gen_related_clocks.*_addr*_sync_i_reg[*]}]]

create_waiver -type CDC -id {CDC-2} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.gen_fifo_req.inst_fifo_req/gen_xpm_memory_fifo.inst_fifo/gen_related_clocks.*_addr*_sync_i_reg[*]}]]

create_waiver -type CDC -id {CDC-2} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.gen_fifo_req.inst_fifo_req/gen_reg_fifo.inst_reg_fifo/inst_sample_cycle_ratio/gen_sample_cycle.gen_delay[*].sample_cycle_d_reg[*]}]]

create_waiver -type CDC -id {CDC-2} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.inst_fifo_node_payld/gen_reg_fifo.inst_reg_fifo/inst_sample_cycle_ratio/gen_sample_cycle.gen_delay[*].sample_cycle_d_reg[*]}]]


create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*CE -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.gen_fifo_req.inst_fifo_req/gen_reg_fifo.inst_reg_fifo/gen_single_rank.data_reg[*]}]]

create_waiver -type CDC -id {CDC-10} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.gen_fifo_req.inst_fifo_req/gen_reg_fifo.inst_reg_fifo/inst_sample_cycle_ratio/gen_sample_cycle.gen_delay[*].sample_cycle_d_reg[*]}]]

create_waiver -type CDC -id {CDC-10} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.inst_fifo_node_payld/gen_reg_fifo.inst_reg_fifo/inst_sample_cycle_ratio/gen_sample_cycle.gen_delay[*].sample_cycle_d_reg[*]}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst/inst_mi_handler/gen_normal_area.inst_fifo_node_payld/gen_xpm_memory_fifo.inst_fifo/gen_related_clocks.*_addr*_sync_i_reg[*]}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.gen_fifo_req.inst_fifo_req/gen_xpm_memory_fifo.inst_fifo/gen_related_clocks.*_addr*_sync_i_reg[*]}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.inst_fifo_node_payld/gen_reg_fifo.inst_reg_fifo/gen_single_rank.empty_*_reg}]]

create_waiver -type CDC -id {CDC-13} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.inst_fifo_node_payld/gen_reg_fifo.inst_reg_fifo/inst_sample_cycle_ratio/gen_sample_cycle.gen_delay[*].sample_cycle_d_reg[*]_sr*}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.gen_no_downsizer.inst_fifo_req_suppress/gen_pipe[*].pipe_reg[*][*]}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.inst_fifo_node_payld_pop_pipeline/gen_pipe[*].pipe_reg[*][*]}]]

create_waiver -type CDC -id {CDC-13} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.gen_fifo_req.inst_fifo_req/gen_reg_fifo.inst_reg_fifo/inst_sample_cycle_ratio/gen_sample_cycle.gen_delay[*].sample_cycle_d_reg[*]_sr*}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.gen_no_downsizer.inst_fifo_req_suppress/gen_pipe[*].pipe_reg[*][*]}]]

create_waiver -type CDC -id {CDC-10} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.inst_fifo_node_payld_pop_pipeline/gen_pipe[*].pipe_reg[*][*]}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.gen_downsizer.inst_downsizer/active_reg}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*CE -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.gen_downsizer.inst_downsizer/downsizer_pntr_reg[*]}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*CE -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.gen_downsizer.inst_downsizer/downsizer_repeat_reg[*]}]]

create_waiver -type CDC -id {CDC-2} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.inst_fifo_node_payld_pop_pipeline/gen_pipe[*].pipe_reg[*][*]}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.gen_downsizer.inst_downsizer/downsizer_pntr_reg[*]}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.gen_downsizer.inst_downsizer/downsizer_repeat_reg[*]}]]

create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.inst_fifo_send/gen_AB_reg_slice.payld_*_reg[*]}]]

create_waiver -type CDC -id {CDC-10} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.gen_downsizer.inst_downsizer/inst_payld_xfer_data/gen_pipe[*].pipe_reg[*][*]}]]

create_waiver -type CDC -id {CDC-4} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.gen_fifo_req.inst_fifo_req/gen_xpm_fifo_wrapper.inst_fifo/gen_xpm_fifo_async.inst_xpm_fifo_async/gnuram_async_fifo.xpm_fifo_base_inst/gen_pntr_pf_rc.wpr_rc_reg/reg_out_i_reg[*]}]]

create_waiver -type CDC -id {CDC-4} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.inst_fifo_node_payld/gen_xpm_fifo_wrapper.inst_fifo/gen_xpm_fifo_async.inst_xpm_fifo_async/gnuram_async_fifo.xpm_fifo_base_inst/gen_pntr_pf_rc.wpr_rc_reg/reg_out_i_reg[*]}]]


create_waiver -type CDC -id {CDC-4} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.gen_fifo_req.inst_fifo_req/gen_xpm_fifo_wrapper.inst_fifo/gen_xpm_fifo_async.inst_xpm_fifo_async/gnuram_async_fifo.xpm_fifo_base_inst/gen_pntr_pf_rc.rpw_rc_reg/reg_out_i_reg[*]}]]

create_waiver -type CDC -id {CDC-4} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.inst_fifo_node_payld/gen_xpm_fifo_wrapper.inst_fifo/gen_xpm_fifo_async.inst_xpm_fifo_async/gnuram_async_fifo.xpm_fifo_base_inst/gen_pntr_pf_rc.rpw_rc_reg/reg_out_i_reg[*]}]]


create_waiver -type CDC -id {CDC-1} -user "sc_node" -desc "Timing uncritical paths" -tags "1166090" -scope -internal \
    -to [get_pins -quiet -filter REF_PIN_NAME=~*D -of_objects [get_cells -hierarchical -filter {NAME =~ */inst_mi_handler/gen_normal_area.gen_downsizer.inst_downsizer/gen_*_payld.inst_downsizer_node_payld_pipe/gen_pipe[*].pipe_reg[*][*]}]]



