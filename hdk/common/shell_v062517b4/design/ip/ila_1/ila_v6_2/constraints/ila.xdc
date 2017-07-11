##
## ARM and HALT transfer false paths
##
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_reset_ctrl/asyncrounous_transfer*/din_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_reset_ctrl/asyncrounous_transfer*/dout_reg0_reg*" && IS_SEQUENTIAL } ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_reset_ctrl/asyncrounous_transfer.arm_in_transfer_inst/dout_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_reset_ctrl/asyncrounous_transfer.arm_in_transfer_inst/temp_reg0_reg*" && IS_SEQUENTIAL } ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_reset_ctrl/asyncrounous_transfer.halt_in_transfer_inst/dout_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_reset_ctrl/asyncrounous_transfer.halt_in_transfer_inst/temp_reg0_reg*" && IS_SEQUENTIAL } ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_reset_ctrl/asyncrounous_transfer.halt_out_transfer_inst/dout_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_reset_ctrl/asyncrounous_transfer.halt_out_transfer_inst/temp_reg0_reg*" && IS_SEQUENTIAL } ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_reset_ctrl/asyncrounous_transfer.arm_out_transfer_inst/dout_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_reset_ctrl/asyncrounous_transfer.arm_out_transfer_inst/temp_reg0_reg*" && IS_SEQUENTIAL } ]

##
## ILA Register False Paths
##
#set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_*/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_1a/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_sample_counter/iscnt_reg*" && IS_SEQUENTIAL } ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_1a/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/iwcnt_reg*" && IS_SEQUENTIAL } ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_1a/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/u_wcnt_hcmp_q*" && IS_SEQUENTIAL } ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_1a/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/u_wcnt_lcmp_q*" && IS_SEQUENTIAL } ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_1a/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_sample_counter/u_scnt_cmp_q*" && IS_SEQUENTIAL } ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_7/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/u_wcnt_hcmp_q*" && IS_SEQUENTIAL } ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_7/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/u_wcnt_lcmp_q*" && IS_SEQUENTIAL } ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_7/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_sample_counter/u_scnt_cmp_q*" && IS_SEQUENTIAL } ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_1a/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/U_CDONE/I_YESLUT6.I_YES_OREG.O_reg*" && IS_SEQUENTIAL} ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_1a/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/U_NS0/I_YESLUT6.I_YES_OREG.O_reg*" && IS_SEQUENTIAL} ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_1a/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/U_NS1/I_YESLUT6.I_YES_OREG.O_reg*" && IS_SEQUENTIAL} ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_1a/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/icap_wr_en_reg*" && IS_SEQUENTIAL} ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_1a/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/itrigger_out_reg*" && IS_SEQUENTIAL} ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_15/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/use_probe_debug_circuit_2_reg*" && IS_SEQUENTIAL} ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_15/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/en_adv_trigger_2_reg*" && IS_SEQUENTIAL} ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_1a/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/en_adv_trigger_2_reg*" && IS_SEQUENTIAL} ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_1a/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/capture_qual_ctrl_2_reg*" && IS_SEQUENTIAL} ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_stream_ffd/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/debug_data_in_sync1_reg*" && IS_SEQUENTIAL} ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/*.cfg_data_vec_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/cfg_data_vec_sync1_reg*" && IS_SEQUENTIAL} ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_regs/reg_stream_ffd/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL} ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_trig/U_TM/N_DDR_MODE.G_NMU[*].U_M/allx_typeA_match_detection.ltlib_v1_0_0_allx_typeA_inst/probeDelay1_reg*" && IS_SEQUENTIAL} ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_15/I_EN_CTL_EQ1.U_CTL/xsdb_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_trig/U_TM/N_DDR_MODE.G_NMU[*].U_M/allx_typeA_match_detection.ltlib_v1_0_0_allx_typeA_inst/probeDelay1_reg*" && IS_SEQUENTIAL} ]

##
## Match Unit Configuration to Match Output false path
##

set_false_path -from [get_pins -hierarchical -filter {NAME =~ *allx_typeA_match_detection.ltlib_v1_0_0_allx_typeA_inst/DUT/u_srl_drive/CLK}] -to [get_pins -hierarchical -filter {NAME =~ *allx_typeA_match_detection.ltlib_v1_0_0_allx_typeA_inst/DUT/I_WHOLE_SLICE.G_SLICE_IDX[*].U_ALL_SRL_SLICE/I_IS_TERMINATION_SLICE_W_OUTPUT_REG.DOUT_O_reg/D}]
set_false_path -from [get_pins -hierarchical -filter {NAME =~ *allx_typeA_match_detection.ltlib_v1_0_0_allx_typeA_inst/DUT/I_WHOLE_SLICE.G_SLICE_IDX[*].U_ALL_SRL_SLICE/u_srl*/S*/CLK}] -to [get_pins -hierarchical -filter {NAME =~ *allx_typeA_match_detection.ltlib_v1_0_0_allx_typeA_inst/DUT/I_WHOLE_SLICE.G_SLICE_IDX[*].U_ALL_SRL_SLICE/I_IS_TERMINATION_SLICE_W_OUTPUT_REG.DOUT_O_reg/D}]

##
## ILA Capture Block False Paths
##

set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/*cfg_data_vec_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/*icap_addr_reg*" && IS_SEQUENTIAL } ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/captured_samples*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg*/I_EN_STAT_EQ1.U_STAT/xsdb_reg*" && IS_SEQUENTIAL } ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/CAP_DONE_O*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg*/I_EN_STAT_EQ1.U_STAT/xsdb_reg*" && IS_SEQUENTIAL } ]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/CAP_TRIGGER_O*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg*/I_EN_STAT_EQ1.U_STAT/xsdb_reg*" && IS_SEQUENTIAL } ]

##
## ILA Capture State to XSDB register False Paths
##
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/U_NS*/I_YESLUT6.I_YES_OREG.O_reg_reg*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_regs/reg_*/I_EN_STAT_EQ1.U_STAT/xsdb_reg_reg[*]*" && IS_SEQUENTIAL } ]

##
## ILA Sample Counter Match Condition out False Paths
##
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_sample_counter/U_SCMPCE/I_YESLUT6.U_SRL32/CLK*"}] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_sample_counter/u_scnt_cmp_q*" && IS_SEQUENTIAL } ]
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_sample_counter/u_scnt_cmp/allx_typeA_match_detection.ltlib_v1_0_0_allx_typeA_inst/DUT/u_srl_drive/CLK*"}] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_sample_counter/u_scnt_cmp_q*" && IS_SEQUENTIAL } ]
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_sample_counter/u_scnt_cmp/allx_typeA_match_detection.ltlib_v1_0_0_allx_typeA_inst/DUT/I_WHOLE_SLICE.G_SLICE_IDX[*].U_ALL_SRL_SLICE/u_srl*/S*/CLK*"}] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_sample_counter/u_scnt_cmp_q*" && IS_SEQUENTIAL } ]
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/U_CMPRESET/I_YESLUT6.U_SRL32_*/CLK*" }] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_sample_counter/u_scnt_cmp_q*" && IS_SEQUENTIAL } ]

##
## ILA Window Counter Match Condition out False Paths
##
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/u_wcnt_lcmp/allx_typeA_match_detection.ltlib_v1_0_0_allx_typeA_inst/DUT/I_WHOLE_SLICE.G_SLICE_IDX[*].U_ALL_SRL_SLICE/u_srl*/S*/CLK*"}] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/u_wcnt_lcmp_q*" && IS_SEQUENTIAL } ]
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/u_wcnt_hcmp/allx_typeA_match_detection.ltlib_v1_0_0_allx_typeA_inst/DUT/I_WHOLE_SLICE.G_SLICE_IDX[*].U_ALL_SRL_SLICE/u_srl*/S*/CLK*"}] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/u_wcnt_hcmp_q*" && IS_SEQUENTIAL } ]
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/u_wcnt_lcmp/allx_typeA_match_detection.ltlib_v1_0_0_allx_typeA_inst/DUT/u_srl_drive/CLK*"}] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/u_wcnt_lcmp_q*" && IS_SEQUENTIAL } ]
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/u_wcnt_hcmp/allx_typeA_match_detection.ltlib_v1_0_0_allx_typeA_inst/DUT/u_srl_drive/CLK*"}] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/u_wcnt_hcmp_q*" && IS_SEQUENTIAL } ]
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/U_WHCMPCE/I_YESLUT6.U_SRL32/CLK*"}] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/u_wcnt_hcmp_q*" && IS_SEQUENTIAL } ]
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/U_WLCMPCE/I_YESLUT6.U_SRL32/CLK*"}] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/u_wcnt_lcmp_q*" && IS_SEQUENTIAL } ]
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/U_CMPRESET/I_YESLUT6.U_SRL32_*/CLK*" }] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/u_wcnt_lcmp_q*" && IS_SEQUENTIAL } ]
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/U_CMPRESET/I_YESLUT6.U_SRL32_*/CLK*" }] -to [get_cells -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/u_wcnt_hcmp_q*" && IS_SEQUENTIAL } ]
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_sample_counter/U_SCE/I_YESLUT6.U_SRLC16E/CLK*" }] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_sample_counter/iscnt_reg*" && IS_SEQUENTIAL }]
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_sample_counter/U_SCE/I_YESLUT6.U_SRLC16E/CLK*" }] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/icap_wr_en_reg*" && IS_SEQUENTIAL }]
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_sample_counter/U_SCRST/I_YESLUT6.U_SRL32_*/CLK*" }] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_sample_counter/iscnt_reg*" && IS_SEQUENTIAL }] 
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/U_WCE/I_YESLUT6.U_SRLC16E/CLK*" }] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/u_cap_addrgen/u_cap_window_counter/iwcnt_reg*" && IS_SEQUENTIAL }]
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/U_CDONE/I_YESLUT6.U_SRL32_*/CLK*" }] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/U_CDONE/I_YESLUT6.I_YES_OREG.O_reg*" && IS_SEQUENTIAL} ]
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/U_NS0/I_YESLUT6.U_SRL32_*/CLK*" }] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/U_NS0/I_YESLUT6.I_YES_OREG.O_reg*" && IS_SEQUENTIAL} ]
set_false_path -from [get_pins -hierarchical -filter { NAME =~  "*ila_core_inst/u_ila_cap_ctrl/U_NS1/I_YESLUT6.U_SRL32_*/CLK*" }] -to [get_cells -hierarchical -filter { NAME =~ "*ila_core_inst/u_ila_cap_ctrl/U_NS1/I_YESLUT6.I_YES_OREG.O_reg*" && IS_SEQUENTIAL} ]



