## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

+incdir+${XILINX_IP}/ddr4_core/rtl/ip_top
+incdir+${XILINX_IP}/ddr4_core/rtl/cal
+incdir+${XILINX_IP}/ddr4_core/ip_1/rtl/map
+incdir+${HDK_COMMON_DIR}/verif/tb/sv

${XILINX_IP}/ddr4_core/ip_1/rtl/phy/ddr4_phy_v2_2_xiphy_behav.sv
${XILINX_IP}/ddr4_core/ip_1/rtl/phy/ddr4_phy_v2_2_xiphy.sv
${XILINX_IP}/ddr4_core/ip_1/rtl/iob/ddr4_phy_v2_2_iob_byte.sv
${XILINX_IP}/ddr4_core/ip_1/rtl/iob/ddr4_phy_v2_2_iob.sv
${XILINX_IP}/ddr4_core/ip_1/rtl/clocking/ddr4_phy_v2_2_pll.sv
${XILINX_IP}/ddr4_core/ip_1/rtl/xiphy_files/ddr4_phy_v2_2_xiphy_tristate_wrapper.sv
${XILINX_IP}/ddr4_core/ip_1/rtl/xiphy_files/ddr4_phy_v2_2_xiphy_riuor_wrapper.sv
${XILINX_IP}/ddr4_core/ip_1/rtl/xiphy_files/ddr4_phy_v2_2_xiphy_control_wrapper.sv
${XILINX_IP}/ddr4_core/ip_1/rtl/xiphy_files/ddr4_phy_v2_2_xiphy_byte_wrapper.sv
${XILINX_IP}/ddr4_core/ip_1/rtl/xiphy_files/ddr4_phy_v2_2_xiphy_bitslice_wrapper.sv
${XILINX_IP}/ddr4_core/ip_1/rtl/phy/ddr4_core_phy_ddr4.sv
${XILINX_IP}/ddr4_core/ip_1/rtl/ip_top/ddr4_core_phy.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_wtr.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_ref.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_rd_wr.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_periodic.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_group.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_ecc_merge_enc.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_ecc_gen.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_ecc_fi_xor.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_ecc_dec_fix.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_ecc_buf.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_ecc.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_ctl.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_cmd_mux_c.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_cmd_mux_ap.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_arb_p.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_arb_mux_p.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_arb_c.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_arb_a.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_act_timer.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc_act_rank.sv
${XILINX_IP}/ddr4_core/rtl/controller/ddr4_v2_2_mc.sv
${XILINX_IP}/ddr4_core/rtl/ui/ddr4_v2_2_ui_wr_data.sv
${XILINX_IP}/ddr4_core/rtl/ui/ddr4_v2_2_ui_rd_data.sv
${XILINX_IP}/ddr4_core/rtl/ui/ddr4_v2_2_ui_cmd.sv
${XILINX_IP}/ddr4_core/rtl/ui/ddr4_v2_2_ui.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_axi_ar_channel.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_axi_aw_channel.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_axi_b_channel.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_axi_cmd_arbiter.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_axi_cmd_fsm.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_axi_cmd_translator.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_axi_fifo.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_axi_incr_cmd.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_axi_r_channel.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_axi_w_channel.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_axi_wr_cmd_fsm.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_axi_wrap_cmd.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_a_upsizer.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_axi.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_axi_register_slice.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_axi_upsizer.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_axic_register_slice.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_carry_and.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_carry_latch_and.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_carry_latch_or.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_carry_or.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_command_fifo.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_comparator.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_comparator_sel.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_comparator_sel_static.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_r_upsizer.sv
${XILINX_IP}/ddr4_core/rtl/axi/ddr4_v2_2_w_upsizer.sv
${XILINX_IP}/ddr4_core/rtl/axi_ctrl/ddr4_v2_2_axi_ctrl_addr_decode.sv
${XILINX_IP}/ddr4_core/rtl/axi_ctrl/ddr4_v2_2_axi_ctrl_read.sv
${XILINX_IP}/ddr4_core/rtl/axi_ctrl/ddr4_v2_2_axi_ctrl_reg_bank.sv
${XILINX_IP}/ddr4_core/rtl/axi_ctrl/ddr4_v2_2_axi_ctrl_reg.sv
${XILINX_IP}/ddr4_core/rtl/axi_ctrl/ddr4_v2_2_axi_ctrl_top.sv
${XILINX_IP}/ddr4_core/rtl/axi_ctrl/ddr4_v2_2_axi_ctrl_write.sv
${XILINX_IP}/ddr4_core/rtl/clocking/ddr4_v2_2_infrastructure.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_cal_xsdb_bram.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_cal_write.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_cal_wr_byte.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_cal_wr_bit.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_cal_sync.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_core_ddr4_cal_riu.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_cal_read.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_cal_rd_en.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_cal_pi.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_cal_mc_odt.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_cal_debug_microblaze.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_cal_cplx_data.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_cal_cplx.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_cal_config_rom.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_cal_addr_decode.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_cal_top.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_cal_xsdb_arbiter.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_cal.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_chipscope_xsdb_slave.sv
${XILINX_IP}/ddr4_core/rtl/cal/ddr4_v2_2_dp_AB9.sv
${XILINX_IP}/ddr4_core/rtl/ip_top/ddr4_core.sv
${XILINX_IP}/ddr4_core/rtl/ip_top/ddr4_core_ddr4.sv
${XILINX_IP}/ddr4_core/rtl/ip_top/ddr4_core_ddr4_mem_intfc.sv
${XILINX_IP}/ddr4_core/tb/microblaze_mcs_0.sv

+incdir+${HDK_COMMON_DIR}/verif/models/ddr4_model


-y ${HDK_COMMON_DIR}/verif/models/ddr4_model
-y ${HDK_COMMON_DIR}/verif/models/ddr4_rdimm_wrapper

# ${HDK_COMMON_DIR}/verif/models/ddr4_rdimm_wrapper/ddr4_rdimm_wrapper.sv
${HDK_COMMON_DIR}/verif/models/ddr4_model/ddr4_sdram_model_wrapper.sv
