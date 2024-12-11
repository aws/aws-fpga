vlib modelsim_lib/work
vlib modelsim_lib/msim

vlib modelsim_lib/msim/xilinx_vip
vlib modelsim_lib/msim/xpm
vlib modelsim_lib/msim/microblaze_v11_0_13
vlib modelsim_lib/msim/xil_defaultlib
vlib modelsim_lib/msim/lib_cdc_v1_0_3
vlib modelsim_lib/msim/proc_sys_reset_v5_0_15
vlib modelsim_lib/msim/lmb_v10_v3_0_14
vlib modelsim_lib/msim/lmb_bram_if_cntlr_v4_0_24
vlib modelsim_lib/msim/blk_mem_gen_v8_4_8
vlib modelsim_lib/msim/iomodule_v3_1_10

vmap xilinx_vip modelsim_lib/msim/xilinx_vip
vmap xpm modelsim_lib/msim/xpm
vmap microblaze_v11_0_13 modelsim_lib/msim/microblaze_v11_0_13
vmap xil_defaultlib modelsim_lib/msim/xil_defaultlib
vmap lib_cdc_v1_0_3 modelsim_lib/msim/lib_cdc_v1_0_3
vmap proc_sys_reset_v5_0_15 modelsim_lib/msim/proc_sys_reset_v5_0_15
vmap lmb_v10_v3_0_14 modelsim_lib/msim/lmb_v10_v3_0_14
vmap lmb_bram_if_cntlr_v4_0_24 modelsim_lib/msim/lmb_bram_if_cntlr_v4_0_24
vmap blk_mem_gen_v8_4_8 modelsim_lib/msim/blk_mem_gen_v8_4_8
vmap iomodule_v3_1_10 modelsim_lib/msim/iomodule_v3_1_10

vlog -work xilinx_vip -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_axi4streampc.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_axi4pc.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/xil_common_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/clk_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/rst_vip_if.sv" \

vlog -work xpm -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/map" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/ip_top" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"$XILINX_VIVADO/data/ip/xpm/xpm_fifo/hdl/xpm_fifo.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_cdc/hdl/xpm_cdc.sv" \

vcom -work xpm -64 -93  \
"$XILINX_VIVADO/data/ip/xpm/xpm_VCOMP.vhd" \

vcom -work microblaze_v11_0_13 -64 -93  \
"../../../ipstatic/hdl/microblaze_v11_0_vh_rfs.vhd" \

vcom -work xil_defaultlib -64 -93  \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/bd_0/ip/ip_0/sim/bd_9c5e_microblaze_I_0.vhd" \

vcom -work lib_cdc_v1_0_3 -64 -93  \
"../../../ipstatic/hdl/lib_cdc_v1_0_rfs.vhd" \

vcom -work proc_sys_reset_v5_0_15 -64 -93  \
"../../../ipstatic/hdl/proc_sys_reset_v5_0_vh_rfs.vhd" \

vcom -work xil_defaultlib -64 -93  \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/bd_0/ip/ip_1/sim/bd_9c5e_rst_0_0.vhd" \

vcom -work lmb_v10_v3_0_14 -64 -93  \
"../../../ipstatic/hdl/lmb_v10_v3_0_vh_rfs.vhd" \

vcom -work xil_defaultlib -64 -93  \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/bd_0/ip/ip_2/sim/bd_9c5e_ilmb_0.vhd" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/bd_0/ip/ip_3/sim/bd_9c5e_dlmb_0.vhd" \

vcom -work lmb_bram_if_cntlr_v4_0_24 -64 -93  \
"../../../ipstatic/hdl/lmb_bram_if_cntlr_v4_0_vh_rfs.vhd" \

vcom -work xil_defaultlib -64 -93  \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/bd_0/ip/ip_4/sim/bd_9c5e_dlmb_cntlr_0.vhd" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/bd_0/ip/ip_5/sim/bd_9c5e_ilmb_cntlr_0.vhd" \

vlog -work blk_mem_gen_v8_4_8 -64 -incr -mfcu  "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/map" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/ip_top" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../ipstatic/simulation/blk_mem_gen_v8_4.v" \

vlog -work xil_defaultlib -64 -incr -mfcu  "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/map" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/ip_top" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/bd_0/ip/ip_6/sim/bd_9c5e_lmb_bram_I_0.v" \

vcom -work xil_defaultlib -64 -93  \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/bd_0/ip/ip_7/sim/bd_9c5e_second_dlmb_cntlr_0.vhd" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/bd_0/ip/ip_8/sim/bd_9c5e_second_ilmb_cntlr_0.vhd" \

vlog -work xil_defaultlib -64 -incr -mfcu  "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/map" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/ip_top" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/bd_0/ip/ip_9/sim/bd_9c5e_second_lmb_bram_I_0.v" \

vcom -work iomodule_v3_1_10 -64 -93  \
"../../../ipstatic/hdl/iomodule_v3_1_vh_rfs.vhd" \

vcom -work xil_defaultlib -64 -93  \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/bd_0/ip/ip_10/sim/bd_9c5e_iomodule_0_0.vhd" \

vlog -work xil_defaultlib -64 -incr -mfcu  "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/map" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/ip_top" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/bd_0/sim/bd_9c5e.v" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_0/sim/cl_ddr4_32g_ap_microblaze_mcs.v" \

vlog -work xil_defaultlib -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/map" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/ip_top" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/phy/cl_ddr4_32g_ap_phy_ddr4.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/phy/ddr4_phy_v2_2_xiphy_behav.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/phy/ddr4_phy_v2_2_xiphy.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/iob/ddr4_phy_v2_2_iob_byte.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/iob/ddr4_phy_v2_2_iob.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/clocking/ddr4_phy_v2_2_pll.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/xiphy_files/ddr4_phy_v2_2_xiphy_tristate_wrapper.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/xiphy_files/ddr4_phy_v2_2_xiphy_riuor_wrapper.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/xiphy_files/ddr4_phy_v2_2_xiphy_control_wrapper.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/xiphy_files/ddr4_phy_v2_2_xiphy_byte_wrapper.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/xiphy_files/ddr4_phy_v2_2_xiphy_bitslice_wrapper.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/ip_1/rtl/ip_top/cl_ddr4_32g_ap_phy.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_wtr.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_ref.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_rd_wr.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_periodic.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_group.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_ecc_merge_enc.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_ecc_gen.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_ecc_fi_xor.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_ecc_dec_fix.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_ecc_buf.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_ecc.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_ctl.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_cmd_mux_c.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_cmd_mux_ap.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_arb_p.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_arb_mux_p.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_arb_c.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_arb_a.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_act_timer.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc_act_rank.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/controller/ddr4_v2_2_mc.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/ui/ddr4_v2_2_ui_wr_data.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/ui/ddr4_v2_2_ui_rd_data.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/ui/ddr4_v2_2_ui_cmd.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/ui/ddr4_v2_2_ui.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_axi_ar_channel.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_axi_aw_channel.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_axi_b_channel.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_axi_cmd_arbiter.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_axi_cmd_fsm.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_axi_cmd_translator.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_axi_fifo.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_axi_incr_cmd.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_axi_r_channel.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_axi_w_channel.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_axi_wr_cmd_fsm.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_axi_wrap_cmd.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_a_upsizer.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_axi.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_axi_register_slice.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_axi_upsizer.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_axic_register_slice.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_carry_and.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_carry_latch_and.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_carry_latch_or.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_carry_or.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_command_fifo.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_comparator.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_comparator_sel.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_comparator_sel_static.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_r_upsizer.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi/ddr4_v2_2_w_upsizer.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi_ctrl/ddr4_v2_2_axi_ctrl_addr_decode.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi_ctrl/ddr4_v2_2_axi_ctrl_read.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi_ctrl/ddr4_v2_2_axi_ctrl_reg_bank.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi_ctrl/ddr4_v2_2_axi_ctrl_reg.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi_ctrl/ddr4_v2_2_axi_ctrl_top.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/axi_ctrl/ddr4_v2_2_axi_ctrl_write.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/clocking/ddr4_v2_2_infrastructure.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_cal_xsdb_bram.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_cal_write.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_cal_wr_byte.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_cal_wr_bit.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_cal_sync.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_cal_read.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_cal_rd_en.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_cal_pi.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_cal_mc_odt.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_cal_debug_microblaze.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_cal_cplx_data.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_cal_cplx.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_cal_config_rom.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_cal_addr_decode.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_cal_top.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_cal_xsdb_arbiter.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_cal.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_chipscope_xsdb_slave.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/ddr4_v2_2_dp_AB9.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/ip_top/cl_ddr4_32g_ap_ddr4.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/ip_top/cl_ddr4_32g_ap_ddr4_mem_intfc.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/cal/cl_ddr4_32g_ap_ddr4_cal_riu.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/rtl/ip_top/cl_ddr4_32g_ap.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_ddr4_32g_ap/tb/cl_ddr4_32g_ap_microblaze_mcs_0.sv" \

vlog -work xil_defaultlib \
"glbl.v"

