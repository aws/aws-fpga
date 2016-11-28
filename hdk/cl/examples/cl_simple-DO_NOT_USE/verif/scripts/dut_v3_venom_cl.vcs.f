
-y $XILINX_VIVADO/data/verilog/src/unisims
+incdir+$XILINX_VIVADO/data/verilog/src
$XILINX_VIVADO/data/verilog/src/glbl.v
-y $XILINX_VIVADO/data/verilog/src/retarget

-v $XILINX_VIVADO/data/ip/xpm/xpm_cdc/hdl/xpm_cdc.sv
$IMPORT_DESIGN_DIR/cl/cl_simple_defines.vh

-y $IMPORT_DESIGN_DIR/mgt
-y $IMPORT_DESIGN_DIR/lib
-y $IMPORT_DESIGN_DIR/cl
-y $IMPORT_DESIGN_DIR/sh
+incdir+$IMPORT_DESIGN_DIR/lib

#PCIe or XDMA
#-f $SCRIPTS_DIR/dut_venom_cl_pcie.f
-f $SCRIPTS_DIR/dut_venom_cl_xdma.f

#HMC

# DDR
+incdir+$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/ip_top
+incdir+$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal
+incdir+$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/ip_1/rtl/map

$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/ip_1/rtl/phy/ddr4_phy_v2_1_xiphy_behav.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/ip_1/rtl/phy/ddr4_phy_v2_1_xiphy.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/ip_1/rtl/iob/ddr4_phy_v2_1_iob_byte.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/ip_1/rtl/iob/ddr4_phy_v2_1_iob.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/ip_1/rtl/clocking/ddr4_phy_v2_1_pll.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/ip_1/rtl/xiphy_files/ddr4_phy_v2_1_xiphy_tristate_wrapper.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/ip_1/rtl/xiphy_files/ddr4_phy_v2_1_xiphy_riuor_wrapper.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/ip_1/rtl/xiphy_files/ddr4_phy_v2_1_xiphy_control_wrapper.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/ip_1/rtl/xiphy_files/ddr4_phy_v2_1_xiphy_byte_wrapper.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/ip_1/rtl/xiphy_files/ddr4_phy_v2_1_xiphy_bitslice_wrapper.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/ip_1/rtl/phy/ddr4_core_phy_ddr4.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/ip_1/rtl/ip_top/ddr4_core_phy.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_wtr.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_ref.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_rd_wr.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_periodic.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_group.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_ecc_merge_enc.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_ecc_gen.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_ecc_fi_xor.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_ecc_dec_fix.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_ecc_buf.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_ecc.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_ctl.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_cmd_mux_c.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_cmd_mux_ap.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_arb_p.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_arb_mux_p.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_arb_c.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_arb_a.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_act_timer.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc_act_rank.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/controller/ddr4_v2_1_mc.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/ui/ddr4_v2_1_ui_wr_data.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/ui/ddr4_v2_1_ui_rd_data.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/ui/ddr4_v2_1_ui_cmd.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/ui/ddr4_v2_1_ui.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_axi_ar_channel.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_axi_aw_channel.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_axi_b_channel.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_axi_cmd_arbiter.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_axi_cmd_fsm.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_axi_cmd_translator.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_axi_fifo.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_axi_incr_cmd.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_axi_r_channel.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_axi_w_channel.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_axi_wr_cmd_fsm.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_axi_wrap_cmd.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_a_upsizer.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_axi.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_axi_register_slice.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_axi_upsizer.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_axic_register_slice.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_carry_and.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_carry_latch_and.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_carry_latch_or.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_carry_or.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_command_fifo.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_comparator.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_comparator_sel.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_comparator_sel_static.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_r_upsizer.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi/ddr4_v2_1_w_upsizer.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi_ctrl/ddr4_v2_1_axi_ctrl_addr_decode.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi_ctrl/ddr4_v2_1_axi_ctrl_read.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi_ctrl/ddr4_v2_1_axi_ctrl_reg_bank.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi_ctrl/ddr4_v2_1_axi_ctrl_reg.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi_ctrl/ddr4_v2_1_axi_ctrl_top.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/axi_ctrl/ddr4_v2_1_axi_ctrl_write.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/clocking/ddr4_v2_1_infrastructure.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_xsdb_bram.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_write.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_wr_byte.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_wr_bit.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_sync.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_core_ddr4_cal_riu.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_read.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_rd_en.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_pi.sv
#$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_odt.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_mc_odt.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_debug_microblaze.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_cplx_data.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_cplx.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_config_rom.sv
#$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_bfifo.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_addr_decode.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_top.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal_xsdb_arbiter.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_cal.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_chipscope_xsdb_slave.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/cal/ddr4_v2_1_dp_AB9.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/ip_top/ddr4_core.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/ip_top/ddr4_core_ddr4.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/rtl/ip_top/ddr4_core_ddr4_mem_intfc.sv
$DESIGN_DIR/$DESIGN_NAME/$DESIGN_NAME.srcs/sources_1/ip/ddr4_core/tb/microblaze_mcs_0.sv

#System management

#Aurora
+incdir+$IMPORT_DESIGN_DIR/sh


+incdir+$IMPORT_DESIGN_DIR/cl/
$IMPORT_DESIGN_DIR/cl/cl_simple.sv
$IMPORT_DESIGN_DIR/cl/cl_tst.sv
$IMPORT_DESIGN_DIR/cl/cl_tst_scrb.sv
$IMPORT_DESIGN_DIR/cl/mem_scrb.sv


-y $IMPORT_DESIGN_DIR/top
