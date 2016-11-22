xv_path=$XILINX_VIVADO

vivado -mode batch -source vivado_gen_complib.tcl

#KIRAN# ip_user_dir="../../../design/rtl/minotaur_test/minotaur_test.ip_user_files/ipstatic"
#KIRAN# ip_dir="../../../design/rtl/minotaur_test/minotaur_test.srcs/sources_1/ip"
#KIRAN# 
#KIRAN# venom_ip_user_dir="../../../design/rtl/venom/venom.ip_user_files/ipstatic"
#KIRAN# venom_ip_dir="../../../design/rtl/venom/venom.srcs/sources_1/ip"
#KIRAN# 

lib_base_dir=${QUESTA_COMPLIB_DIR}
venom_cl_ip_user_dir="../../../design/rtl/${DESIGN_NAME}/${DESIGN_NAME}.ip_user_files/ipstatic"
venom_cl_ip_dir="../../../design/rtl/${DESIGN_NAME}/${DESIGN_NAME}.srcs/sources_1/ip"

#KIRAN# bu_ip_user_dir="../../../design/rtl/bringup_slow/bringup_slow.ip_user_files/ipstatic"
#KIRAN# 
#KIRAN# vmap secureip $lib_base_dir/secureip
#KIRAN# vmap unisim   $lib_base_dir/unisim
#KIRAN# vmap unimacro $lib_base_dir/unimacro
#KIRAN# vmap unifast  $lib_base_dir/unifast
#KIRAN# vmap unisims_ver  $lib_base_dir/unisims_ver
#KIRAN# vmap unimacro_ver $lib_base_dir/unimacro_ver
#KIRAN# vmap unifast_ver  $lib_base_dir/unifast_ver
#KIRAN# vmap simprims_ver $lib_base_dir/simprims_ver
#KIRAN# 
#KIRAN# vmap xil_defaultlib $lib_base_dir/xil_defaultlib
#KIRAN# vmap fifo_generator_v13_1_0 $lib_base_dir/fifo_generator_v13_1_0

vmap fifo_generator_v13_1_2 $lib_base_dir/fifo_generator_v13_1_2

#KIRAN# #ifndef HDK_DELIVERY
#KIRAN# vmap dist_mem_gen_v8_0_10 $lib_base_dir/dist_mem_gen_v8_0_10
#KIRAN# vmap lib_pkg_v1_0_2 $lib_base_dir/lib_pkg_v1_0_2
#KIRAN# vmap lib_cdc_v1_0_2 $lib_base_dir/lib_cdc_v1_0_2
#KIRAN# vmap lib_srl_fifo_v1_0_2 $lib_base_dir/lib_srl_fifo_v1_0_2
#KIRAN# vmap fifo_generator_v13_1_1 $lib_base_dir/fifo_generator_v13_1_1
#KIRAN# vmap lib_fifo_v1_0_4 $lib_base_dir/lib_fifo_v1_0_4
#KIRAN# vmap axi_lite_ipif_v3_0_3 $lib_base_dir/axi_lite_ipif_v3_0_3
#KIRAN# vmap interrupt_control_v3_1_3 $lib_base_dir/interrupt_control_v3_1_3
#KIRAN# vmap axi_quad_spi_v3_2_7 $lib_base_dir/axi_quad_spi_v3_2_7
#KIRAN# #endif
#KIRAN# 
#KIRAN# 
#KIRAN# 
#KIRAN# vlib $lib_base_dir/xil_defaultlib 
#KIRAN# vlog -64 -incr -sv -work $lib_base_dir/xil_defaultlib  \
#KIRAN# $XILINX_VIVADO/data/ip/xpm/xpm_cdc/hdl/xpm_cdc.sv \
#KIRAN# $XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory.sv \
#KIRAN# 2>&1 | tee -a create_libs.vcom.log
#KIRAN# 
#KIRAN# #2016.2#$XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory_base.sv \
#KIRAN# #2016.2#$XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory_dpdistram.sv \
#KIRAN# #2016.2#$XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory_dprom.sv \
#KIRAN# #2016.2#$XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory_sdpram.sv \
#KIRAN# #2016.2#$XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory_spram.sv \
#KIRAN# #2016.2#$XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory_sprom.sv \
#KIRAN# #2016.2#$XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory_tdpram.sv \
#KIRAN# 
#KIRAN# vlib $lib_base_dir/xpm 
#KIRAN# vmap xpm $lib_base_dir/xpm
#KIRAN# vcom -64 -93 -work $lib_base_dir/xpm  \
#KIRAN# "$XILINX_VIVADO/data/ip/xpm/xpm_VCOMP.vhd" \
#KIRAN# 2>&1 | tee -a create_libs.vcom.log
#KIRAN# 
#KIRAN# #ifndef HDK_DELIVERY
#KIRAN# 
#KIRAN# #########################################################
#KIRAN# ## Library: fifo_generator_v13_1_0
#KIRAN# #########################################################
#KIRAN# vlib $lib_base_dir/fifo_generator_v13_1_0
#KIRAN# 
#KIRAN# vlog -64 -incr -work $lib_base_dir/fifo_generator_v13_1_0  \
#KIRAN# "$ip_user_dir/fifo_generator_v13_1_0/simulation/fifo_generator_vlog_beh.v" \
#KIRAN# 2>&1 | tee -a create_libs.vcom.log
#KIRAN# 
#KIRAN# vcom -64 -93 -work $lib_base_dir/fifo_generator_v13_1_0  \
#KIRAN# "$ip_user_dir/fifo_generator_v13_1_0/hdl/fifo_generator_v13_1_rfs.vhd" \
#KIRAN# 2>&1 | tee -a create_libs.vcom.log
#KIRAN# 
#KIRAN# vlog -64 -incr -work $lib_base_dir/fifo_generator_v13_1_0  \
#KIRAN# "$ip_user_dir/fifo_generator_v13_1_0/hdl/fifo_generator_v13_1_rfs.v" \
#KIRAN# 2>&1 | tee -a create_libs.vcom.log
#KIRAN# 

#########################################################
## Library: fifo_generator_v13_1_2
#########################################################
vlib $lib_base_dir/fifo_generator_v13_1_2

vlog -64 -incr -work $lib_base_dir/fifo_generator_v13_1_2  \
"$venom_cl_ip_user_dir/simulation/fifo_generator_vlog_beh.v" \
2>&1 | tee -a create_libs.vcom.log

vcom -64 -93 -work $lib_base_dir/fifo_generator_v13_1_2  \
"$venom_cl_ip_user_dir/hdl/fifo_generator_v13_1_rfs.vhd" \
2>&1 | tee -a create_libs.vcom.log

vlog -64 -incr -work $lib_base_dir/fifo_generator_v13_1_2  \
"$venom_cl_ip_user_dir/hdl/fifo_generator_v13_1_rfs.v" \
2>&1 | tee -a create_libs.vcom.log

#KIRAN# #########################################################
#KIRAN# ## Library: fifo_generator_v13_1_1
#KIRAN# #########################################################
#KIRAN# vlib $lib_base_dir/fifo_generator_v13_1_1
#KIRAN# 
#KIRAN# vlog -64 -incr -work $lib_base_dir/fifo_generator_v13_1_1  \
#KIRAN# "$venom_cl_ip_user_dir/fifo_generator_v13_1_1/simulation/fifo_generator_vlog_beh.v" \
#KIRAN# 2>&1 | tee -a create_libs.vcom.log
#KIRAN# 
#KIRAN# vcom -64 -93 -work $lib_base_dir/fifo_generator_v13_1_1  \
#KIRAN# "$venom_cl_ip_user_dir/fifo_generator_v13_1_1/hdl/fifo_generator_v13_1_rfs.vhd" \
#KIRAN# 2>&1 | tee -a create_libs.vcom.log
#KIRAN# 
#KIRAN# vlog -64 -incr -work $lib_base_dir/fifo_generator_v13_1_1  \
#KIRAN# "$venom_cl_ip_user_dir/fifo_generator_v13_1_1/hdl/fifo_generator_v13_1_rfs.v" \
#KIRAN# 2>&1 | tee -a create_libs.vcom.log
#KIRAN# 
#KIRAN# #########################################################
#KIRAN# ## Library: axi_clock_converter_v2_1_8
#KIRAN# #########################################################
#KIRAN# vlib $lib_base_dir/axi_clock_converter_v2_1_8
#KIRAN# vmap axi_clock_coverter_v2_1_8 $lib_base_dir/axi_clock_converter_v2_1_8
#KIRAN# vlog -64 -incr -work $lib_base_dir/axi_clock_converter_v2_1_8  \
#KIRAN# "$venom_cl_ip_user_dir/axi_clock_converter_v2_1_8/hdl/verilog/axi_clock_converter_v2_1_axic_sync_clock_converter.v" \
#KIRAN# "$venom_cl_ip_user_dir/axi_clock_converter_v2_1_8/hdl/verilog/axi_clock_converter_v2_1_axic_sample_cycle_ratio.v" \
#KIRAN# "$venom_cl_ip_user_dir/axi_clock_converter_v2_1_8/hdl/verilog/axi_clock_converter_v2_1_axi_clock_converter.v" \
#KIRAN# 
#KIRAN# 
#KIRAN# vlog -work xil_defaultlib \
#KIRAN# "$venom_cl_ip_dir/axi_clock_converter_512/sim/axi_clock_converter_512.v" \
#KIRAN# 
#KIRAN# ## Library: dist_mem_gen_v8_0_10
#KIRAN# #########################################################
#KIRAN# vlib $lib_base_dir/dist_mem_gen_v8_0_10
#KIRAN# vlog -64 -incr -work $lib_base_dir/dist_mem_gen_v8_0_10  \
#KIRAN# "$ip_user_dir/dist_mem_gen_v8_0_10/simulation/dist_mem_gen_v8_0.v" \
#KIRAN# 2>&1 | tee -a create_libs.vcom.log
#KIRAN# 
#KIRAN# #########################################################
#KIRAN# ## Library: lib_cdc_v1_0_2
#KIRAN# #########################################################
#KIRAN# vlib $lib_base_dir/lib_cdc_v1_0_2
#KIRAN# vmap lib_cdc_v1_0_2 $lib_base_dir/lib_cdc_v1_0_2
#KIRAN# vcom $vhdl_opts -work $lib_base_dir/lib_cdc_v1_0_2  \
#KIRAN# "$ip_user_dir/lib_cdc_v1_0_2/hdl/src/vhdl/cdc_sync.vhd" \
#KIRAN# 2>&1 | tee -a create_libs.vcom.log
#KIRAN# 
#KIRAN# #########################################################
#KIRAN# ## Library: lib_pkg_v1_0_2
#KIRAN# #########################################################
#KIRAN# vlib $lib_base_dir/lib_pkg_v1_0_2
#KIRAN# vcom $vhdl_opts -work $lib_base_dir/lib_pkg_v1_0_2  \
#KIRAN# "$ip_user_dir/lib_pkg_v1_0_2/hdl/src/vhdl/lib_pkg.vhd" \
#KIRAN# 2>&1 | tee -a create_libs.vcom.log
#KIRAN# 
#KIRAN# #########################################################
#KIRAN# ## Library: lib_srl_fifo_v1_0_2
#KIRAN# #########################################################
#KIRAN# vlib $lib_base_dir/lib_srl_fifo_v1_0_2
#KIRAN# vmap lib_srl_fifo_v1_0_2 $lib_base_dir/lib_srl_fifo_v1_0_2
#KIRAN# vcom -work $lib_base_dir/lib_srl_fifo_v1_0_2 -64 \
#KIRAN#   "$ip_user_dir/lib_srl_fifo_v1_0_2/hdl/src/vhdl/cntr_incr_decr_addn_f.vhd" \
#KIRAN#   "$ip_user_dir/lib_srl_fifo_v1_0_2/hdl/src/vhdl/dynshreg_f.vhd" \
#KIRAN#   "$ip_user_dir/lib_srl_fifo_v1_0_2/hdl/src/vhdl/srl_fifo_rbu_f.vhd" \
#KIRAN#   "$ip_user_dir/lib_srl_fifo_v1_0_2/hdl/src/vhdl/srl_fifo_f.vhd" \
#KIRAN# 2>&1 | tee -a create_libs.vcom.log
#KIRAN# 
#KIRAN# #########################################################
#KIRAN# ## Library: lib_fifo_v1_0_4
#KIRAN# #########################################################
#KIRAN# vlib $lib_base_dir/lib_fifo_v1_0_4
#KIRAN# vmap lib_fifo_v1_0_4 $lib_base_dir/lib_fifo_v1_0_4
#KIRAN# vcom $vhdl_opts -work $lib_base_dir/lib_fifo_v1_0_4  \
#KIRAN# "$ip_user_dir/lib_fifo_v1_0_4/hdl/src/vhdl/async_fifo_fg.vhd" \
#KIRAN# "$ip_user_dir/lib_fifo_v1_0_4/hdl/src/vhdl/sync_fifo_fg.vhd" \
#KIRAN# 2>&1 | tee -a create_libs.vcom.log
#KIRAN# 
#KIRAN# axi_hwicap_dir="../../../design/rtl/bringup_slow/bringup_slow.srcs/sources_1/ip/axi_hwicap_0"
#KIRAN# #########################################################
#KIRAN# ## Library: axi_lite_ipif_v3_0_3
#KIRAN# #########################################################
#KIRAN# vlib $lib_base_dir/axi_lite_ipif_v3_0_3
#KIRAN# vcom $vhdl_opts -work $lib_base_dir/axi_lite_ipif_v3_0_3  \
#KIRAN# "$ip_user_dir/axi_lite_ipif_v3_0_3/hdl/src/vhdl/ipif_pkg.vhd" \
#KIRAN# "$ip_user_dir/axi_lite_ipif_v3_0_3/hdl/src/vhdl/pselect_f.vhd" \
#KIRAN# "$ip_user_dir/axi_lite_ipif_v3_0_3/hdl/src/vhdl/address_decoder.vhd" \
#KIRAN# "$ip_user_dir/axi_lite_ipif_v3_0_3/hdl/src/vhdl/slave_attachment.vhd" \
#KIRAN# "$ip_user_dir/axi_lite_ipif_v3_0_3/hdl/src/vhdl/axi_lite_ipif.vhd" \
#KIRAN# 2>&1 | tee -a create_libs.vcom.log
#KIRAN# 
#KIRAN# 
#KIRAN# #########################################################
#KIRAN# ## Library: interrupt_control_v3_1_3
#KIRAN# #########################################################
#KIRAN# vlib $lib_base_dir/interrupt_control_v3_1_3
#KIRAN# vcom $vhdl_opts -work $lib_base_dir/interrupt_control_v3_1_3  \
#KIRAN# "$ip_user_dir/interrupt_control_v3_1_3/hdl/src/vhdl/interrupt_control.vhd" \
#KIRAN# 2>&1 | tee -a create_libs.vcom.log
#KIRAN# 
#KIRAN# 
#KIRAN# #########################################################
#KIRAN# ## Library: axi_hwicap_v3_0_12 
#KIRAN# #########################################################
#KIRAN# vlib  $lib_base_dir/axi_hwicap_v3_0_12
#KIRAN# vmap axi_hwicap_v3_0_12 $lib_base_dir/axi_hwicap_v3_0_12
#KIRAN# vcom -64 -93 -work $lib_base_dir/axi_hwicap_v3_0_12  \
#KIRAN# "$bu_ip_user_dir/axi_hwicap_v3_0_12/hdl/src/vhdl/ipic_if.vhd" \
#KIRAN# "$bu_ip_user_dir/axi_hwicap_v3_0_12/hdl/src/vhdl/icap_statemachine.vhd" \
#KIRAN# "$bu_ip_user_dir/axi_hwicap_v3_0_12/hdl/src/vhdl/icap_statemachine_shared.vhd" \
#KIRAN# "$bu_ip_user_dir/axi_hwicap_v3_0_12/hdl/src/vhdl/hwicap.vhd" \
#KIRAN# "$bu_ip_user_dir/axi_hwicap_v3_0_12/hdl/src/vhdl/hwicap_shared.vhd" \
#KIRAN# "$bu_ip_user_dir/axi_hwicap_v3_0_12/hdl/src/vhdl/axi_hwicap.vhd" \
#KIRAN# 
#KIRAN# vcom -64 -93 -work $lib_base_dir/xil_defaultlib  \
#KIRAN# "$ip_user_dir/axi_hwicap_0/sim/axi_hwicap_0.vhd" \
#KIRAN# 
#KIRAN# 
#KIRAN# #########################################################
#KIRAN# ## Library: axi_quad_spi_v3_2_7
#KIRAN# #########################################################
#KIRAN# vlib $lib_base_dir/axi_quad_spi_v3_2_7
#KIRAN# vcom -work $lib_base_dir/axi_quad_spi_v3_2_7 $vhdl_opts \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/comp_defs.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/pselect_f.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/counter_f.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/soft_reset.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/xip_cross_clk_sync.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/reset_sync_module.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/qspi_status_slave_sel_reg.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/qspi_startup_block.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/qspi_receive_transmit_reg.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/qspi_occupancy_reg.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/qspi_mode_control_logic.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/qspi_mode_0_module.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/qspi_look_up_logic.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/qspi_fifo_ifmodule.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/qspi_cntrl_reg.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/qspi_address_decoder.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/cross_clk_sync_fifo_1.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/cross_clk_sync_fifo_0.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/xip_status_reg.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/xip_cntrl_reg.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/qspi_core_interface.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/axi_qspi_xip_if.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/axi_qspi_enhanced_mode.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/axi_quad_spi_v3_2_7/hdl/src/vhdl/axi_quad_spi.vhd" \
#KIRAN#   "$ip_dir/axi_quad_spi_0/sim/axi_quad_spi_0.vhd" \
#KIRAN# 2>&1 | tee -a create_libs.vcom.log
#KIRAN# 
#KIRAN# #endif
