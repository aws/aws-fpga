vlib questa_lib/work
vlib questa_lib/msim

vlib questa_lib/msim/xilinx_vip
vlib questa_lib/msim/xpm
vlib questa_lib/msim/gtwizard_ultrascale_v1_7_18
vlib questa_lib/msim/xil_defaultlib
vlib questa_lib/msim/blk_mem_gen_v8_4_8
vlib questa_lib/msim/xdma_v4_1_29

vmap xilinx_vip questa_lib/msim/xilinx_vip
vmap xpm questa_lib/msim/xpm
vmap gtwizard_ultrascale_v1_7_18 questa_lib/msim/gtwizard_ultrascale_v1_7_18
vmap xil_defaultlib questa_lib/msim/xil_defaultlib
vmap blk_mem_gen_v8_4_8 questa_lib/msim/blk_mem_gen_v8_4_8
vmap xdma_v4_1_29 questa_lib/msim/xdma_v4_1_29

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

vlog -work xpm -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source" "+incdir+../../../ipstatic/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"$XILINX_VIVADO/data/ip/xpm/xpm_fifo/hdl/xpm_fifo.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_cdc/hdl/xpm_cdc.sv" \

vcom -work xpm -64 -93  \
"$XILINX_VIVADO/data/ip/xpm/xpm_VCOMP.vhd" \

vlog -work gtwizard_ultrascale_v1_7_18 -64 -incr -mfcu  "+incdir+../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source" "+incdir+../../../ipstatic/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_bit_sync.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gte4_drp_arb.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gthe4_delay_powergood.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gtye4_delay_powergood.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gthe3_cpll_cal.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gthe3_cal_freqcnt.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gthe4_cpll_cal.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gthe4_cpll_cal_rx.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gthe4_cpll_cal_tx.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gthe4_cal_freqcnt.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gtye4_cpll_cal.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gtye4_cpll_cal_rx.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gtye4_cpll_cal_tx.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gtye4_cal_freqcnt.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gtwiz_buffbypass_rx.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gtwiz_buffbypass_tx.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gtwiz_reset.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gtwiz_userclk_rx.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gtwiz_userclk_tx.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gtwiz_userdata_rx.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_gtwiz_userdata_tx.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_reset_sync.v" \
"../../../ipstatic/hdl/gtwizard_ultrascale_v1_7_reset_inv_sync.v" \

vlog -work xil_defaultlib -64 -incr -mfcu  "+incdir+../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source" "+incdir+../../../ipstatic/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/ip_0/sim/gtwizard_ultrascale_v1_7_gtye4_channel.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/ip_0/sim/pcie_bridge_ep_pcie4c_ip_gt_gtye4_channel_wrapper.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/ip_0/sim/gtwizard_ultrascale_v1_7_gtye4_common.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/ip_0/sim/pcie_bridge_ep_pcie4c_ip_gt_gtye4_common_wrapper.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/ip_0/sim/pcie_bridge_ep_pcie4c_ip_gt_gtwizard_gtye4.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/ip_0/sim/pcie_bridge_ep_pcie4c_ip_gt_gtwizard_top.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/ip_0/sim/pcie_bridge_ep_pcie4c_ip_gt.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_cxs_remap.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_512b_async_fifo.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_512b_cc_intfc.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_512b_cc_output_mux.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_512b_cq_intfc.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_512b_cq_output_mux.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_512b_intfc_int.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_512b_intfc.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_512b_rc_intfc.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_512b_rc_output_mux.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_512b_rq_intfc.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_512b_rq_output_mux.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_512b_sync_fifo.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_bram_16k_int.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_bram_16k.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_bram_32k.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_bram_4k_int.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_bram_msix.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_bram_rep_int.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_bram_rep.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_bram_tph.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_bram.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_gtwizard_top.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_phy_ff_chain.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_gen4_fast2slow.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_gen4_rx_64b_bridge.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_gen4_tx_64b_bridge.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_gen4_perlane_64b_bridge.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_gen4_tx_eq_bridge.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_gen4_perlane_eq_bridge.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_phy_pipeline.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_gt_gt_channel.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_gt_gt_common.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_gt_phy_clk.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_gt_phy_rst.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_gt_phy_rxeq.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_gt_phy_txeq.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_sync_cell.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_sync.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_gt_cdr_ctrl_on_eidle.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_gt_receiver_detect_rxterm.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_gt_phy_wrapper.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_phy_top.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_init_ctrl.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_pl_eq.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_vf_decode.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_vf_decode_attr.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_pipe.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_seqnum_fifo.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_sys_clk_gen_ps.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source/pcie_bridge_ep_pcie4c_ip_pcie4c_uscale_core_top.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/sim/pcie_bridge_ep_pcie4c_ip.v" \

vlog -work blk_mem_gen_v8_4_8 -64 -incr -mfcu  "+incdir+../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source" "+incdir+../../../ipstatic/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../ipstatic/ip_1/simulation/blk_mem_gen_v8_4.v" \

vlog -work xil_defaultlib -64 -incr -mfcu  "+incdir+../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source" "+incdir+../../../ipstatic/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_1/sim/xdma_v4_1_29_blk_mem_64_reg_be.v" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_2/sim/xdma_v4_1_29_blk_mem_64_noreg_be.v" \

vlog -work xdma_v4_1_29 -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source" "+incdir+../../../ipstatic/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../ipstatic/hdl/xdma_v4_1_vl_rfs.sv" \

vlog -work xil_defaultlib -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/ip_0/source" "+incdir+../../../ipstatic/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/xdma_v4_1/hdl/verilog/pcie_bridge_ep_dma_bram_wrap.sv" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/xdma_v4_1/hdl/verilog/pcie_bridge_ep_dma_bram_wrap_1024.sv" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/xdma_v4_1/hdl/verilog/pcie_bridge_ep_dma_bram_wrap_2048.sv" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/xdma_v4_1/hdl/verilog/pcie_bridge_ep_core_top.sv" \
"../../../../cl_ip.gen/sources_1/ip/pcie_bridge_ep/sim/pcie_bridge_ep.sv" \

vlog -work xil_defaultlib \
"glbl.v"

