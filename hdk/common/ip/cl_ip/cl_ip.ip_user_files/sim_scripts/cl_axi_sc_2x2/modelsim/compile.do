vlib modelsim_lib/work
vlib modelsim_lib/msim

vlib modelsim_lib/msim/xilinx_vip
vlib modelsim_lib/msim/xpm
vlib modelsim_lib/msim/xlconstant_v1_1_9
vlib modelsim_lib/msim/xil_defaultlib
vlib modelsim_lib/msim/lib_cdc_v1_0_3
vlib modelsim_lib/msim/proc_sys_reset_v5_0_15
vlib modelsim_lib/msim/smartconnect_v1_0
vlib modelsim_lib/msim/axi_infrastructure_v1_1_0
vlib modelsim_lib/msim/axi_register_slice_v2_1_31
vlib modelsim_lib/msim/axi_vip_v1_1_17

vmap xilinx_vip modelsim_lib/msim/xilinx_vip
vmap xpm modelsim_lib/msim/xpm
vmap xlconstant_v1_1_9 modelsim_lib/msim/xlconstant_v1_1_9
vmap xil_defaultlib modelsim_lib/msim/xil_defaultlib
vmap lib_cdc_v1_0_3 modelsim_lib/msim/lib_cdc_v1_0_3
vmap proc_sys_reset_v5_0_15 modelsim_lib/msim/proc_sys_reset_v5_0_15
vmap smartconnect_v1_0 modelsim_lib/msim/smartconnect_v1_0
vmap axi_infrastructure_v1_1_0 modelsim_lib/msim/axi_infrastructure_v1_1_0
vmap axi_register_slice_v2_1_31 modelsim_lib/msim/axi_register_slice_v2_1_31
vmap axi_vip_v1_1_17 modelsim_lib/msim/axi_vip_v1_1_17

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

vlog -work xpm -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"$XILINX_VIVADO/data/ip/xpm/xpm_fifo/hdl/xpm_fifo.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_cdc/hdl/xpm_cdc.sv" \

vcom -work xpm -64 -93  \
"$XILINX_VIVADO/data/ip/xpm/xpm_VCOMP.vhd" \

vlog -work xlconstant_v1_1_9 -64 -incr -mfcu  "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/e2d2/hdl/xlconstant_v1_1_vl_rfs.v" \

vlog -work xil_defaultlib -64 -incr -mfcu  "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_0/sim/bd_1096_one_0.v" \

vcom -work lib_cdc_v1_0_3 -64 -93  \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/2a4f/hdl/lib_cdc_v1_0_rfs.vhd" \

vcom -work proc_sys_reset_v5_0_15 -64 -93  \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/3a26/hdl/proc_sys_reset_v5_0_vh_rfs.vhd" \

vcom -work xil_defaultlib -64 -93  \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_1/sim/bd_1096_psr_aclk_0.vhd" \

vlog -work smartconnect_v1_0 -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/sc_util_v1_0_vl_rfs.sv" \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/3718/hdl/sc_switchboard_v1_0_vl_rfs.sv" \

vlog -work xil_defaultlib -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_2/sim/bd_1096_arsw_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_3/sim/bd_1096_rsw_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_4/sim/bd_1096_awsw_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_5/sim/bd_1096_wsw_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_6/sim/bd_1096_bsw_0.sv" \

vlog -work smartconnect_v1_0 -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/98d8/hdl/sc_mmu_v1_0_vl_rfs.sv" \

vlog -work xil_defaultlib -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_7/sim/bd_1096_s00mmu_0.sv" \

vlog -work smartconnect_v1_0 -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/2da8/hdl/sc_transaction_regulator_v1_0_vl_rfs.sv" \

vlog -work xil_defaultlib -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_8/sim/bd_1096_s00tr_0.sv" \

vlog -work smartconnect_v1_0 -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/a950/hdl/sc_si_converter_v1_0_vl_rfs.sv" \

vlog -work xil_defaultlib -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_9/sim/bd_1096_s00sic_0.sv" \

vlog -work smartconnect_v1_0 -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/cef3/hdl/sc_axi2sc_v1_0_vl_rfs.sv" \

vlog -work xil_defaultlib -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_10/sim/bd_1096_s00a2s_0.sv" \

vlog -work smartconnect_v1_0 -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/sc_node_v1_0_vl_rfs.sv" \

vlog -work xil_defaultlib -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_11/sim/bd_1096_sarn_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_12/sim/bd_1096_srn_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_13/sim/bd_1096_sawn_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_14/sim/bd_1096_swn_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_15/sim/bd_1096_sbn_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_16/sim/bd_1096_s01mmu_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_17/sim/bd_1096_s01tr_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_18/sim/bd_1096_s01sic_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_19/sim/bd_1096_s01a2s_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_20/sim/bd_1096_sarn_1.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_21/sim/bd_1096_srn_1.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_22/sim/bd_1096_sawn_1.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_23/sim/bd_1096_swn_1.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_24/sim/bd_1096_sbn_1.sv" \

vlog -work smartconnect_v1_0 -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/7f4f/hdl/sc_sc2axi_v1_0_vl_rfs.sv" \

vlog -work xil_defaultlib -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_25/sim/bd_1096_m00s2a_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_26/sim/bd_1096_m00arn_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_27/sim/bd_1096_m00rn_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_28/sim/bd_1096_m00awn_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_29/sim/bd_1096_m00wn_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_30/sim/bd_1096_m00bn_0.sv" \

vlog -work smartconnect_v1_0 -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/1f04/hdl/sc_exit_v1_0_vl_rfs.sv" \

vlog -work xil_defaultlib -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_31/sim/bd_1096_m00e_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_32/sim/bd_1096_m01s2a_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_33/sim/bd_1096_m01arn_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_34/sim/bd_1096_m01rn_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_35/sim/bd_1096_m01awn_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_36/sim/bd_1096_m01wn_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_37/sim/bd_1096_m01bn_0.sv" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/ip/ip_38/sim/bd_1096_m01e_0.sv" \

vlog -work xil_defaultlib -64 -incr -mfcu  "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/bd_0/sim/bd_1096.v" \

vlog -work axi_infrastructure_v1_1_0 -64 -incr -mfcu  "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl/axi_infrastructure_v1_1_vl_rfs.v" \

vlog -work axi_register_slice_v2_1_31 -64 -incr -mfcu  "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/92b2/hdl/axi_register_slice_v2_1_vl_rfs.v" \

vlog -work axi_vip_v1_1_17 -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/4d04/hdl/axi_vip_v1_1_vl_rfs.sv" \

vlog -work xil_defaultlib -64 -incr -mfcu  "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_2x2/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../bd/cl_axi_sc_2x2/ip/cl_axi_sc_2x2_smartconnect_0_0/sim/cl_axi_sc_2x2_smartconnect_0_0.v" \
"../../../bd/cl_axi_sc_2x2/sim/cl_axi_sc_2x2.v" \

vlog -work xil_defaultlib \
"glbl.v"

