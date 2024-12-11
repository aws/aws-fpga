transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

vlib work
vlib riviera/xilinx_vip
vlib riviera/xpm
vlib riviera/xlconstant_v1_1_9
vlib riviera/xil_defaultlib
vlib riviera/lib_cdc_v1_0_3
vlib riviera/proc_sys_reset_v5_0_15
vlib riviera/smartconnect_v1_0
vlib riviera/axi_infrastructure_v1_1_0
vlib riviera/axi_register_slice_v2_1_31
vlib riviera/axi_vip_v1_1_17

vmap xilinx_vip riviera/xilinx_vip
vmap xpm riviera/xpm
vmap xlconstant_v1_1_9 riviera/xlconstant_v1_1_9
vmap xil_defaultlib riviera/xil_defaultlib
vmap lib_cdc_v1_0_3 riviera/lib_cdc_v1_0_3
vmap proc_sys_reset_v5_0_15 riviera/proc_sys_reset_v5_0_15
vmap smartconnect_v1_0 riviera/smartconnect_v1_0
vmap axi_infrastructure_v1_1_0 riviera/axi_infrastructure_v1_1_0
vmap axi_register_slice_v2_1_31 riviera/axi_register_slice_v2_1_31
vmap axi_vip_v1_1_17 riviera/axi_vip_v1_1_17

vlog -work xilinx_vip  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_axi4streampc.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_axi4pc.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/xil_common_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/clk_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/rst_vip_if.sv" \

vlog -work xpm  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"$XILINX_VIVADO/data/ip/xpm/xpm_fifo/hdl/xpm_fifo.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_cdc/hdl/xpm_cdc.sv" \

vcom -work xpm -93  -incr \
"$XILINX_VIVADO/data/ip/xpm/xpm_VCOMP.vhd" \

vlog -work xlconstant_v1_1_9  -incr -v2k5 "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/e2d2/hdl/xlconstant_v1_1_vl_rfs.v" \

vlog -work xil_defaultlib  -incr -v2k5 "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../bd/cl_axi_sc_1x1/ip/cl_axi_sc_1x1_smartconnect_0_0/bd_0/ip/ip_0/sim/bd_6722_one_0.v" \

vcom -work lib_cdc_v1_0_3 -93  -incr \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/2a4f/hdl/lib_cdc_v1_0_rfs.vhd" \

vcom -work proc_sys_reset_v5_0_15 -93  -incr \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/3a26/hdl/proc_sys_reset_v5_0_vh_rfs.vhd" \

vcom -work xil_defaultlib -93  -incr \
"../../../bd/cl_axi_sc_1x1/ip/cl_axi_sc_1x1_smartconnect_0_0/bd_0/ip/ip_1/sim/bd_6722_psr0_0.vhd" \
"../../../bd/cl_axi_sc_1x1/ip/cl_axi_sc_1x1_smartconnect_0_0/bd_0/ip/ip_2/sim/bd_6722_psr_aclk_0.vhd" \
"../../../bd/cl_axi_sc_1x1/ip/cl_axi_sc_1x1_smartconnect_0_0/bd_0/ip/ip_3/sim/bd_6722_psr_aclk1_0.vhd" \

vlog -work smartconnect_v1_0  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/sc_util_v1_0_vl_rfs.sv" \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/98d8/hdl/sc_mmu_v1_0_vl_rfs.sv" \

vlog -work xil_defaultlib  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../bd/cl_axi_sc_1x1/ip/cl_axi_sc_1x1_smartconnect_0_0/bd_0/ip/ip_4/sim/bd_6722_s00mmu_0.sv" \

vlog -work smartconnect_v1_0  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/2da8/hdl/sc_transaction_regulator_v1_0_vl_rfs.sv" \

vlog -work xil_defaultlib  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../bd/cl_axi_sc_1x1/ip/cl_axi_sc_1x1_smartconnect_0_0/bd_0/ip/ip_5/sim/bd_6722_s00tr_0.sv" \

vlog -work smartconnect_v1_0  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/a950/hdl/sc_si_converter_v1_0_vl_rfs.sv" \

vlog -work xil_defaultlib  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../bd/cl_axi_sc_1x1/ip/cl_axi_sc_1x1_smartconnect_0_0/bd_0/ip/ip_6/sim/bd_6722_s00sic_0.sv" \

vlog -work smartconnect_v1_0  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/cef3/hdl/sc_axi2sc_v1_0_vl_rfs.sv" \

vlog -work xil_defaultlib  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../bd/cl_axi_sc_1x1/ip/cl_axi_sc_1x1_smartconnect_0_0/bd_0/ip/ip_7/sim/bd_6722_s00a2s_0.sv" \

vlog -work smartconnect_v1_0  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/sc_node_v1_0_vl_rfs.sv" \

vlog -work xil_defaultlib  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../bd/cl_axi_sc_1x1/ip/cl_axi_sc_1x1_smartconnect_0_0/bd_0/ip/ip_8/sim/bd_6722_sarn_0.sv" \
"../../../bd/cl_axi_sc_1x1/ip/cl_axi_sc_1x1_smartconnect_0_0/bd_0/ip/ip_9/sim/bd_6722_srn_0.sv" \
"../../../bd/cl_axi_sc_1x1/ip/cl_axi_sc_1x1_smartconnect_0_0/bd_0/ip/ip_10/sim/bd_6722_sawn_0.sv" \
"../../../bd/cl_axi_sc_1x1/ip/cl_axi_sc_1x1_smartconnect_0_0/bd_0/ip/ip_11/sim/bd_6722_swn_0.sv" \
"../../../bd/cl_axi_sc_1x1/ip/cl_axi_sc_1x1_smartconnect_0_0/bd_0/ip/ip_12/sim/bd_6722_sbn_0.sv" \

vlog -work smartconnect_v1_0  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/7f4f/hdl/sc_sc2axi_v1_0_vl_rfs.sv" \

vlog -work xil_defaultlib  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../bd/cl_axi_sc_1x1/ip/cl_axi_sc_1x1_smartconnect_0_0/bd_0/ip/ip_13/sim/bd_6722_m00s2a_0.sv" \

vlog -work smartconnect_v1_0  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/1f04/hdl/sc_exit_v1_0_vl_rfs.sv" \

vlog -work xil_defaultlib  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../bd/cl_axi_sc_1x1/ip/cl_axi_sc_1x1_smartconnect_0_0/bd_0/ip/ip_14/sim/bd_6722_m00e_0.sv" \

vlog -work xil_defaultlib  -incr -v2k5 "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../bd/cl_axi_sc_1x1/ip/cl_axi_sc_1x1_smartconnect_0_0/bd_0/sim/bd_6722.v" \

vlog -work smartconnect_v1_0  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/3718/hdl/sc_switchboard_v1_0_vl_rfs.sv" \

vlog -work axi_infrastructure_v1_1_0  -incr -v2k5 "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl/axi_infrastructure_v1_1_vl_rfs.v" \

vlog -work axi_register_slice_v2_1_31  -incr -v2k5 "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/92b2/hdl/axi_register_slice_v2_1_vl_rfs.v" \

vlog -work axi_vip_v1_1_17  -incr -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/4d04/hdl/axi_vip_v1_1_vl_rfs.sv" \

vlog -work xil_defaultlib  -incr -v2k5 "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/f0b6/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/c783/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/bd/cl_axi_sc_1x1/ipshared/ec67/hdl" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xlconstant_v1_1_9 -l xil_defaultlib -l lib_cdc_v1_0_3 -l proc_sys_reset_v5_0_15 -l smartconnect_v1_0 -l axi_infrastructure_v1_1_0 -l axi_register_slice_v2_1_31 -l axi_vip_v1_1_17 \
"../../../bd/cl_axi_sc_1x1/ip/cl_axi_sc_1x1_smartconnect_0_0/sim/cl_axi_sc_1x1_smartconnect_0_0.v" \
"../../../bd/cl_axi_sc_1x1/sim/cl_axi_sc_1x1.v" \

vlog -work xil_defaultlib \
"glbl.v"

