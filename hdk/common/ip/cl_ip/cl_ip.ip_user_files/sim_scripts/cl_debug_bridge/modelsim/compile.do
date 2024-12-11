vlib modelsim_lib/work
vlib modelsim_lib/msim

vlib modelsim_lib/msim/xilinx_vip
vlib modelsim_lib/msim/xpm
vlib modelsim_lib/msim/xsdbm_v3_0_2
vlib modelsim_lib/msim/xil_defaultlib
vlib modelsim_lib/msim/lut_buffer_v2_0_1

vmap xilinx_vip modelsim_lib/msim/xilinx_vip
vmap xpm modelsim_lib/msim/xpm
vmap xsdbm_v3_0_2 modelsim_lib/msim/xsdbm_v3_0_2
vmap xil_defaultlib modelsim_lib/msim/xil_defaultlib
vmap lut_buffer_v2_0_1 modelsim_lib/msim/lut_buffer_v2_0_1

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

vlog -work xpm -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../ipstatic/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"$XILINX_VIVADO/data/ip/xpm/xpm_fifo/hdl/xpm_fifo.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_cdc/hdl/xpm_cdc.sv" \

vcom -work xpm -64 -93  \
"$XILINX_VIVADO/data/ip/xpm/xpm_VCOMP.vhd" \

vlog -work xsdbm_v3_0_2 -64 -incr -mfcu  "+incdir+../../../ipstatic/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../ipstatic/hdl/xsdbm_v3_0_vl_rfs.v" \

vlog -work xil_defaultlib -64 -incr -mfcu  "+incdir+../../../ipstatic/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/sim/bd_a493_xsdbm_0.v" \

vlog -work lut_buffer_v2_0_1 -64 -incr -mfcu  "+incdir+../../../ipstatic/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../ipstatic/hdl/lut_buffer_v2_0_vl_rfs.v" \

vlog -work xil_defaultlib -64 -incr -mfcu  "+incdir+../../../ipstatic/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_1/sim/bd_a493_lut_buffer_0.v" \
"../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/sim/bd_a493.v" \
"../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/sim/cl_debug_bridge.v" \

vlog -work xil_defaultlib \
"glbl.v"

