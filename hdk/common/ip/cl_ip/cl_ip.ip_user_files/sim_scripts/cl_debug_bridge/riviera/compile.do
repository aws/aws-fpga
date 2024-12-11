transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

vlib work
vlib riviera/xilinx_vip
vlib riviera/xpm
vlib riviera/xsdbm_v3_0_2
vlib riviera/xil_defaultlib
vlib riviera/lut_buffer_v2_0_1

vmap xilinx_vip riviera/xilinx_vip
vmap xpm riviera/xpm
vmap xsdbm_v3_0_2 riviera/xsdbm_v3_0_2
vmap xil_defaultlib riviera/xil_defaultlib
vmap lut_buffer_v2_0_1 riviera/lut_buffer_v2_0_1

vlog -work xilinx_vip  -incr -l axi_vip_v1_1_17 -l smartconnect_v1_0 -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xsdbm_v3_0_2 -l xil_defaultlib -l lut_buffer_v2_0_1 \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_axi4streampc.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_axi4pc.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/xil_common_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/clk_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/rst_vip_if.sv" \

vlog -work xpm  -incr -l axi_vip_v1_1_17 -l smartconnect_v1_0 -l hbm_v1_0_16 -l xdma_v4_1_29 -l xilinx_vip "+incdir+../../../ipstatic/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xsdbm_v3_0_2 -l xil_defaultlib -l lut_buffer_v2_0_1 \
"$XILINX_VIVADO/data/ip/xpm/xpm_fifo/hdl/xpm_fifo.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_cdc/hdl/xpm_cdc.sv" \

vcom -work xpm -93  -incr \
"$XILINX_VIVADO/data/ip/xpm/xpm_VCOMP.vhd" \

vlog -work xsdbm_v3_0_2  -incr -v2k5 "+incdir+../../../ipstatic/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xsdbm_v3_0_2 -l xil_defaultlib -l lut_buffer_v2_0_1 \
"../../../ipstatic/hdl/xsdbm_v3_0_vl_rfs.v" \

vlog -work xil_defaultlib  -incr -v2k5 "+incdir+../../../ipstatic/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xsdbm_v3_0_2 -l xil_defaultlib -l lut_buffer_v2_0_1 \
"../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/sim/bd_a493_xsdbm_0.v" \

vlog -work lut_buffer_v2_0_1  -incr -v2k5 "+incdir+../../../ipstatic/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xsdbm_v3_0_2 -l xil_defaultlib -l lut_buffer_v2_0_1 \
"../../../ipstatic/hdl/lut_buffer_v2_0_vl_rfs.v" \

vlog -work xil_defaultlib  -incr -v2k5 "+incdir+../../../ipstatic/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xsdbm_v3_0_2 -l xil_defaultlib -l lut_buffer_v2_0_1 \
"../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_1/sim/bd_a493_lut_buffer_0.v" \
"../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/sim/bd_a493.v" \
"../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/sim/cl_debug_bridge.v" \

vlog -work xil_defaultlib \
"glbl.v"

