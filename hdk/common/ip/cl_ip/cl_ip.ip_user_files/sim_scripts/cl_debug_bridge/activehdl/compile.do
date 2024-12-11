transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

vlib work
vlib activehdl/xilinx_vip
vlib activehdl/xpm
vlib activehdl/xsdbm_v3_0_2
vlib activehdl/xil_defaultlib
vlib activehdl/lut_buffer_v2_0_1

vmap xilinx_vip activehdl/xilinx_vip
vmap xpm activehdl/xpm
vmap xsdbm_v3_0_2 activehdl/xsdbm_v3_0_2
vmap xil_defaultlib activehdl/xil_defaultlib
vmap lut_buffer_v2_0_1 activehdl/lut_buffer_v2_0_1

vlog -work xilinx_vip  -sv2k12 "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xsdbm_v3_0_2 -l xil_defaultlib -l lut_buffer_v2_0_1 \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_axi4streampc.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_axi4pc.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/xil_common_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/clk_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/rst_vip_if.sv" \

vlog -work xpm  -sv2k12 "+incdir+../../../ipstatic/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xsdbm_v3_0_2 -l xil_defaultlib -l lut_buffer_v2_0_1 \
"$XILINX_VIVADO/data/ip/xpm/xpm_fifo/hdl/xpm_fifo.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_cdc/hdl/xpm_cdc.sv" \

vcom -work xpm -  \
"$XILINX_VIVADO/data/ip/xpm/xpm_VCOMP.vhd" \

vlog -work xsdbm_v3_0_2  -v2k5 "+incdir+../../../ipstatic/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xsdbm_v3_0_2 -l xil_defaultlib -l lut_buffer_v2_0_1 \
"../../../ipstatic/hdl/xsdbm_v3_0_vl_rfs.v" \

vlog -work xil_defaultlib  -v2k5 "+incdir+../../../ipstatic/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xsdbm_v3_0_2 -l xil_defaultlib -l lut_buffer_v2_0_1 \
"../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/sim/bd_a493_xsdbm_0.v" \

vlog -work lut_buffer_v2_0_1  -v2k5 "+incdir+../../../ipstatic/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xsdbm_v3_0_2 -l xil_defaultlib -l lut_buffer_v2_0_1 \
"../../../ipstatic/hdl/lut_buffer_v2_0_vl_rfs.v" \

vlog -work xil_defaultlib  -v2k5 "+incdir+../../../ipstatic/hdl/verilog" "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_0/hdl/verilog" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xsdbm_v3_0_2 -l xil_defaultlib -l lut_buffer_v2_0_1 \
"../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/ip/ip_1/sim/bd_a493_lut_buffer_0.v" \
"../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/bd_0/sim/bd_a493.v" \
"../../../../cl_ip.gen/sources_1/ip/cl_debug_bridge/sim/cl_debug_bridge.v" \

vlog -work xil_defaultlib \
"glbl.v"

