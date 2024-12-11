transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

vlib work
vlib activehdl/xilinx_vip
vlib activehdl/xpm
vlib activehdl/xil_defaultlib
vlib activehdl/hbm_v1_0_16

vmap xilinx_vip activehdl/xilinx_vip
vmap xpm activehdl/xpm
vmap xil_defaultlib activehdl/xil_defaultlib
vmap hbm_v1_0_16 activehdl/hbm_v1_0_16

vlog -work xilinx_vip  -sv2k12 "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xil_defaultlib -l hbm_v1_0_16 \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_axi4streampc.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_axi4pc.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/xil_common_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/clk_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/rst_vip_if.sv" \

vlog -work xpm  -sv2k12 "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_hbm/hdl/rtl" "+incdir+../../../ipstatic/verif/model" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xil_defaultlib -l hbm_v1_0_16 \
"$XILINX_VIVADO/data/ip/xpm/xpm_fifo/hdl/xpm_fifo.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_cdc/hdl/xpm_cdc.sv" \

vcom -work xpm -  \
"$XILINX_VIVADO/data/ip/xpm/xpm_VCOMP.vhd" \

vlog -work xil_defaultlib  -sv2k12 "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_hbm/hdl/rtl" "+incdir+../../../ipstatic/verif/model" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xil_defaultlib -l hbm_v1_0_16 \
"../../../../cl_ip.gen/sources_1/ip/cl_hbm/hdl/rtl/hbm_v1_0_16.sv" \

vlog -work hbm_v1_0_16  -sv2k12 "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_hbm/hdl/rtl" "+incdir+../../../ipstatic/verif/model" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xil_defaultlib -l hbm_v1_0_16 \
"../../../ipstatic/hdl/hbm_v1_0_vl_rfs.sv" \

vlog -work xil_defaultlib  -sv2k12 "+incdir+../../../../cl_ip.gen/sources_1/ip/cl_hbm/hdl/rtl" "+incdir+../../../ipstatic/verif/model" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xil_defaultlib -l hbm_v1_0_16 \
"../../../../cl_ip.gen/sources_1/ip/cl_hbm/verif/model/hbm_model.sv" \
"../../../../cl_ip.gen/sources_1/ip/cl_hbm/sim/cl_hbm.sv" \

vlog -work xil_defaultlib \
"glbl.v"

