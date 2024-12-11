transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

vlib work
vlib activehdl/xilinx_vip
vlib activehdl/xpm
vlib activehdl/xil_defaultlib

vmap xilinx_vip activehdl/xilinx_vip
vmap xpm activehdl/xpm
vmap xil_defaultlib activehdl/xil_defaultlib

vlog -work xilinx_vip  -sv2k12 "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xil_defaultlib \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_axi4streampc.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_axi4pc.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/xil_common_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_pkg.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi4stream_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/axi_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/clk_vip_if.sv" \
"$XILINX_VIVADO/data/xilinx_vip/hdl/rst_vip_if.sv" \

vlog -work xpm  -sv2k12 "+incdir+../../../ipstatic" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xil_defaultlib \
"$XILINX_VIVADO/data/ip/xpm/xpm_fifo/hdl/xpm_fifo.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_cdc/hdl/xpm_cdc.sv" \

vcom -work xpm -  \
"$XILINX_VIVADO/data/ip/xpm/xpm_VCOMP.vhd" \

vlog -work xil_defaultlib  -v2k5 "+incdir+../../../ipstatic" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xil_defaultlib \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_b/clk_mmcm_b_mmcm_pll_drp.v" \

vcom -work xil_defaultlib -  \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_b/proc_common_v3_00_a/hdl/src/vhdl/clk_mmcm_b_conv_funs_pkg.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_b/proc_common_v3_00_a/hdl/src/vhdl/clk_mmcm_b_proc_common_pkg.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_b/proc_common_v3_00_a/hdl/src/vhdl/clk_mmcm_b_ipif_pkg.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_b/proc_common_v3_00_a/hdl/src/vhdl/clk_mmcm_b_family_support.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_b/proc_common_v3_00_a/hdl/src/vhdl/clk_mmcm_b_family.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_b/proc_common_v3_00_a/hdl/src/vhdl/clk_mmcm_b_soft_reset.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_b/proc_common_v3_00_a/hdl/src/vhdl/clk_mmcm_b_pselect_f.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_b/axi_lite_ipif_v1_01_a/hdl/src/vhdl/clk_mmcm_b_address_decoder.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_b/axi_lite_ipif_v1_01_a/hdl/src/vhdl/clk_mmcm_b_slave_attachment.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_b/axi_lite_ipif_v1_01_a/hdl/src/vhdl/clk_mmcm_b_axi_lite_ipif.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_b/clk_mmcm_b_clk_wiz_drp.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_b/clk_mmcm_b_axi_clk_config.vhd" \

vlog -work xil_defaultlib  -v2k5 "+incdir+../../../ipstatic" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" -l xilinx_vip -l xpm -l xil_defaultlib \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_b/clk_mmcm_b_clk_wiz.v" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_b/clk_mmcm_b.v" \

vlog -work xil_defaultlib \
"glbl.v"

