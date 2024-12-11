vlib questa_lib/work
vlib questa_lib/msim

vlib questa_lib/msim/xilinx_vip
vlib questa_lib/msim/xpm
vlib questa_lib/msim/xil_defaultlib

vmap xilinx_vip questa_lib/msim/xilinx_vip
vmap xpm questa_lib/msim/xpm
vmap xil_defaultlib questa_lib/msim/xil_defaultlib

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

vlog -work xpm -64 -incr -mfcu  -sv -L axi_vip_v1_1_17 -L smartconnect_v1_0 -L hbm_v1_0_16 -L xdma_v4_1_29 -L xilinx_vip "+incdir+../../../ipstatic" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"$XILINX_VIVADO/data/ip/xpm/xpm_fifo/hdl/xpm_fifo.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_memory/hdl/xpm_memory.sv" \
"$XILINX_VIVADO/data/ip/xpm/xpm_cdc/hdl/xpm_cdc.sv" \

vcom -work xpm -64 -93  \
"$XILINX_VIVADO/data/ip/xpm/xpm_VCOMP.vhd" \

vlog -work xil_defaultlib -64 -incr -mfcu  "+incdir+../../../ipstatic" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_hbm/clk_mmcm_hbm_mmcm_pll_drp.v" \

vcom -work xil_defaultlib -64 -93  \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_hbm/proc_common_v3_00_a/hdl/src/vhdl/clk_mmcm_hbm_conv_funs_pkg.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_hbm/proc_common_v3_00_a/hdl/src/vhdl/clk_mmcm_hbm_proc_common_pkg.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_hbm/proc_common_v3_00_a/hdl/src/vhdl/clk_mmcm_hbm_ipif_pkg.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_hbm/proc_common_v3_00_a/hdl/src/vhdl/clk_mmcm_hbm_family_support.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_hbm/proc_common_v3_00_a/hdl/src/vhdl/clk_mmcm_hbm_family.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_hbm/proc_common_v3_00_a/hdl/src/vhdl/clk_mmcm_hbm_soft_reset.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_hbm/proc_common_v3_00_a/hdl/src/vhdl/clk_mmcm_hbm_pselect_f.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_hbm/axi_lite_ipif_v1_01_a/hdl/src/vhdl/clk_mmcm_hbm_address_decoder.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_hbm/axi_lite_ipif_v1_01_a/hdl/src/vhdl/clk_mmcm_hbm_slave_attachment.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_hbm/axi_lite_ipif_v1_01_a/hdl/src/vhdl/clk_mmcm_hbm_axi_lite_ipif.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_hbm/clk_mmcm_hbm_clk_wiz_drp.vhd" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_hbm/clk_mmcm_hbm_axi_clk_config.vhd" \

vlog -work xil_defaultlib -64 -incr -mfcu  "+incdir+../../../ipstatic" "+incdir+$XILINX_VIVADO/data/xilinx_vip/include" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_hbm/clk_mmcm_hbm_clk_wiz.v" \
"../../../../cl_ip.gen/sources_1/ip/clk_mmcm_hbm/clk_mmcm_hbm.v" \

vlog -work xil_defaultlib \
"glbl.v"

