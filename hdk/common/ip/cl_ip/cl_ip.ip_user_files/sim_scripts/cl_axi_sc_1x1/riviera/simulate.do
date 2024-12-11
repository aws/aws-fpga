transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

asim +access +r +m+cl_axi_sc_1x1  -L xilinx_vip -L xpm -L xlconstant_v1_1_9 -L xil_defaultlib -L lib_cdc_v1_0_3 -L proc_sys_reset_v5_0_15 -L smartconnect_v1_0 -L axi_infrastructure_v1_1_0 -L axi_register_slice_v2_1_31 -L axi_vip_v1_1_17 -L xilinx_vip -L unisims_ver -L unimacro_ver -L secureip -O5 xil_defaultlib.cl_axi_sc_1x1 xil_defaultlib.glbl

do {cl_axi_sc_1x1.udo}

run 1000ns

endsim

quit -force
