transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

asim +access +r +m+cl_axi3_256b_reg_slice  -L xilinx_vip -L xpm -L axi_infrastructure_v1_1_0 -L axi_register_slice_v2_1_31 -L xil_defaultlib -L xilinx_vip -L unisims_ver -L unimacro_ver -L secureip -O2 xil_defaultlib.cl_axi3_256b_reg_slice xil_defaultlib.glbl

do {cl_axi3_256b_reg_slice.udo}

run

endsim

quit -force
