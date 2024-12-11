transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

asim +access +r +m+dest_register_slice  -L xilinx_vip -L xpm -L axi_infrastructure_v1_1_0 -L axi_register_slice_v2_1_31 -L xil_defaultlib -L xilinx_vip -L unisims_ver -L unimacro_ver -L secureip -O2 xil_defaultlib.dest_register_slice xil_defaultlib.glbl

do {dest_register_slice.udo}

run

endsim

quit -force
