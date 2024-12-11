transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

asim +access +r +m+axi_register_slice_light  -L xilinx_vip -L xpm -L axi_infrastructure_v1_1_0 -L axi_register_slice_v2_1_31 -L xil_defaultlib -L xilinx_vip -L unisims_ver -L unimacro_ver -L secureip -O5 xil_defaultlib.axi_register_slice_light xil_defaultlib.glbl

do {axi_register_slice_light.udo}

run 1000ns

endsim

quit -force
