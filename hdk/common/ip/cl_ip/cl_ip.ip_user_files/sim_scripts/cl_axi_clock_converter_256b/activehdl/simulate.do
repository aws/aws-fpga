transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

asim +access +r +m+cl_axi_clock_converter_256b  -L xilinx_vip -L xpm -L axi_infrastructure_v1_1_0 -L fifo_generator_v13_2_10 -L axi_clock_converter_v2_1_30 -L xil_defaultlib -L xilinx_vip -L unisims_ver -L unimacro_ver -L secureip -O2 xil_defaultlib.cl_axi_clock_converter_256b xil_defaultlib.glbl

do {cl_axi_clock_converter_256b.udo}

run

endsim

quit -force
