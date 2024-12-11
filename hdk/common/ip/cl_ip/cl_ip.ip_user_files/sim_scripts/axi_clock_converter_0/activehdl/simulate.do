transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

asim +access +r +m+axi_clock_converter_0  -L xilinx_vip -L xpm -L axi_infrastructure_v1_1_0 -L fifo_generator_v13_2_10 -L axi_clock_converter_v2_1_30 -L xil_defaultlib -L xilinx_vip -L unisims_ver -L unimacro_ver -L secureip -O2 xil_defaultlib.axi_clock_converter_0 xil_defaultlib.glbl

do {axi_clock_converter_0.udo}

run

endsim

quit -force
