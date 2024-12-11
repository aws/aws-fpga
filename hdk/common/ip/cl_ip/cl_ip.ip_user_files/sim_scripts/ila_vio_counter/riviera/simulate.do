transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

asim +access +r +m+ila_vio_counter  -L xilinx_vip -L xpm -L xil_defaultlib -L xilinx_vip -L unisims_ver -L unimacro_ver -L secureip -O5 xil_defaultlib.ila_vio_counter xil_defaultlib.glbl

do {ila_vio_counter.udo}

run 1000ns

endsim

quit -force
