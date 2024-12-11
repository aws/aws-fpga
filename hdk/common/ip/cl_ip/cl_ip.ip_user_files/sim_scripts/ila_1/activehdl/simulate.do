transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

asim +access +r +m+ila_1  -L xilinx_vip -L xpm -L xil_defaultlib -L xilinx_vip -L unisims_ver -L unimacro_ver -L secureip -O2 xil_defaultlib.ila_1 xil_defaultlib.glbl

do {ila_1.udo}

run

endsim

quit -force
