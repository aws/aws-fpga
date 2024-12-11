transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

asim +access +r +m+ila_c2c  -L xilinx_vip -L xpm -L xil_defaultlib -L xilinx_vip -L unisims_ver -L unimacro_ver -L secureip -O5 xil_defaultlib.ila_c2c xil_defaultlib.glbl

do {ila_c2c.udo}

run 1000ns

endsim

quit -force
