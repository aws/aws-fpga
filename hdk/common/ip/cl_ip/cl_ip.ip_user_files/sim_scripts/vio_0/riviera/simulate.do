transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

asim +access +r +m+vio_0  -L xilinx_vip -L xpm -L xil_defaultlib -L xilinx_vip -L unisims_ver -L unimacro_ver -L secureip -O5 xil_defaultlib.vio_0 xil_defaultlib.glbl

do {vio_0.udo}

run 1000ns

endsim

quit -force
