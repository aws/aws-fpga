transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

asim +access +r +m+cl_hbm  -L xilinx_vip -L xpm -L xil_defaultlib -L hbm_v1_0_16 -L xilinx_vip -L unisims_ver -L unimacro_ver -L secureip -O5 xil_defaultlib.cl_hbm xil_defaultlib.glbl

do {cl_hbm.udo}

run 1000ns

endsim

quit -force
