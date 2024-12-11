transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

asim +access +r +m+cl_hbm_mmcm  -L xilinx_vip -L xpm -L xil_defaultlib -L xilinx_vip -L unisims_ver -L unimacro_ver -L secureip -O2 xil_defaultlib.cl_hbm_mmcm xil_defaultlib.glbl

do {cl_hbm_mmcm.udo}

run

endsim

quit -force
