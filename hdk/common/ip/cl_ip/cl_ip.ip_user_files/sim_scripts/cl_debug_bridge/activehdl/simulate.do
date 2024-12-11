transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

asim +access +r +m+cl_debug_bridge  -L xilinx_vip -L xpm -L xsdbm_v3_0_2 -L xil_defaultlib -L lut_buffer_v2_0_1 -L xilinx_vip -L unisims_ver -L unimacro_ver -L secureip -O2 xil_defaultlib.cl_debug_bridge xil_defaultlib.glbl

do {cl_debug_bridge.udo}

run

endsim

quit -force
