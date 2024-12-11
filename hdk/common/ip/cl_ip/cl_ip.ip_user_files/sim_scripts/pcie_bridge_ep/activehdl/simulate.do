transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

asim +access +r +m+pcie_bridge_ep  -L xilinx_vip -L xpm -L gtwizard_ultrascale_v1_7_18 -L xil_defaultlib -L blk_mem_gen_v8_4_8 -L xdma_v4_1_29 -L xilinx_vip -L unisims_ver -L unimacro_ver -L secureip -O2 xil_defaultlib.pcie_bridge_ep xil_defaultlib.glbl

do {pcie_bridge_ep.udo}

run

endsim

quit -force
