transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

asim +access +r +m+clk_mmcm_a  -L xilinx_vip -L xpm -L xil_defaultlib -L xilinx_vip -L unisims_ver -L unimacro_ver -L secureip -O2 xil_defaultlib.clk_mmcm_a xil_defaultlib.glbl

do {clk_mmcm_a.udo}

run

endsim

quit -force
