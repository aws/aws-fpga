transcript off
onbreak {quit -force}
onerror {quit -force}
transcript on

asim +access +r +m+cl_ddr4  -L xilinx_vip -L xpm -L microblaze_v11_0_13 -L xil_defaultlib -L lib_cdc_v1_0_3 -L proc_sys_reset_v5_0_15 -L lmb_v10_v3_0_14 -L lmb_bram_if_cntlr_v4_0_24 -L blk_mem_gen_v8_4_8 -L iomodule_v3_1_10 -L xilinx_vip -L unisims_ver -L unimacro_ver -L secureip -O5 xil_defaultlib.cl_ddr4 xil_defaultlib.glbl

do {cl_ddr4.udo}

run 1000ns

endsim

quit -force
