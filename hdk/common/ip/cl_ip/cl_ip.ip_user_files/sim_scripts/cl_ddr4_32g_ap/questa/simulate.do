onbreak {quit -f}
onerror {quit -f}

vsim  -lib xil_defaultlib cl_ddr4_32g_ap_opt

set NumericStdNoWarnings 1
set StdArithNoWarnings 1

do {wave.do}

view wave
view structure
view signals

do {cl_ddr4_32g_ap.udo}

run 1000ns

quit -force
