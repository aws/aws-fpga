onbreak {quit -f}
onerror {quit -f}

vsim  -lib xil_defaultlib cl_axi_sc_2x2_opt

set NumericStdNoWarnings 1
set StdArithNoWarnings 1

do {wave.do}

view wave
view structure
view signals

do {cl_axi_sc_2x2.udo}

run 1000ns

quit -force
