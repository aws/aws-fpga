onbreak {quit -f}
onerror {quit -f}

vsim  -lib xil_defaultlib cl_c2c_xbar_128G_opt

set NumericStdNoWarnings 1
set StdArithNoWarnings 1

do {wave.do}

view wave
view structure
view signals

do {cl_c2c_xbar_128G.udo}

run 1000ns

quit -force
