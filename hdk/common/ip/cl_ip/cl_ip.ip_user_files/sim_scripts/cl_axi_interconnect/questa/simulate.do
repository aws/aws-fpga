onbreak {quit -f}
onerror {quit -f}

vsim  -lib xil_defaultlib cl_axi_interconnect_opt

set NumericStdNoWarnings 1
set StdArithNoWarnings 1

do {wave.do}

view wave
view structure
view signals

do {cl_axi_interconnect.udo}

run 1000ns

quit -force
