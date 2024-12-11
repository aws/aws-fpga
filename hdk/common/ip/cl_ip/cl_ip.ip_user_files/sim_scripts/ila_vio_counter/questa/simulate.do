onbreak {quit -f}
onerror {quit -f}

vsim  -lib xil_defaultlib ila_vio_counter_opt

set NumericStdNoWarnings 1
set StdArithNoWarnings 1

do {wave.do}

view wave
view structure
view signals

do {ila_vio_counter.udo}

run 1000ns

quit -force
