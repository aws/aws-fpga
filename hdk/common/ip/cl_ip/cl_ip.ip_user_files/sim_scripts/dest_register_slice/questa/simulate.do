onbreak {quit -f}
onerror {quit -f}

vsim  -lib xil_defaultlib dest_register_slice_opt

set NumericStdNoWarnings 1
set StdArithNoWarnings 1

do {wave.do}

view wave
view structure
view signals

do {dest_register_slice.udo}

run 1000ns

quit -force
