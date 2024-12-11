onbreak {quit -f}
onerror {quit -f}

vsim  -lib xil_defaultlib cl_axi3_256b_reg_slice_opt

set NumericStdNoWarnings 1
set StdArithNoWarnings 1

do {wave.do}

view wave
view structure
view signals

do {cl_axi3_256b_reg_slice.udo}

run 1000ns

quit -force
