onbreak {quit -f}
onerror {quit -f}

vsim  -lib xil_defaultlib axi_register_slice_light_opt

set NumericStdNoWarnings 1
set StdArithNoWarnings 1

do {wave.do}

view wave
view structure
view signals

do {axi_register_slice_light.udo}

run 1000ns

quit -force
