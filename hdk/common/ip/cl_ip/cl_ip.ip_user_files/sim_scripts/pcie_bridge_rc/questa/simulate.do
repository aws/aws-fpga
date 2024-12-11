onbreak {quit -f}
onerror {quit -f}

vsim  -lib xil_defaultlib pcie_bridge_rc_opt

set NumericStdNoWarnings 1
set StdArithNoWarnings 1

do {wave.do}

view wave
view structure
view signals

do {pcie_bridge_rc.udo}

run 1000ns

quit -force
