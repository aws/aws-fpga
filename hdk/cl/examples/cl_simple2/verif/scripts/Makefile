
all:	compile run

compile:
	xvlog --sv -m64 --relax -f tb.vivado.f
	xelab -m64 --timescale 1ps/1ps --debug typical --relax --mt 8 -L xil_defaultlib -L unisims_ver -L unimacro_ver -L secureip -snapshot tb work.tb work.glbl work.test_peek_poke

run:
	xsim -R -log test.log -tclbatch waves.tcl -g tb

clean:
	rm -rf .Xil
	rm -rf xsim.dir
	rm -rf *.log
	rm -rf *.jou
	rm -rf *.pb
	rm -rf *.dat
	rm -rf *.wdb
