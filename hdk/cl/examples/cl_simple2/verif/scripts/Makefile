export SIMULATOR = vivado
#export CL_ROOT = $(PWD)/../..
export SIM_DIR = $(CL_DIR)/verif/sim
export SCRIPTS_DIR = $(PWD)

include $(HDK_COMMON_DIR)/verif/tb/scripts/Makefile.$(SIMULATOR).inc

all:	compile run

compile:
	mkdir -p $(SIM_DIR)
	cd $(SIM_DIR) && xvlog --sv -m64 --relax -f $(SCRIPTS_DIR)/top.vivado.f
	cd $(SIM_DIR) && xelab -m64 --timescale 1ps/1ps --debug typical --relax --mt 8 -L xil_defaultlib -L unisims_ver -L unimacro_ver -L secureip -snapshot tb work.tb work.glbl work.test_peek_poke

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
