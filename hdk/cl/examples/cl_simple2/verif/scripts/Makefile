export SIMULATOR = vivado
export CL_ROOT = $(PWD)/../..
export SIM_DIR = $(CL_ROOT)/verif/sim
export SCRIPTS_DIR = $(PWD)
export XILINX_IP = $(HDK_DIR)/top/vu9p/design/v3_venom_cl/v3_venom_cl.srcs/sources_1/ip
export SH_LIB_DIR = $(HDK_COMMON_DIR)/shell_latest/design/lib

all:	compile run

include $(HDK_COMMON_DIR)/verif/tb/scripts/Makefile.$(SIMULATOR).inc

compile:
	mkdir -p $(SIM_DIR)
	cd $(SIM_DIR) && xvlog --sv -m64 --relax -f $(SCRIPTS_DIR)/top.vivado.f
	cd $(SIM_DIR) && xelab -m64 --timescale 1ps/1ps --debug typical --relax --mt 8 -L xil_defaultlib -L unisims_ver -L unimacro_ver -L secureip -snapshot tb work.tb work.glbl work.test_peek_poke

run:
	cd $(SIM_DIR) && xsim -R -log test.log -tclbatch $(SCRIPTS_DIR)/waves.tcl tb

