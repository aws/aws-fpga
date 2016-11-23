export CL_ROOT = $(PWD)/../..
export SIM_DIR = $(CL_ROOT)/verif/sim
export SCRIPTS_DIR = $(PWD)
export XILINX_IP = $(HDK_DIR)/top/vu9p/design/v3_venom_cl/v3_venom_cl.srcs/sources_1/ip
export SH_LIB_DIR = $(HDK_COMMON_DIR)/shell_latest/design/lib

all:	compile run

ifeq ($(QUESTA), 1)
  export SIMULATOR = questa
  export COMPLIB_DIR = $(CL_ROOT)/verif/questa_complib
  include Makefile.questa
else
  export SIMULATOR = vivado
  include Makefile.vivado
endif


include $(HDK_COMMON_DIR)/verif/tb/scripts/Makefile.$(SIMULATOR).inc
