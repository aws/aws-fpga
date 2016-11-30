## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## =============================================================================

export TEST ?= test_null
export C_TEST ?= test_null

export TEST_NAME =  $(CL_ROOT)/verif/tests/$(TEST).sv
export C_TEST_NAME = $(CL_ROOT)/software/src/$(C_TEST).sv

export CL_ROOT = $(PWD)/../..


ifeq ($(C_TEST),test_null)
  export SIM_DIR = $(CL_ROOT)/verif/sim/$(TEST)
else
  export SIM_DIR = $(CL_ROOT)/verif/sim/$(C_TEST)
endif


export SCRIPTS_DIR = $(PWD)
export XILINX_IP = $(HDK_DIR)/top/vu9p/design/v3_venom_cl/v3_venom_cl.srcs/sources_1/ip
export SH_LIB_DIR = $(HDK_COMMON_DIR)/shell_latest/design/lib
export SH_INF_DIR = $(HDK_COMMON_DIR)/shell_latest/design/interfaces

export C_INC_DIR  = $(CL_ROOT)/software/include
export C_SRC_DIR  = $(CL_ROOT)/software/src

all:	compile run

ifeq ($(QUESTA), 1)
  export SIMULATOR = questa
  export COMPLIB_DIR = $(CL_ROOT)/verif/sim/questa_complib
  include Makefile.questa
else
  export SIMULATOR = vivado
  include Makefile.vivado
endif

include $(HDK_COMMON_DIR)/verif/tb/scripts/Makefile.$(SIMULATOR).inc
