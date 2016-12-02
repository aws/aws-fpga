## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## =============================================================================

export TEST ?= test_null
export C_TEST ?= test_null

export CL_ROOT = $(PWD)/../..

export TEST_NAME =  $(CL_ROOT)/verif/tests/$(TEST).sv
export C_TEST_NAME = $(CL_ROOT)/software/src/$(C_TEST).sv

export SIM_ROOT = $(CL_ROOT)/verif/sim

ifeq ($(C_TEST),test_null)
  export SIM_DIR = $(SIM_ROOT)/$(TEST)
else
  export SIM_DIR = $(SIM_ROOT)/$(C_TEST)
endif


export SCRIPTS_DIR = $(PWD)
export XILINX_IP = $(HDK_COMMON_DIR)/shell_latest/design/ip
export SH_LIB_DIR = $(HDK_COMMON_DIR)/shell_latest/design/lib
export SH_INF_DIR = $(HDK_COMMON_DIR)/shell_latest/design/interfaces

export C_INC_DIR  = $(CL_ROOT)/software/include
export C_SRC_DIR  = $(CL_ROOT)/software/src

SV_TEST_LIST = test_hello_world
C_TEST_LIST  = test_hello_world.c

all:	compile run

include $(HDK_COMMON_DIR)/verif/tb/scripts/Makefile.common.inc

