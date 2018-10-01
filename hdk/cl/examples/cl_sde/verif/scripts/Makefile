# Amazon FPGA Hardware Development Kit
#
# Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Amazon Software License (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#    http://aws.amazon.com/asl/
#
# or in the "license" file accompanying this file. This file is distributed on
# an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.
#
## 
## export TEST ?= test_null
## export C_TEST ?= test_null
## 
## export CL_ROOT = $(PWD)/../..
## 
## export C_INC_DIR  = $(CL_ROOT)/software/verif_rtl/include
## export C_SRC_DIR  = $(CL_ROOT)/software/verif_rtl/src
## 
## export TEST_NAME =  $(CL_ROOT)/verif/tests/$(TEST).sv
## export C_TEST_NAME = $(C_SRC_DIR)/$(C_TEST).c
## 
## export SIM_ROOT = $(CL_ROOT)/verif/sim
## 
## ifeq ($(C_TEST),test_null)
##   export SIM_DIR = $(SIM_ROOT)/$(TEST)
## else
##   export SIM_DIR = $(SIM_ROOT)/$(C_TEST)
## endif
## 
## 
## export SCRIPTS_DIR = $(PWD)
## export XILINX_IP   = $(HDK_SHELL_DESIGN_DIR)/ip
## export SH_LIB_DIR  = $(HDK_SHELL_DESIGN_DIR)/lib
## export SH_INF_DIR  = $(HDK_SHELL_DESIGN_DIR)/interfaces
## export SH_SH_DIR   = $(HDK_SHELL_DESIGN_DIR)/sh_ddr/sim
## 
## SV_TEST_LIST = test_hello_world
## C_TEST_LIST  = test_hello_world.c
## 
## all:	make_sim_dir compile run
## 
## include $(HDK_COMMON_DIR)/verif/tb/scripts/Makefile.common.inc

export MAKE_DEBUG = 0

export VCS = 1
export TEST ?= test_null
export C_TEST ?= test_null

export CL_ROOT = $(PWD)/../..

export C_INC_DIR  = $(CL_ROOT)/software/include
export C_SRC_DIR  = $(CL_ROOT)/software/src

export TEST_NAME =  $(CL_ROOT)/verif/tests/$(TEST).sv
export C_TEST_NAME = $(C_SRC_DIR)/$(C_TEST).c

export DEFAULT_DEFINES = +define+SH_BFM_TB
#+define+NO_SDE_DEBUG_ILA

REGRESS ?= 0
TYPE ?= smoke

export PLUSARGS ?= +$(TEST)
export REGRESS_PLUSARGS ?= +$(TEST)

export TEST_DIR ?= $(TEST)
export LOG_NAME ?= $(TEST).log
export VCS_COMPLIB_DIR ?= $(PWD)/../sim/vcs_complib

ifeq ($(REGRESS), 1)
  export SIM_ROOT ?= $(CL_ROOT)/verif/sim/regress/$(TYPE)
  export RESULTS_FILE = results_$(TYPE).log
  override REGRESS_PLUSARGS += +NO_WAVES +define+NO_SDE_DEBUG_ILA
else
  export SIM_ROOT ?= $(CL_ROOT)/verif/sim
endif

ifeq ($(C_TEST),test_null)
  export SIM_DIR ?= $(SIM_ROOT)/$(TEST_DIR)
else
  export SIM_DIR ?= $(SIM_ROOT)/$(C_TEST)
endif

export SCRIPTS_DIR = $(PWD)
export XILINX_IP   = $(HDK_SHELL_DESIGN_DIR)/ip
export SH_LIB_DIR  = $(HDK_SHELL_DESIGN_DIR)/lib
export SH_INF_DIR  = $(HDK_SHELL_DESIGN_DIR)/interfaces

SV_TEST_LIST = test_dram_dma
C_TEST_LIST  = test_peek_poke.c

all:	make_sim_dir compile run check

include $(HDK_COMMON_DIR)/verif/tb/scripts/Makefile.common.inc

