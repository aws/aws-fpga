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

ifndef VIVADO_TOOL_VERSION
$(error Environment variable VIVADO_TOOL_VERSION not set. please source hdk_setup.sh)
else
$(info VIVADO_TOOL_VERSION = $(VIVADO_TOOL_VERSION))
endif

export TEST ?= test_null
export C_TEST ?= test_null

export CL_ROOT = $(PWD)/../..
export SDK_DIR = $(AWS_FPGA_REPO_DIR)/sdk

export C_COMMON_DIR        = $(HDK_COMMON_DIR)/software
export C_SDK_USR_INC_DIR   = $(SDK_DIR)/userspace/include
export C_SDK_USR_UTILS_DIR = $(SDK_DIR)/userspace/utils
export C_INC_DIR  = $(CL_ROOT)/software/runtime
export C_SRC_DIR  = $(CL_ROOT)/software/runtime

export TEST_NAME =  $(CL_ROOT)/verif/tests/$(TEST).sv

ifeq ($(C_TEST),test_null)
  export C_TEST_NAME = $(HDK_COMMON_DIR)/software/src/$(C_TEST).c
else
  export C_TEST_NAME = $(C_SRC_DIR)/$(C_TEST).c
endif

export SIM_ROOT = $(CL_ROOT)/verif/sim/$(SIMULATOR)

ifeq ($(C_TEST),test_null)
  ifeq ($(AXI_MEMORY_MODEL), 1)
    ifeq ($(ECC_DIRECT), 1)
        export SIM_DIR = $(SIM_ROOT)/$(TEST)_sv_fast_ecc_direct
    else 
      ifeq ($(ECC_RAND), 1)
        export SIM_DIR = $(SIM_ROOT)/$(TEST)_sv_fast_ecc_rnd
      else
        ifeq ($(DDR_BKDR), 1)
         export SIM_DIR = $(SIM_ROOT)/$(TEST)_sv_fast_bkdr
	else 
         export SIM_DIR = $(SIM_ROOT)/$(TEST)_sv_fast
	endif 
      endif
    endif
  else
   ifeq ($(ECC_DIRECT), 1)
        export SIM_DIR = $(SIM_ROOT)/$(TEST)_sv_ecc_direct
    else 
      ifeq ($(ECC_RAND), 1)
        export SIM_DIR = $(SIM_ROOT)/$(TEST)_sv_ecc_rnd
      else
        ifeq ($(DDR_BKDR), 1)
         export SIM_DIR = $(SIM_ROOT)/$(TEST)_sv_bkdr
	else 
         export SIM_DIR = $(SIM_ROOT)/$(TEST)_sv
	endif 
      endif
    endif
  endif
else
  export SIM_DIR = $(SIM_ROOT)/$(C_TEST)_c
endif

export SCRIPTS_DIR = $(PWD)
export XILINX_IP   = $(HDK_SHELL_DESIGN_DIR)/ip
export SH_LIB_DIR  = $(HDK_SHELL_DESIGN_DIR)/lib
export SH_INF_DIR  = $(HDK_SHELL_DESIGN_DIR)/interfaces
export SH_SH_DIR   = $(HDK_SHELL_DESIGN_DIR)/sh_ddr/sim

SV_TEST_LIST = test_hello_world
C_FILES      = $(C_TEST_NAME) $(C_SDK_USR_UTILS_DIR)/sh_dpi_tasks.c $(C_COMMON_DIR)/src/fpga_pci_sv.c $(C_SRC_DIR)/test_dram_dma_common.c

ifeq ($(XCHK), 1)
  all:	make_sim_dir compile_chk run
else
  all:	make_sim_dir compile run
endif

include $(HDK_COMMON_DIR)/verif/tb/scripts/Makefile.common.inc

