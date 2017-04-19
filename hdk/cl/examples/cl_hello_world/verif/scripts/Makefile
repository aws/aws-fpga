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


export TEST ?= test_null
export C_TEST ?= test_null

export CL_ROOT = $(PWD)/../..

export C_INC_DIR  = $(CL_ROOT)/software/verif_rtl/include
export C_SRC_DIR  = $(CL_ROOT)/software/verif_rtl/src

export TEST_NAME =  $(CL_ROOT)/verif/tests/$(TEST).sv
export C_TEST_NAME = $(C_SRC_DIR)/$(C_TEST).c

export SIM_ROOT = $(CL_ROOT)/verif/sim

ifeq ($(C_TEST),test_null)
  export SIM_DIR = $(SIM_ROOT)/$(TEST)
else
  export SIM_DIR = $(SIM_ROOT)/$(C_TEST)
endif


export SCRIPTS_DIR = $(PWD)
export XILINX_IP   = $(HDK_SHELL_DESIGN_DIR)/ip
export SH_LIB_DIR  = $(HDK_SHELL_DESIGN_DIR)/lib
export SH_INF_DIR  = $(HDK_SHELL_DESIGN_DIR)/interfaces
export SH_SH_DIR   = $(HDK_SHELL_DESIGN_DIR)/sh_ddr/sim

SV_TEST_LIST = test_hello_world
C_TEST_LIST  = test_hello_world.c

all:	make_sim_dir compile run

include $(HDK_COMMON_DIR)/verif/tb/scripts/Makefile.common.inc

