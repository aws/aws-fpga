ifndef VIVADO_TOOL_VERSION
  $(error Environment variable VIVADO_TOOL_VERSION not set. Please source hdk_setup.sh)
else
  $(info VIVADO_TOOL_VERSION = $(VIVADO_TOOL_VERSION))
endif

ifndef CL_DIR
  $(error Environment variable CL_DIR not set. Please set CL_DIR to `$AWS_FPGA_REPO_DIR/hdk/cl/examples/<EXAMPLE NAME>`)
else
  $(info CL_DIR = $(CL_DIR))
  ifneq (1,$(CL_DIR_FORCE))
    ifneq (,$(findstring $(CL_DIR),$(PWD)))
      $(info Running from $(PWD))
    else
      $(error CL_DIR cannot be found in PWD=$(PWD). Set `CL_DIR_FORCE=1` to override)
    endif
  else
    $(info Forcing the use of $(CL_DIR) from $(PWD))
  endif
endif

include Makefile.tests
export TEST ?= test_null
export C_TEST ?= test_null

# TODO: Come back to this
export SCRIPTS_DIR = $(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
export SDK_DIR = $(AWS_FPGA_REPO_DIR)/sdk

export C_COMMON_DIR        = $(HDK_COMMON_DIR)/software
export C_COMMON_SRC_DIR    = $(C_COMMON_DIR)/src
export C_SDK_USR_INC_DIR   = $(SDK_DIR)/userspace/include
export C_SDK_USR_UTILS_DIR = $(SDK_DIR)/userspace/utils
export C_INC_DIR           = $(CL_DIR)/software/runtime
export C_SRC_DIR           = $(CL_DIR)/software/src
export C_HEADER_INCLUDE_DIR       = $(CL_DIR)/software/include

export TEST_NAME =  $(CL_DIR)/verif/tests/$(TEST).sv

ifeq ($(C_TEST),test_null)
  export C_TEST_NAME = $(HDK_COMMON_DIR)/software/src/$(C_TEST).c
else
  export C_TEST_NAME = $(C_SRC_DIR)/$(C_TEST).c
endif

export SIM_ROOT = $(CL_DIR)/verif/sim/$(SIMULATOR)
