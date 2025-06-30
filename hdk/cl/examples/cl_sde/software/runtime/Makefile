# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
# =============================================================================

export TEST ?= test_sde_loopback

SLOT_NUM = 0
APP_SCRIPTS_DIR = $(SDK_DIR)/apps/virtual-ethernet/scripts
SDK_USERSPACE_DIR = $(SDK_DIR)/userspace
SDE_EXAMPLE_DIR = ../src
SDE_LIB_DIR = $(SDE_EXAMPLE_DIR)/sde_lib
APP_INSTALL_DIR = $(HDK_DIR)/cl/examples/cl_sde/software/runtime/veth_app
DPDK_DIR = $(APP_INSTALL_DIR)/dpdk
RMDIR = sudo rm -rf
STATS_PERIOD = 0

INCLUDES=-I$(SDE_LIB_DIR) -I$(SDK_USERSPACE_DIR)/include -I$(SDK_USERSPACE_DIR)/fpga_libs/fpga_mgmt
LDFLAGS = -L$(SDK_USERSPACE_DIR)/lib/so
LDLIBS = -lfpga_mgmt
# Global offsets are available if your design has an offset register set compared to the original CL_SDE example.
GLOBAL_SDE_OFFSET=-DGLOBAL_SDE_OFFSET=0x0
GLOBAL_ATG_OFFSET=-DGLOBAL_ATG_OFFSET=0x0
OPT=-DFPGA_ALLOW_NON_ROOT -DCONFIG_LOGLEVEL=1 $(GLOBAL_SDE_OFFSET) $(GLOBAL_ATG_OFFSET)
CFLAGS=$(OPT) -g -Wall -Werror -W -Wno-parentheses -Wstrict-prototypes -Wmissing-prototypes $(INCLUDES)
SRC=$(SDE_LIB_DIR)/sde_hw_ctrl.c $(SDE_LIB_DIR)/sde_dma_buffer.c $(SDE_LIB_DIR)/sde_mgmt.c $(SDE_LIB_DIR)/sde_utility.c $(SDE_LIB_DIR)/sde_mem.c
SDE_EXAMPLES = sde_c2h_perf_test sde_h2c_perf_test sde_c2h_simple sde_h2c_simple sde_loopback_simple sde_c2h_user_buffers

.PHONY: all clean

all: check_env ve_install sde_examples ve_run

ve_install: check_env
	$(APP_SCRIPTS_DIR)/virtual_ethernet_install.py $(APP_INSTALL_DIR)
	sudo $(APP_SCRIPTS_DIR)/virtual_ethernet_setup.py $(DPDK_DIR) $(SLOT_NUM)

ve_run: check_env ve_install sde_examples
	sudo $(DPDK_DIR)/build/app/dpdk-testpmd -l 0-1  -- --port-topology=loop --auto-start --tx-first --stats-period=$(STATS_PERIOD) \

sde_examples: $(SDE_EXAMPLES)

clean:
	$(RMDIR) $(APP_INSTALL_DIR) $(SDE_EXAMPLES)

check_env:
ifndef SDK_DIR
    $(error SDK_DIR is undefined. Try "source sdk_setup.sh" to set the software environment)
endif
ifndef HDK_DIR
    $(error HDK_DIR is undefined. Try "source hdk_setup.sh" to set the software environment)
endif

sde_c2h_perf_test: $(SDE_EXAMPLE_DIR)/sde_c2h_perf_test.c $(SRC) check_env
	gcc $< $(SRC) -o $@ -mavx2 $(LDFLAGS) $(LDLIBS) $(CFLAGS)

sde_h2c_perf_test: $(SDE_EXAMPLE_DIR)/sde_h2c_perf_test.c $(SRC) check_env
	gcc $< $(SRC) -o $@ -mavx2 $(LDFLAGS) $(LDLIBS) $(CFLAGS)

sde_c2h_simple: $(SDE_EXAMPLE_DIR)/sde_c2h_simple.c $(SRC) check_env
	gcc $< $(SRC) -o $@ -mavx2 $(LDFLAGS) $(LDLIBS) $(CFLAGS)

sde_h2c_simple: $(SDE_EXAMPLE_DIR)/sde_h2c_simple.c $(SRC) check_env
	gcc $< $(SRC) -o $@ -mavx2 $(LDFLAGS) $(LDLIBS) $(CFLAGS)

sde_loopback_simple: $(SDE_EXAMPLE_DIR)/sde_loopback_simple.c $(SRC) check_env
	gcc $< $(SRC) -o $@ -mavx2 $(LDFLAGS) $(LDLIBS) $(CFLAGS)

sde_c2h_user_buffers: $(SDE_EXAMPLE_DIR)/sde_c2h_user_buffers.c $(SRC) check_env
	gcc $< $(SRC) -o $@ -mavx2 $(LDFLAGS) $(LDLIBS) $(CFLAGS)
