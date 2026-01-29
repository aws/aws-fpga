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

SLOT_NUM := 0
APP_SCRIPTS_DIR := $(SDK_DIR)/apps/virtual-ethernet/scripts
SDK_USERSPACE_DIR := $(SDK_DIR)/userspace
SDE_EXAMPLE_DIR := ../src
SDE_SRC_DIR := $(SDE_EXAMPLE_DIR)/sde_lib
SDE_LIB_DIR := $(SDE_SRC_DIR)/lib
SDE_LIB_SO_DIR := $(SDE_LIB_DIR)/so
APP_INSTALL_DIR := $(HDK_DIR)/cl/examples/cl_sde/software/runtime/veth_app
DPDK_DIR := $(APP_INSTALL_DIR)/dpdk
RM := sudo rm -rf
STATS_PERIOD := 0

INCLUDES := -I$(SDE_SRC_DIR) -I$(SDK_USERSPACE_DIR)/include -I$(SDK_USERSPACE_DIR)/fpga_libs/fpga_mgmt
LDFLAGS := -L$(SDE_LIB_SO_DIR) -L$(SDK_USERSPACE_DIR)/lib/so
LDLIBS := -lsde -lfpga_mgmt

# Global offsets are available if your design has an offset register set compared to the original CL_SDE example.
GLOBAL_SDE_OFFSET := -DGLOBAL_SDE_OFFSET=0x0
GLOBAL_ATG_OFFSET := -DGLOBAL_ATG_OFFSET=0x0

OPT := -DFPGA_ALLOW_NON_ROOT -DCONFIG_LOGLEVEL=1 $(GLOBAL_SDE_OFFSET) $(GLOBAL_ATG_OFFSET)
LIB_CFLAGS := $(OPT) -g -Wall -Werror -W -Wno-parentheses -Wstrict-prototypes -Wmissing-prototypes $(INCLUDES) -fvisibility=hidden -mavx2 -MMD -MP
EXAMPLE_CFLAGS := $(OPT) -g -Wall -Werror -W -Wno-parentheses -Wstrict-prototypes -Wmissing-prototypes $(INCLUDES)
SRCS := $(wildcard $(SDE_SRC_DIR)/*.c)
SDE_EXAMPLES := sde_c2h_perf_test sde_h2c_perf_test sde_c2h_simple sde_h2c_simple sde_loopback_simple sde_c2h_user_buffers sde_loopback_perf_test
SDE_VERSION := 1.0.0
SDELIB_SO := $(SDE_LIB_SO_DIR)/libsde.so.$(SDE_VERSION)
OBJS := $(SRCS:.c=.o)
DEPS := $(OBJS:.o=.d)


.PHONY: all clean install_sde_lib check_env help ve_install ve_run

all: check_env ve_install sde_examples ve_run

help:
	@echo "Available targets:"
	@echo "  all              - Build everything"
	@echo "  ve_install       - Build the DPDK virtual ethernet application and configure hardware"
	@echo "  ve_run           - Run the dpdk-testpmd application"
	@echo "  clean            - Remove built files"
	@echo "  sde_examples     - Build SDE examples"
	@echo "  help             - Display this help message"

ve_install: check_env
	$(APP_SCRIPTS_DIR)/virtual_ethernet_install.py $(APP_INSTALL_DIR)
	sudo $(APP_SCRIPTS_DIR)/virtual_ethernet_setup.py $(DPDK_DIR) $(SLOT_NUM)

ve_run: check_env ve_install sde_examples
	sudo $(DPDK_DIR)/build/app/dpdk-testpmd -l 0-1  -- --port-topology=loop --auto-start --tx-first --stats-period=$(STATS_PERIOD) \

sde_examples: $(SDE_EXAMPLES)

clean:
	$(RM) $(APP_INSTALL_DIR) $(SDE_EXAMPLES) $(SDELIB_SO) $(OBJS) $(DEPS)

check_env:
ifndef SDK_DIR
    $(error SDK_DIR is undefined. Try "source sdk_setup.sh" to set the software environment)
endif
ifndef HDK_DIR
    $(error HDK_DIR is undefined. Try "source hdk_setup.sh" to set the software environment)
endif

install_sde_lib: $(SDELIB_SO)
	sudo ./install_lib.sh

$(SDELIB_SO): $(OBJS)
	mkdir -p $(SDE_LIB_SO_DIR)
	$(CC) -o $(SDELIB_SO) $(LIBCFLAGS) -shared $(OBJS) -Wl,-soname,libsde.so.1

$(SDE_SRC_DIR)/%.o: $(SDE_SRC_DIR)/%.c
	$(CC) $(LIB_CFLAGS) -c $< -o $@

%:: $(SDE_EXAMPLE_DIR)/%.c install_sde_lib check_env
	$(CC) -o $@ $< $(LDFLAGS) $(LDLIBS) $(EXAMPLE_CFLAGS)

-include $(DEPS)
