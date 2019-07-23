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

export TEST ?= test_sde_loopback

SLOT_NUM = 0
APP_SCRIPTS_DIR = $(SDK_DIR)/apps/virtual-ethernet/scripts
APP_INSTALL_DIR = veth_app
DPDK_DIR = $(APP_INSTALL_DIR)/dpdk
RMDIR = sudo rm -rf
STATS_PERIOD = 0

.PHONY: all clean

all: check_env install run

install: check_env
	sudo $(APP_SCRIPTS_DIR)/virtual_ethernet_install.py $(APP_INSTALL_DIR)
	sudo $(APP_SCRIPTS_DIR)/virtual_ethernet_setup.py $(DPDK_DIR) $(SLOT_NUM)

run: check_env
	sudo $(DPDK_DIR)/x86_64-native-linuxapp-gcc/app/testpmd -l 0-1  -- --port-topology=loop --auto-start --tx-first --stats-period=$(STATS_PERIOD) & \

clean:
	$(RMDIR) $(APP_INSTALL_DIR)

check_env:
ifndef SDK_DIR
    $(error SDK_DIR is undefined. Try "source sdk_setup.sh" to set the software environment)
endif

