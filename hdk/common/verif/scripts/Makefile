#-------------------------------------------------------------------------------
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
#-------------------------------------------------------------------------------

DONE_FILE := $(HDK_COMMON_DIR)/verif/scripts/.done
DEPS_FILE := $(HDK_SHELL_DESIGN_DIR)/ip/ddr4_core/ddr4_core.xci
DEPS_FILE += $(HDK_COMMON_DIR)/verif/scripts/init.tcl
DEPS_FILE += $(HDK_COMMON_DIR)/verif/scripts/init.sh

CLEAN_TARGETS += $(HDK_COMMON_DIR)/verif/scripts/ddr4_core_ip_report.txt
CLEAN_TARGETS += $(HDK_COMMON_DIR)/verif/scripts/tmp/
CLEAN_TARGETS += $(wildcard $(HDK_COMMON_DIR)/verif/scripts/vivado*.jou)
CLEAN_TARGETS += $(wildcard $(HDK_COMMON_DIR)/verif/scripts/vivado*.log)

all: $(DONE_FILE)

$(DONE_FILE): $(DEPS_FILE)
	@ echo "INFO: Building in $(shell dirname $@)"
	@ echo "INFO: This could take 5-10 minutes, please be patient!"
	@ rm -rf $(CLEAN_TARGETS)
	@ cd $(shell dirname $@)\
	&& ./init.sh $(MODEL_DIR)\
	&& echo "INFO: DDR4 model build passed."\
	|| (echo "ERROR: DDR4 model build failed." && exit 2)
	@ touch $@

