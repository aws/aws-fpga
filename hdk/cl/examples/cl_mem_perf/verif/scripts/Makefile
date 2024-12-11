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

ifndef HDK_COMMON_DIR
  $(error Environment variable HDK_COMMON_DIR not set. Please source hdk_setup.sh)
endif

include $(HDK_COMMON_DIR)/verif/tb/scripts/Makefile.header.inc

### Files required to do C cosimulation
C_FILES = $(C_TEST_NAME) $(C_COMMON_SRC_DIR)/fpga_pci_sv.c $(C_INC_DIR)/test_dram_dma_common.c $(C_COMMON_SRC_DIR)/sh_dpi_tasks.c
C_INCLUDE_DIRS = $(C_SDK_USR_INC_DIR) $(C_SDK_USR_UTILS_DIR) $(C_COMMON_DIR)/include $(C_COMMON_DIR)/src $(C_INC_DIR) $(C_HEADER_INCLUDE_DIR)

### DEFAULT: Lists each test target under Makefile.tests
REGRESSION_TEST_LIST = ${DEFAULT_REGRESSION_TEST_LIST_COLLECTION}
### ALTERNATIVE: Space-delimitted list of test targets
### 	REGRESSION_TEST_LIST = test_ddr test_ddr_peek_poke

### 'regression' sub-targets can be found in $(HDK_COMMON_DIR)/verif/tb/scripts/Makefile.common.inc
regression: run_regression log_regression_results print_regression_results

include $(HDK_COMMON_DIR)/verif/tb/scripts/Makefile.common.inc
