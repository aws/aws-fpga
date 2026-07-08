# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

SDK_USERSPACE_DIR := $(SDK_DIR)/userspace

CL_SRC_DIR := ../src
SW_INC_DIR := ../include

INCLUDES := -I$(SW_INC_DIR) -I$(SDK_USERSPACE_DIR)/include
LDFLAGS := -L$(SDK_USERSPACE_DIR)/lib/so -L$(SDK_USERSPACE_DIR)/lib
LDLIBS := -lfpga_mgmt -lfpga_clkgen

CC = gcc
CFLAGS = -DCONFIG_LOGLEVEL=4 -std=gnu11 -g -Wall -Werror $(INCLUDES)

# Utility library sources
UTIL_SRCS := $(CL_SRC_DIR)/cl_clk_gen_utils.c
UTIL_OBJS := $(UTIL_SRCS:.c=.o)

EXAMPLES := test_clk_adder

.PHONY: all clean check_env help

all: check_env $(EXAMPLES)

help:
	@echo "Available targets:"
	@echo "  all              - Build everything"
	@echo "  clean            - Remove built files"
	@echo "  help             - Display this help message"

clean:
	$(RM) $(EXAMPLES) $(UTIL_OBJS)

check_env:
ifndef SDK_DIR
    $(error SDK_DIR is undefined. Try "source sdk_setup.sh" to set the software environment)
endif

# Build utility library objects
$(CL_SRC_DIR)/%.o: $(CL_SRC_DIR)/%.c
	$(CC) $(CFLAGS) -c $< -o $@

# Build test executables with utility library
%: $(CL_SRC_DIR)/%.c $(UTIL_OBJS) check_env
	$(CC) -o $@ $< $(UTIL_OBJS) $(CFLAGS) $(LDFLAGS) $(LDLIBS)
