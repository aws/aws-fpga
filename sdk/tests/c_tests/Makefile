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

FPGAMGMTLIB_TESTS_SO = fpga_mgmt_lib_tests.so

INCLUDES = -I$(SDK_DIR)/userspace/include

CC = gcc
CFLAGS = -DCONFIG_LOGLEVEL=4 -shared -fPIC -std=gnu99 -g -Wall -Werror $(INCLUDES)

LDLIBS = -lfpga_mgmt -lpthread -L.

SRC = $(wildcard *.c) 
OBJ = $(SRC:.c=.o)

all: check_env $(FPGAMGMTLIB_TESTS_SO)

$(FPGAMGMTLIB_TESTS_SO): $(OBJ)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS) $(LDLIBS)

clean:
	rm -f *.o $(FPGAMGMTLIB_TESTS_SO)

check_env:
ifndef SDK_DIR
    $(error SDK_DIR is undefined. Try "source sdk_setup.sh" to set the software environment)
endif
