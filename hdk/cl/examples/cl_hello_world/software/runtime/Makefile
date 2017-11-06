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

VPATH = src:include:$(HDK_DIR)/common/software/src:$(HDK_DIR)/common/software/include

INCLUDES = -I$(SDK_DIR)/userspace/include
INCLUDES += -I $(HDK_DIR)/common/software/include
INCLUDES += -I ./include

CC = gcc
CFLAGS = -DCONFIG_LOGLEVEL=4 -g -Wall $(INCLUDES)

LDLIBS = -lfpga_mgmt -lrt -lpthread

SRC = ${SDK_DIR}/userspace/utils/sh_dpi_tasks.c test_hello_world.c
OBJ = $(SRC:.c=.o)
BIN = test_hello_world

all: $(BIN) check_env

$(BIN): $(OBJ)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS) $(LDLIBS)

clean:
	rm -f *.o $(BIN)

check_env:
ifndef SDK_DIR
    $(error SDK_DIR is undefined. Try "source sdk_setup.sh" to set the software environment)
endif
