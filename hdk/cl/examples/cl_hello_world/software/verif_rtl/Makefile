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

C_SRCS := test_hello_world.c pcie_utils.c cl_utils.c main.c
C_OBJS := $(C_SRCS:.c=.o)

CC = gcc
CFLAGS = -I ./include
CFLAGS += -I $(HDK_DIR)/common/software/include
all: test_hello_world

test_hello_world: $(C_SRCS)
	$(CC) $(CFLAGS) -o $@ $^

clean:
	rm test_hello_world
