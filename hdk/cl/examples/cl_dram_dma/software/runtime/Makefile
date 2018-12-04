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

INCLUDES = -I$(SDK_DIR)/userspace/include

CC = gcc
CFLAGS = -DCONFIG_LOGLEVEL=4 -std=gnu11 -g -Wall -Werror $(INCLUDES)

LDLIBS = -lfpga_mgmt

SRC = test_dram_dma_common.c test_dram_dma_retention.c test_dram_dma.c test_dram_dma_hwsw_cosim.c
OBJ = $(SRC:.c=.o)


all: test_dram_dma check_env retention cosim $(BIN)

test_dram_dma: $(OBJ)
	$(CC) $(CFLAGS) -o test_dram_dma test_dram_dma.o test_dram_dma_common.o  $(LDFLAGS) $(LDLIBS)

retention: $(OBJ)
	$(CC) $(CFLAGS) -o test_dram_dma_retention test_dram_dma_retention.o test_dram_dma_common.o $(LDFLAGS) $(LDLIBS)

cosim: $(OBJ)
	$(CC) $(CFLAGS) -o test_dram_dma_hwsw_cosim test_dram_dma_hwsw_cosim.o test_dram_dma_common.o $(LDFLAGS) $(LDLIBS)

clean:
	rm -f *.o test_dram_dma_retention test_dram_dma test_dram_dma_hwsw_cosim

check_env:
ifndef SDK_DIR
    $(error SDK_DIR is undefined. Try "source sdk_setup.sh" to set the software environment)
endif
