## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## =============================================================================

#VPATH = src:include:$(HDK_DIR)/common/software/src:$(HDK_DIR)/common/software/include

TOP = ../../../../../..
SDK = $(TOP)/sdk/userspace
INCLUDES = -I$(SDK)/include

CC = gcc
CFLAGS = -g -Wall $(INCLUDES)

LDFLAGS = -L$(SDK)/utils -L$(SDK)/hal/lib -L$(SDK)/fpga_libs/fpga_pci/lib -L$(SDK)/fpga_libs/fpga_mgmt/lib
LDLIBS = -lutils -lfpga_pci -lfpga_mgmt -lfpga_hal_reg -lfpga_hal_plat -lrt -lpthread

SRC = test_hello_world.c
OBJ = $(SRC:.c=.o)
BIN = test_hello_world

all: $(BIN)

$(BIN): $(OBJ)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS) $(LDLIBS)

clean:
	rm -f *.o $(BIN)
