## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## =============================================================================

#VPATH = src:include:$(HDK_DIR)/common/software/src:$(HDK_DIR)/common/software/include

INCLUDES = -I$(SDK_DIR)/include

CC = gcc
CFLAGS = -DCONFIG_LOGLEVEL=4 -g -Wall $(INCLUDES)

LDFLAGS = -L$(SDK_DIR)/lib
LDLIBS = -lfpga_pci -lfpga_mgmt -lfpga_hal_reg -lfpga_hal_plat -lfpga_hal_mbox -lutils -lrt -lpthread

SRC = test_hello_world.c
OBJ = $(SRC:.c=.o)
BIN = test_hello_world

all: $(BIN)

$(BIN): $(OBJ)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS) $(LDLIBS)

clean:
	rm -f *.o $(BIN)
