## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## =============================================================================

INCLUDES = -I$(SDK_DIR)/userspace/include

CC = gcc
CFLAGS = -DCONFIG_LOGLEVEL=4 -std=gnu99 -g -Wall -Werror $(INCLUDES)

LDLIBS = -lfpga_mgmt -lrt -lpthread

SRC = test_dram_dma.c
OBJ = $(SRC:.c=.o)
BIN = test_dram_dma

all: $(BIN) check_env

$(BIN): $(OBJ)
        $(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS) $(LDLIBS)

clean:
        rm -f *.o $(BIN)

check_env:
ifndef SDK_DIR
    $(error SDK_DIR is undefined. Try "source sdk_setup.sh" to set the software environment)
endif
