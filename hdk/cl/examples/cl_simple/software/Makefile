## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## =============================================================================

VPATH = src:include:$(HDK_DIR)/common/software/src:$(HDK_DIR)/common/software/include

C_SRCS := test_peek_poke.c pcie_utils.c cl_utils.c main.c
C_OBJS := $(C_SRCS:.c=.o)

CC = gcc
CFLAGS = -I ./include
CFLAGS += -I $(HDK_DIR)/common/software/include
all: test_peek_poke

test_peek_poke: $(C_SRCS)
	$(CC) $(CFLAGS) -o $@ $^

clean:
	rm test_peek_poke
