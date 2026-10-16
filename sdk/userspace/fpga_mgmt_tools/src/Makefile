#
# Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License"). You may
# not use this file except in compliance with the License. A copy of the
# License is located at
#
#     http://aws.amazon.com/apache2.0/
#
# or in the "license" file accompanying this file. This file is distributed
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
# express or implied. See the License for the specific language governing
# permissions and limitations under the License.
#

TOP = ../..
include $(TOP)/common.mk

INCLUDES = -I$(FPGAHALINC_PATH) -I$(TOPINC_PATH) -I../. -I.

# Keep shared and static library paths separate.
LDFLAGS_SHARED = $(LDFLAGS) -L$(LIB_SO_PATH)
LDLIBS = -lfpga_mgmt

# flags for compiling a statically linked version
LDFLAGS_STATIC = $(LDFLAGS) -L$(LIB_PATH)
LDLIBS_STATIC = -lfpga_mgmt -lrt -lpthread

VTAG_XVC_SRC = virtual_jtag_pcie.c virtual_jtag_server.c

SRC = fpga_local_cmd.c fpga_local_cmd_parse.c $(VTAG_XVC_SRC)
OBJ = $(SRC:.c=.o)
BIN = fpga-local-cmd
BIN_STATIC = static-fpga-local-cmd

all: $(BIN) $(BIN_STATIC)

$(BIN): $(OBJ)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS_SHARED) $(LDLIBS)

$(BIN_STATIC): $(OBJ)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS_STATIC) $(LDLIBS_STATIC)

clean:
	rm -f *.o *.d *.a $(BIN) $(BIN_STATIC)

-include $(DEPS)
