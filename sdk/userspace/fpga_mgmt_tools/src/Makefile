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
TOPINC_PATH = $(TOP)/include
FPGAHALINC_PATH = $(TOPINC_PATH)/hal
LIB_PATH = $(TOP)/lib

INCLUDES = -I$(FPGAHALINC_PATH) -I$(TOP)/include -I../. -I.

#OPT=-O2
CFLAGS=$(OPT) -g  -Wall -Werror -W -Wno-parentheses -Wstrict-prototypes -Wmissing-prototypes $(INCLUDES)

LDFLAGS = -L$(LIB_PATH)/so
LDLIBS = -lfpga_mgmt

# flags for compiling a staticly linked version
LDFLAGS_STATIC = -L$(LIB_PATH)
LDLIBS_STATIC = -lfpga_mgmt -lrt -lpthread

UTILLCDLIB = $(LIB_PATH)/libutils.a
LIBS=$(UTILLCDLIB)
VTAG_XVC_SRC = virtual_jtag_pcie.c virtual_jtag_server.c

SRC = fpga_local_cmd.c fpga_local_cmd_parse.c $(VTAG_XVC_SRC)
OBJ = $(SRC:.c=.o)
BIN = fpga-local-cmd
BIN_STATIC = static-fpga-local-cmd

all: $(BIN) $(BIN_STATIC)

$(BIN): $(OBJ)
	$(CC) -o $@ $^ $(LDFLAGS) $(LDLIBS) 

$(BIN_STATIC): $(OBJ)
	$(CC) -o $@ $^ $(LDFLAGS_STATIC) $(LDLIBS_STATIC)

clean:
	rm -f *.o *.a $(BIN) $(BIN_STATIC)
