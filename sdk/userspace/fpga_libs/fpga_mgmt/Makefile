#
# Copyright 2015-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
UTILLIB_PATH = $(TOP)/util
LIB_PATH = $(TOP)/lib
LIB_SO_PATH = $(LIB_PATH)/so

INCLUDES = -I. -I$(TOPINC_PATH) -I/usr/include

#OPT=-O2
CFLAGS=$(OPT) -g -std=gnu99 -fPIC -Wall -Werror -W -Wno-parentheses -Wstrict-prototypes -Wmissing-prototypes $(INCLUDES)

SRC = $(wildcard *.c)
OBJ = $(SRC:.c=.o)
FPGAMGMTLIB_SO = $(LIB_SO_PATH)/libfpga_mgmt.so.1.0.0
FPGAMGMTLIB = $(LIB_PATH)/libfpga_mgmt.a

LDLIBS = -lrt -lpthread

FPGAAUXLIBS = $(LIB_PATH)/libfpga_pci.a
FPGAAUXLIBS += $(LIB_PATH)/libutils.a

all: $(FPGAMGMTLIB) $(FPGAMGMTLIB_SO)

$(FPGAMGMTLIB): $(OBJ)
	mkdir -p $(LIB_PATH)
	for library in $(FPGAAUXLIBS); do ar -x $$library; done
	ar rcs $(FPGAMGMTLIB) *.o

$(FPGAMGMTLIB_SO): $(OBJ)
	mkdir -p $(LIB_SO_PATH)
	$(CC) -o $(FPGAMGMTLIB_SO) -shared $(OBJ) -Wl,-soname,libfpga_mgmt.so.1 -Wl,--whole-archive $(FPGAAUXLIBS) -Wl,--no-whole-archive $(LDLIBS)
	ln -sf libfpga_mgmt.so.1.0.0 $(LIB_SO_PATH)/libfpga_mgmt.so

clean:
	rm -f *.o $(FPGAMGMTLIB) $(FPGAMGMTLIB_SO)
